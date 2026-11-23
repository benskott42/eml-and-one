import Decimal from "decimal.js";
import type { C } from "./complex";
import { cutTraceActive, noteExactGate, onNegativeCutZ } from "./cut";
import {
  EmlError,
  EmlLimitError,
  EXACT_TIMED_OUT,
  SINGULAR_INDET,
  SINGULAR_LN0,
  SINGULAR_NONFINITE,
  SINGULAR_POLE,
  type EvalBudget,
  type Node,
  unverifiedKind,
  precisionMessage,
  provenInteger,
} from "./node";
import { EXACT_TOO_LARGE } from "./exactBudget";
import { decadeOf, inScaledShell, oddSeriesOf, isMarkedExactInt, knownValue } from "./lowering";
import { isSeriesShortcut } from "./node";
import { floatShowsComponent } from "./format";

/**
 * Wide-exponent complex values for EML circuits.
 *
 * decimal.js supplies the significand and an exponent far past float64's
 * ~709 limit. The branch rules match lib/eml/complex.ts: eml's logarithm
 * sits on the lower bank of the negative-real cut. An imaginary part of
 * exact zero, including −0, uses arg = −π. A nonzero imaginary part, however
 * small, keeps atan2, so −2 ± 10^(−300)i stay off the cut.
 * The log inside eml uses the lower bank: ln(+0) = −∞, ln(−0) = −∞ − iπ,
 * and ln(−∞) = +∞ − iπ. The composed ln program then matches principal Log,
 * so that program's ln(−0) is −∞ + iπ. exp(−∞) = +0, and exp(−∞ + iπ) = −0,
 * which is what makes the circuit for 0² come out 0. Float64 keeps the same
 * signs; 1/(−0) = −∞ there.
 *
 * Each eml subtraction drops a component only when it cancelled below the
 * working tolerance of its own terms. That turns the circuit for 0 into
 * exact 0, so later ln(0) and exp(−∞) stay on the extended-value rules
 * instead of amplifying a 10^(−precision) residual.
 */

const PRECISION = 120;
/** v1.1: significant digits on screen, the same as float mode's toPrecision(12). */
const SHOWN_DIGITS = 12;
/** v1.1: below this, scientific notation, as float mode does below 10^(−6). (Was 10^(−9).) */
const FIXED_FLOOR = "1e-6";

const D = Decimal.clone({ precision: PRECISION, minE: -9e15, maxE: 9e15 });

function tol(): Decimal {
  return new D(10).pow(-(D.precision - 8));
}
const ZERO = new D(0);
const ONE = new D(1);
const NEG_INF = new D(-Infinity);
const POS_INF = new D(Infinity);
const NAN = new D(NaN);

export type Z = { re: Decimal; im: Decimal };

const Z1: Z = { re: ONE, im: ZERO };

function z(re: Decimal.Value, im: Decimal.Value = 0): Z {
  return { re: new D(re), im: new D(im) };
}

function signedInf(part: Decimal): Decimal {
  if (part.abs().lte(tol())) return part.isNeg() ? new D(-0) : ZERO;
  return part.isNeg() ? NEG_INF : POS_INF;
}

function signedZeroFrom(part: Decimal): Decimal {
  return part.isNeg() ? new D(-0) : ZERO;
}

/**
 * cos and sin. An angle within the working tolerance of a multiple of π/2 is
 * that axis, so exp(iπ) is −1 and the composed logarithm takes the upper bank.
 * π − 10^(−12) is far outside this tolerance.
 */
function cosSin(theta: Decimal): { c: Decimal; s: Decimal } {
  const pi = D.acos(-1);
  const half = pi.div(2);
  const steps = theta.div(half).toNearest(1);
  if (theta.sub(steps.mul(half)).abs().lte(tol())) {
    const ax = ((steps.toNumber() % 4) + 4) % 4;
    if (ax === 0) return { c: ONE, s: ZERO };
    if (ax === 1) return { c: ZERO, s: ONE };
    if (ax === 2) return { c: ONE.neg(), s: ZERO };
    return { c: ZERO, s: ONE.neg() };
  }
  return { c: theta.cos(), s: theta.sin() };
}

function axisInfinity(part: Decimal): Decimal {
  // exp(+∞ ± iπ/2) is a pure imaginary infinity. The binary64 quarter turn
  // is about 10^(−16) off true π/2, and Infinity times that residual is NaN
  // once a later step subtracts the two infinities.
  if (part.abs().lt("1e-15")) return part.isNeg() ? new D(-0) : ZERO;
  return part.isNeg() ? NEG_INF : POS_INF;
}

function expZ(v: Z): Z {
  if (!v.im.isFinite()) return { re: NAN, im: NAN };
  const trig = v.im.isFinite() ? cosSin(v.im) : { c: NAN, s: NAN };
  if (!v.re.isFinite()) {
    if (v.re.isNeg()) return { re: signedZeroFrom(trig.c), im: signedZeroFrom(trig.s) };
    if (v.re.isPos()) return { re: axisInfinity(trig.c), im: axisInfinity(trig.s) };
    return { re: NAN, im: NAN };
  }
  const mag = v.re.exp();
  if (!v.re.isZero() && mag.eq(1)) noteAbsorb(ONE, v.re);
  // v1.1 (overnight Finding 8): exp(iθ) with a huge θ carries |θ|·10^(−digits) of angle
  // error, so its parts are only good to that absolute size. Record it as working scale,
  // and the dust check clears i^(10^20)'s 3.5×10^(−97) i once it moves with the digits.
  if (!v.im.isZero() && v.im.e >= 2 && mag.isFinite() && !mag.isZero()) {
    const w = v.im.e + mag.e;
    if (w > emlWork) emlWork = w;
    if (w > emlWorkRe) emlWorkRe = w;
    if (w > emlWorkIm) emlWorkIm = w;
  }
  if (mag.isZero()) return { re: signedZeroFrom(trig.c), im: signedZeroFrom(trig.s) };
  if (!mag.isFinite()) return { re: signedInf(trig.c), im: signedInf(trig.s) };
  return { re: mag.mul(trig.c), im: mag.mul(trig.s) };
}

/**
 * Lower bank, exact cut only. Imaginary dust is a real point off the axis:
 * −2 + 10^(−300)i is not rewritten as −2.
 */
let exactTraceNode: object | null = null;
let loggedCut = false;

function lnEml(v: Z): Z {
  // Log(NaN) is NaN. A non-finite test is true for NaN and must not turn it into +∞.
  loggedCut = onNegativeCutZ(v);
  if (exactTraceNode) noteExactGate(exactTraceNode, v);
  if (v.re.isNaN() || v.im.isNaN()) return { re: NAN, im: NAN };
  const negPi = D.acos(-1).neg();
  if (v.re.isZero() && v.im.isZero()) {
    if (v.re.isNeg()) return { re: NEG_INF, im: negPi };
    return { re: NEG_INF, im: v.im.isNeg() ? new D(-0) : ZERO };
  }
  const mag = D.hypot(v.re, v.im);
  if (mag.isZero()) return { re: NEG_INF, im: v.re.isNeg() ? negPi : ZERO };
  const onCut = v.im.isZero() && v.re.isNeg();
  if (v.re.isNeg() && v.re.isFinite() && (v.im.isZero() || v.re.e - v.im.e > D.precision - 24)) {
    cutSeen = true;
    nodeCut = true;
  }
  let arg = onCut ? negPi : (atan2Fast(v.im, v.re) ?? D.atan2(v.im, v.re));
  if (!onCut && !v.im.isZero() && (arg.eq(negPi) || arg.eq(negPi.neg()))) {
    const gap = v.re.e - v.im.e;
    if (Number.isFinite(gap) && gap > 8 && gap < 2000) {
      const local = D.clone({ precision: D.precision + gap + 8 });
      arg = new D(local.atan2(new local(v.im.toString()), new local(v.re.toString())).toString());
    }
  }
  if (!mag.isFinite()) return { re: POS_INF, im: arg.isFinite() ? arg : ZERO };
  if (!v.re.isZero() && !v.im.isZero()) {
    const [big, small] = v.re.abs().gte(v.im.abs()) ? [v.re.abs(), v.im.abs()] : [v.im.abs(), v.re.abs()];
    // ln|z| = ln|big| + small²/(2 big²) + …; hypot drops that term once 2·gap passes the precision.
    if (mag.eq(big)) noteAbsorb(ONE, new D(10).pow(-2 * (big.e - small.e)));
  }
  return { re: D.ln(mag), im: arg };
}

/**
 * atan2 from a float seed and one tangent correction: θ = θ₀ + atan(t),
 * t = (y cos θ₀ − x sin θ₀)/(x cos θ₀ + y sin θ₀), |t| ≈ 1e−16, atan(t) by its
 * odd series to full precision. Near ±π the angle is π − atan2(|y|, −x).
 * Returns null for zero or non-finite parts; the caller then uses D.atan2.
 */
function atan2Fast(y: Decimal, x: Decimal): Decimal | null {
  if (!y.isFinite() || !x.isFinite() || y.isZero() || x.isZero()) return null;
  const digits = D.precision;
  if (x.isNeg() && y.abs().lt(x.abs())) {
    const phi = atan2Core(y.abs(), x.neg(), digits);
    if (!phi) return null;
    const local = D.clone({ precision: digits + 12 });
    const out = local.acos(-1).sub(phi);
    return new D(y.isNeg() ? out.neg() : out);
  }
  const th = atan2Core(y, x, digits);
  return th ? new D(th) : null;
}

function atan2Core(y: Decimal, x: Decimal, digits: number): Decimal | null {
  const local = D.clone({ precision: digits + 12 });
  const shift = Math.max(y.e, x.e);
  const scale = new local(10).pow(-shift);
  const Y = new local(y);
  const X = new local(x);
  const ys = Y.mul(scale).toNumber();
  const xs = X.mul(scale).toNumber();
  if (!Number.isFinite(ys) || !Number.isFinite(xs) || (ys === 0 && xs === 0)) return null;
  const seed = Math.atan2(ys, xs);
  const th = new local(seed);
  const a = Math.abs(seed);
  let c: Decimal;
  let s: Decimal;
  if (a < Math.PI / 4 || a > (3 * Math.PI) / 4) {
    s = th.sin();
    c = local.sqrt(local.sub(1, s.mul(s)));
    if (a > Math.PI / 2) c = c.neg();
  } else {
    c = th.cos();
    s = local.sqrt(local.sub(1, c.mul(c)));
    if (seed < 0) s = s.neg();
  }
  const t = Y.mul(c).sub(X.mul(s)).div(X.mul(c).plus(Y.mul(s)));
  if (!t.isFinite() || t.abs().gt("1e-8")) return null;
  const t2 = t.mul(t);
  const eps = new local(10).pow(-(digits + 10));
  let term = t;
  let sum = t;
  for (let n = 3; term.abs().gt(eps) && n < 4001; n += 2) {
    term = term.mul(t2).neg();
    sum = sum.plus(term.div(n));
  }
  return th.plus(sum);
}

/** Decades cancelled inside one subtraction. A later pass may raise precision. */
let lossGap = 0;
/**
 * Largest cancellation (decades) at a gate inside a scaled shell in this pass. Shell gates
 * carry no work, so a lifted tiny sum's cancellation was invisible: 1e−320·(1+1e−100) −
 * 1e−320 cancelled 100 decades at 120 digits and certified 1.00000003×10^(−420).
 * Ported from main 1.0.1 (6704f98, 2c5db2f).
 */
let shellLoss = 0;
/** Most negative exponent of a nonzero finite value computed in this pass. */
let tiniest = 0;
/**
 * Finding 4 (v1.1): a Log argument sat on, or within dust of, the negative real axis in
 * this pass. Its bank then depends on an imaginary part that may have fallen off the
 * working precision (ln(−2 − i/10^130), sqrt(−4 − 10^(−130) i)).
 */
let cutSeen = false;
let nodeCut = false;

/** Smallest nonzero exponent of a value, as noteSeen counts it (0 when none). */
function partExp(v: Z): number {
  let e = 0;
  for (const part of [v.re, v.im]) if (part.isFinite() && !part.isZero() && part.e < e) e = part.e;
  return e;
}
function leafTiny(n: Node | undefined): number {
  if (!n || n.type !== "input") return 0;
  return partExp(z(n.value.re, n.value.im));
}
function imExp(v: Z): number {
  return v.im.isFinite() && !v.im.isZero() && v.im.e < 0 ? v.im.e : 0;
}
function leafTinyIm(n: Node | undefined): number {
  if (!n || n.type !== "input") return 0;
  return imExp(z(n.value.re, n.value.im));
}
function noteSeen(v: Z): void {
  const take = (part: Decimal) => {
    if (part.isFinite() && !part.isZero() && part.e < tiniest) tiniest = part.e;
  };
  take(v.re);
  take(v.im);
  if (v.im.isFinite() && !v.im.isZero() && v.im.e < tiniestIm) tiniestIm = v.im.e;
}
/** Finding 4: decade of the smallest nonzero imaginary part this pass saw (the side of a cut). */
let tiniestIm = 0;
/**
 * Size of the terms that cancelled by at least two decades in the last
 * exactEml call (decimal exponent). Rounding there leaves absolute noise near
 * 10^(size − precision). A gate that does not cancel keeps its relative
 * accuracy, so its size is not counted.
 */
let emlWork = Number.NEGATIVE_INFINITY;
let emlWorkRe = Number.NEGATIVE_INFINITY;
let emlWorkIm = Number.NEGATIVE_INFINITY;
/**
 * v1.1 prototype (compscibot): absorbed terms. A nonzero operand that a gate
 * dropped whole because it sat below the working precision of its partner:
 * |small| < ulp(big). `emlAbsorbGap` is the decade gap, `emlAbsorbExp` the
 * decade of the lost term. Cancellation to dust is not this; that is lossGap.
 */
let emlAbsorbGap = Number.NEGATIVE_INFINITY;
let emlAbsorbExp = Number.POSITIVE_INFINITY;
function noteAbsorb(big: Decimal, small: Decimal): void {
  if (ABSORB_OFF) return;
  if (!big.isFinite() || !small.isFinite() || big.isZero() || small.isZero()) return;
  const gap = big.e - small.e;
  if (!Number.isFinite(gap) || gap < D.precision - 2) return;
  if (gap > emlAbsorbGap) emlAbsorbGap = gap;
  if (small.e < emlAbsorbExp) emlAbsorbExp = small.e;
}
/** diff = left − right came out equal to one operand while the other was nonzero. */
function checkAbsorb(diff: Decimal, left: Decimal, right: Decimal): void {
  if (ABSORB_OFF) return;
  if (!diff.isFinite() || !left.isFinite() || !right.isFinite()) return;
  if (!right.isZero() && diff.eq(left) && !left.isZero()) noteAbsorb(left, right);
  else if (!left.isZero() && diff.eq(right.neg()) && !right.isZero()) noteAbsorb(right, left);
}
/** Working precision is never raised past this. A value that still needs more is not certified. */
const PRECISION_CAP = 480;

/**
 * v1.1 suite profiling, off unless EML_PROF names an output file. Inclusive wall
 * time and counts per policy path, so the suite slowdown can be attributed.
 * EML_ABSORB_OFF=1 disables the absorbed-term detector (profiling only).
 */
const PROF_FILE = typeof process !== "undefined" ? process.env?.EML_PROF : undefined;
const PROF = PROF_FILE ? new Map<string, { n: number; ms: number }>() : null;
const profRoots = new WeakSet<object>();
const ABSORB_OFF = typeof process !== "undefined" && process.env?.EML_ABSORB_OFF === "1";
function prof(key: string, t0: number): void {
  if (!PROF) return;
  const row = PROF.get(key) ?? { n: 0, ms: 0 };
  row.n += 1;
  row.ms += performance.now() - t0;
  PROF.set(key, row);
}
if (PROF && PROF_FILE && typeof process !== "undefined") {
  // One stderr line, tagged with EML_PROF's value; no fs import, so the browser bundle is unaffected.
  process.on("exit", () => console.error(`EML_PROF ${PROF_FILE} ${JSON.stringify(Object.fromEntries(PROF))}`));
}

function noteWork(left: Decimal, right: Decimal, diff: Decimal, part: "re" | "im"): void {
  const scale = D.max(left.abs(), right.abs());
  if (!scale.isFinite() || scale.isZero()) return;
  if (!(diff.isZero() || scale.e - diff.abs().e >= 2)) return;
  emlWork = Math.max(emlWork, scale.e);
  if (part === "re") emlWorkRe = Math.max(emlWorkRe, scale.e);
  else emlWorkIm = Math.max(emlWorkIm, scale.e);
}

/** The loss gap noted by the node being evaluated (reset per node), for the cache replay. */
let nodeLoss = 0;
function noteLoss(scale: Decimal, residual: Decimal): void {
  if (!scale.isFinite() || scale.isZero() || !residual.isFinite() || residual.isZero()) return;
  const gap = scale.e - residual.abs().e;
  if (Number.isFinite(gap) && gap > nodeLoss) nodeLoss = gap;
  if (Number.isFinite(gap) && gap > lossGap) lossGap = gap;
}

function cancelled(diff: Decimal, left: Decimal, right: Decimal, part: "re" | "im"): Decimal {
  if (!diff.isFinite()) return diff;
  noteWork(left, right, diff, part);
  // Keep a signed zero. exp(−∞ + iπ) is −0, and wiping that sign makes √0 infinite.
  if (diff.isZero()) return diff.isNeg() ? new D(-0) : ZERO;
  const scale = D.max(left.abs(), right.abs());
  noteLoss(scale, diff);
  if (scale.gt(0) && diff.abs().lte(scale.mul(tol()))) return ZERO;
  return diff;
}

/**
 * A component this far below its neighbour is working-precision dust.
 * 6.7×10^(−106) beside a component ~70 decades away stays: that gap fits in
 * 120 digits. Dust at the tolerance, such as 10^(−104) beside 10^8, does not.
 * A component below an ulp of 1 is not dropped here. 10^(−120) beside 2×10^(−120),
 * and 10^(−125) i beside 10^(−18), are real parts. Cancellation dust is removed
 * only after a second evaluation shows that the part moved.
 */
function scrubDust(v: Z, floorDigits = D.precision, keepBuried = false): Z {
  if (!v.re.isFinite() || !v.im.isFinite()) return v;
  const scale = D.max(v.re.abs(), v.im.abs());
  if (!scale.isFinite() || scale.isZero()) return v;
  // v1.1: after a raised pass the floor is that pass's, so a part it resolved (the K33 −iπ word's 5.7e−116) survives.
  const floor = scale.mul(new D(10).pow(-(floorDigits - 12)));
  const buried = scale.mul(new D(10).pow(-160));
  const limit = keepBuried ? floor : D.max(floor, buried);
  const visible = new D(10).pow(-12);
  const leading = D.max(v.re.abs(), v.im.abs());
  const keep = (part: Decimal) => {
    if (part.isZero() || part.abs().eq(leading)) return part;
    return part.abs().gte(limit) || part.abs().gte(visible) ? part : part.isNeg() ? new D(-0) : ZERO;
  };
  return { re: keep(v.re), im: keep(v.im) };
}

/** ∞ − ∞ of one sign is indeterminate. +∞ − (−∞) stays +∞. */
function sameInfinity(left: Decimal, right: Decimal): boolean {
  return !left.isNaN() && !right.isNaN() && !left.isFinite() && !right.isFinite() && left.isNeg() === right.isNeg();
}

function exactEml(x: Z, y: Z): Z {
  if (x.re.isNaN() || x.im.isNaN() || y.re.isNaN() || y.im.isNaN()) return { re: NAN, im: NAN };
  const a = expZ(x);
  const b = lnEml(y);
  if (a.re.isNaN() || a.im.isNaN() || b.re.isNaN() || b.im.isNaN()) return { re: NAN, im: NAN };
  if (sameInfinity(a.re, b.re) || sameInfinity(a.im, b.im)) return { re: NAN, im: NAN };
  checkAbsorb(a.re.sub(b.re), a.re, b.re);
  checkAbsorb(a.im.sub(b.im), a.im, b.im);
  const re = cancelled(a.re.sub(b.re), a.re, b.re, "re");
  const im = cancelled(a.im.sub(b.im), a.im, b.im, "im");
  if (re.isNaN() || im.isNaN()) return { re: NAN, im: NAN };
  return { re, im };
}

function asZ(value: C | Z): Z {
  if (value.re instanceof Decimal) return value as Z;
  return z(value.re, value.im);
}

export type ExactReport = {
  value: Z;
  singular: string | null;
  touchedLn0: boolean;
  unverified?: boolean;
  /** Largest cancelling term size outside the 2^k lift gates (decimal exponent). */
  workExp?: number;
  /** Per-component cancellation size. A part with no finite work was not a residue. */
  workRe?: number;
  workIm?: number;
  /** v1.1: largest decade gap of a nonzero term a gate dropped (|small| < ulp(big)). */
  absorbedGap?: number;
  /** v1.1: decades below x of the furthest odd-series term exact mode kept (exact.ts series hook). */
  seriesKept?: number;
  /** v1.1: decade of the smallest such term. */
  absorbedExp?: number;
  /** v1.1: set when an absorbed term could not be resolved under the cap. Sticky to the display. */
  notCertified?: { reason: "absorbed"; termDecade: number; gap: number };
  /** Precision the value was computed at. */
  digits?: number;
  /** A series shortcut was used. A zero from that shortcut is not certified. */
  sawLead?: boolean;
  /** Logarithms of a negative real, counted at each log call. A cached subcircuit adds its stored count. */
  cutHits: number;
  /** A Log argument was on or within dust of the negative real axis (Finding 4). */
  cutSeen?: boolean;
  /** Decade of the smallest nonzero value this pass saw. */
  tiniestExp?: number;
  /** Decade of the smallest nonzero imaginary part this pass saw (Finding 4). */
  tiniestImExp?: number;
  /**
   * v1.1 (reviewbot E3): the value is 0 and the first pass recorded a cancellation
   * (lossGap or an absorbed term). The screen must not call such a 0 "the usual value"
   * or show it as the reference in "float differs from exact · 0".
   */
  cancelledZero?: boolean;
};

/**
 * `loss`, `tiny` and `lead` (v1.1, overnight Finding 1/5): what a subtree contributed to the
 * pass-wide lossGap, tiniest and sawLead. A pureCache hit skips the subtree, so it must
 * replay these, or a repeat compute certifies a 0 the first compute escalated away.
 */
type Work = { all: number; re: number; im: number; ab?: number; abE?: number; kept?: number; loss?: number; sh?: number; tiny?: number; tinyIm?: number; lead?: boolean; cut?: boolean };
type Cached = { value: Z; why: string | null; logged: boolean; work: Work; cutHits: number };
/** Var-free subcircuits, by working precision. A rebuilt circuit is new nodes, so it misses this map. */
const pureCache = new Map<number, WeakMap<Node, Cached>>();
const hasVarOf = new WeakMap<Node, boolean>();
const NOCACHE = typeof process !== "undefined" && process.env?.EML_NOCACHE === "1";

function zZero(v: Z): boolean {
  return v.re.isZero() && v.im.isZero();
}

function zFinite(v: Z): boolean {
  return v.re.isFinite() && v.im.isFinite();
}

/**
 * Evaluate a pure or user-bound circuit with wide exponents.
 * `maxNodes` and `deadline` (a performance.now() instant) stop a huge circuit
 * from running without a result. Exact mode uses the same cut as float64:
 * Arg = −π on a negative real, so the composed ln matches principal Log.
 */
function vanished(v: Z): boolean {
  return v.re.isZero() && v.im.isZero();
}

/**
 * Digits needed when a known leaf is too small for the current precision.
 * A large magnitude such as 10^300 is already exact at 120 digits; raising
 * precision there exposes rounding in the circuit and must not happen.
 */
function demandedTinyDigits(root: Node, env: Record<string, C | Z>): number {
  let need = 0;
  const takeExp = (exp: number) => {
    if (!Number.isFinite(exp) || exp >= -(PRECISION - 24)) return;
    need = Math.max(need, -exp + 48);
  };
  const takePart = (part: number | Decimal) => {
    if (part instanceof D) {
      if (!part.isFinite() || part.isZero()) return;
      takeExp(part.e);
      return;
    }
    if (!Number.isFinite(part) || part === 0) return;
    takeExp(Math.floor(Math.log10(Math.abs(part))));
  };
  for (const value of Object.values(env)) {
    takePart(value.re);
    takePart(value.im);
  }
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    const known = knownValue(n);
    if (known) {
      takePart(known.re);
      takePart(known.im);
    }
    const decade = decadeOf(n);
    if (decade !== undefined && decade < -(PRECISION - 24)) need = Math.max(need, -decade + 48);
    if (n.type === "eml" && n.a && n.b) stack.push(n.a, n.b);
  }
  return need;
}

function atPrecision(digits: number, root: Node, env: Record<string, C | Z>, budget: EvalBudget, keepBuried = false): ExactReport {
  const saved = D.precision;
  D.set({ precision: digits });
  const savedKeep = keepBuriedPass;
  keepBuriedPass = keepBuried;
  try {
    const report = exactReport(root, env, budget, 2);
    if (digits <= saved) return report;
    // The retry can carry hundreds of extra digits. The suite compares the
    // working-precision value, so round back once the hidden component is recovered.
    D.set({ precision: saved });
    const round = (part: Decimal) => (part.isFinite() ? new D(part.toSignificantDigits(saved).toString()) : part);
    return { ...report, digits, value: scrubDust({ re: round(report.value.re), im: round(report.value.im) }, process.env?.EML_SCRUB_AT_SAVED === "1" ? saved : digits, keepBuried) };
  } finally {
    D.set({ precision: saved });
    keepBuriedPass = savedKeep;
  }
}

/**
 * A huge result with one component exactly 0. Scaling by that magnitude
 * drops the other component once it falls off the working precision
 * (10^300 + i). The decision uses only the value, so a rebuilt circuit
 * retries the same way.
 */
function hiddenComponent(value: Z): boolean {
  if (!value.re.isFinite() || !value.im.isFinite()) return false;
  if (value.re.isZero() === value.im.isZero()) return false;
  return Math.max(value.re.e, value.im.e) > D.precision - 24;
}

/**
 * Imaginary part sitting on ±π. A tiny imaginary input that fell off the
 * working precision chooses this bank, so the result is not certified there
 * until that input fits.
 */
function nearCut(part: Decimal): boolean {
  if (!part.isFinite() || part.isZero()) return false;
  const pi = D.acos(-1);
  return part.abs().sub(pi).abs().lt("1e-6");
}

/** Set while the cut-side escalation's own pass runs, so its pass-2 present() keeps the part too. */
let keepBuriedPass = false;
function present(report: ExactReport, cutFloor?: number): ExactReport {
  if (keepBuriedPass && cutFloor === undefined) return { ...report, value: scrubDust(report.value, D.precision, true) };
  // v1.1 (Finding 4): after the cut-side escalation the small part is the one that decided
  // the bank (sqrt(−4 − i/10^130) = 2.5×10^(−131) − 2i), so it keeps that pass's floor and is
  // not dropped as buried. Everywhere else the pristine floor stands.
  return { ...report, value: scrubDust(report.value, cutFloor ?? D.precision, cutFloor !== undefined) };
}

/**
 * The part under the circuit's own rounding noise, beside a part above it.
 * The noise follows the size the circuit cancelled at, not a fixed 10^(−112):
 * arcsin(10^(−18) i) cancels terms near 1 and leaves about 10^(−120) beside
 * 10^(−18) i. The 2^k lift gates are not counted.
 */
function dustPart(report: ExactReport): "re" | "im" | null {
  const { value: v, workExp } = report;
  if (workExp === undefined || !Number.isFinite(workExp)) return null;
  if (!v.re.isFinite() || !v.im.isFinite() || v.re.isZero() || v.im.isZero()) return null;
  const noise = new D(10).pow(workExp - ((report.digits ?? D.precision) - 12));
  if (v.re.abs().lt(noise) && v.im.abs().gte(noise)) return "re";
  if (v.im.abs().lt(noise) && v.re.abs().gte(noise)) return "im";
  return null;
}

/**
 * A part under the noise is not always dust: 10^(−18) + 10^(−125) i reaches
 * its imaginary part through exp and ln, which keep relative accuracy. Dust
 * moves when the precision rises and a computed part does not, so evaluate
 * once more with 24 more digits and clear the part only if it moved.
 */
function confirmDust(report: ExactReport, root: Node, env: Record<string, C | Z>, budget: EvalBudget): ExactReport {
  const which = dustPart(report);
  if (!which) return report;
  const part = report.value[which];
  let again: Decimal;
  const td = PROF ? performance.now() : 0;
  try {
    again = atPrecision((report.digits ?? D.precision) + 24, root, env, budget).value[which];
  } catch (err) {
    if (isTimeout(err)) throw err;
    return report;
  } finally {
    prof("confirmDust atPrecision", td);
  }
  if (again.isFinite() && part.sub(again).abs().lte(part.abs().mul("1e-6"))) return report;
  const cleared = part.isNeg() ? new D(-0) : ZERO;
  return { ...report, value: which === "re" ? { re: cleared, im: report.value.im } : { re: report.value.re, im: cleared } };
}

/**
 * v1.1 (overnight Finding 3): a vanished result raised to k + 48 digits is good to about
 * 48 significant digits, not to the working 120. (exp(10^(−130)) − 1)·10^130 came back as
 * 1.000…0001 with a noise digit at the 49th place. Keep 40.
 */
const TRUST_DIGITS = 40;
function trustDigits(report: ExactReport): ExactReport {
  const round = (part: Decimal) => (part.isFinite() && !part.isZero() ? part.toSignificantDigits(TRUST_DIGITS) : part);
  return { ...report, value: { re: round(report.value.re), im: round(report.value.im) } };
}

/** v1.1 (E6): the cooperative deadline ends the whole job; no catch may turn it into a value. */
function isTimeout(err: unknown): boolean {
  return err instanceof EmlLimitError && err.message === EXACT_TIMED_OUT;
}

function certifyZero(report: ExactReport): ExactReport {
  return { ...present(report), unverified: true };
}

/** A component this far below the terms that cancelled is not yet a result. */
function residueFloor(work: number, digits: number): Decimal {
  return new D(10).pow(work - (digits - 12));
}

/**
 * Parts that are small beside the terms that cancelled, exact zeros included.
 * A true zero beside an ordinary value, such as the imaginary part of sin(1),
 * is not on this list: its sibling is not small next to those terms.
 */
function residueParts(report: ExactReport): Array<"re" | "im"> {
  if (vanished(report.value) || report.unverified) return [];
  const digits = report.digits ?? D.precision;
  const out: Array<"re" | "im"> = [];
  const consider = (name: "re" | "im", part: Decimal, work: number | undefined, other: Decimal) => {
    if (work === undefined || !Number.isFinite(work) || !part.isFinite()) return;
    if (!part.isZero()) {
      if (part.abs().lt(residueFloor(work, digits))) out.push(name);
      return;
    }
    const siblingSmall = other.isFinite() && !other.isZero() && other.abs().lt(new D(10).pow(work - 12));
    if (siblingSmall) out.push(name);
  };
  consider("re", report.value.re, report.workRe, report.value.im);
  consider("im", report.value.im, report.workIm, report.value.re);
  return out;
}

/** Same relative move the dust check uses. An exact zero that becomes nonzero has moved. */
function residueMoved(before: Decimal, after: Decimal): boolean {
  if (!before.isFinite() || !after.isFinite()) return !before.eq(after);
  if (before.isZero() && after.isZero()) return false;
  if (before.isZero() || after.isZero()) return true;
  return after.sub(before).abs().gt(before.abs().mul("1e-6"));
}

/**
 * Re-evaluate a residue with more digits. A part that stays put is real, the
 * same way dust is kept. A part that moves is not certified at this precision:
 * raise it, up to 480 digits, or leave the result unverified.
 */
function settleResidue(
  report: ExactReport,
  root: Node,
  env: Record<string, C | Z>,
  budget: EvalBudget,
): ExactReport {
  let current = report;
  for (let hop = 0; hop < 8; hop += 1) {
    const which = residueParts(current);
    if (which.length === 0) return current;
    const digits = current.digits ?? D.precision;
    const hinted = demandedTinyDigits(root, env);
    if (digits >= PRECISION_CAP) return certifyZero(current);
    // A known magnitude past the cap cannot come back. That only withholds a
    // zero component. A nonzero value that does not move on the next check stays.
    if (hinted > PRECISION_CAP && which.some((name) => current.value[name].isZero())) return certifyZero(current);
    const step = hop === 0 ? 24 : 96;
    const raised = hinted > digits && hinted <= PRECISION_CAP ? hinted : 0;
    const next = Math.min(PRECISION_CAP, Math.max(digits + step, raised));
    if (next <= digits) return certifyZero(current);
    let again: ExactReport;
    const ts = PROF ? performance.now() : 0;
    try {
      again = atPrecision(next, root, env, budget);
    } catch (err) {
      if (isTimeout(err)) throw err;
      return certifyZero(current);
    } finally {
      prof("settleResidue atPrecision", ts);
    }
    const changed = which.some((name) => residueMoved(current.value[name], again.value[name]));
    if (!changed) return current;
    current = again;
  }
  return residueParts(current).length === 0 ? current : certifyZero(current);
}

/**
 * A huge integer kept beside a non-integer is a mul by a leaf labelled `beside:`.
 * That mul is not the sum: exact evaluation would certify the bare integer.
 * The leaf sits next to the root, so this does not walk the power.
 */
/**
 * Whether the circuit uses a remembered huge sum (rememberHugeReal) anywhere. That
 * node's gates hold only the bare integer, so any circuit built on it drops the
 * small term. The walk covers the whole DAG: a depth-8 / 64-step cap missed the
 * marker under the product word, and (10^400+i)·2 was certified as 2×10^400.
 */
function hidesBeside(root: Node): boolean {
  const known = besideMemo.get(root);
  if (known !== undefined) return known;
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  let found = false;
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    if (node.type === "input") {
      if (node.label.startsWith("beside:")) {
        found = true;
        break;
      }
      continue;
    }
    if (node.type === "eml") stack.push(node.a, node.b);
  }
  besideMemo.set(root, found);
  return found;
}
const besideMemo = new WeakMap<Node, boolean>();

/**
 * v1.1 prototype: absorbed-term policy. One decision, no loop: a gap that fits
 * under the cap is re-run once at gap + 48 digits; a gap past the cap (the
 * #431 tower's ~1.66M decades) is marked not certified at once.
 */
/** lossGap (or absorbed gap) of the last pass-0 first evaluation, for E3's cancelledZero. */
let firstPassGap = 0;

export function exactReport(
  root: Node,
  env: Record<string, C | Z> = {},
  budget: EvalBudget = {},
  pass = 0,
): ExactReport {
  if (pass !== 0) return exactReportAbsorb(root, env, budget, pass);
  firstPassGap = 0;
  const out = exactReportAbsorb(root, env, budget, pass);
  // v1.1 (item 6): beside a possible infinity only "undefined" (NaN) is a result.
  if (!out.unverified && unverifiedKind(root) === 1 && !(out.value.re.isNaN() && out.value.im.isNaN())) {
    return { value: { re: NAN, im: NAN }, singular: null, touchedLn0: false, unverified: true, cutHits: 0 };
  }
  if (!out.unverified && vanished(out.value) && firstPassGap > 0) return { ...out, cancelledZero: true };
  return out;
}

function exactReportAbsorb(
  root: Node,
  env: Record<string, C | Z>,
  budget: EvalBudget,
  pass: number,
): ExactReport {
  const t0 = PROF ? performance.now() : 0;
  const report = exactReportCore(root, env, budget, pass);
  if (PROF && pass === 0) prof("exactReport pass0 core (incl. all escalation)", t0);
  if (pass !== 0 || report.unverified) return report;
  const gap = report.absorbedGap;
  if (gap === undefined || !Number.isFinite(gap) || gap <= 0) return report;
  // Only a result that reads as exact makes a claim the lost term can break:
  // an integer or zero in each component (−1 for #431 and #5884). 1×10^300 for
  // 10^300 + 1 is already a 12-digit rounding and is left alone (no retry cost).
  // A component that is exactly 0 is also a claim: the K33 −iπ word's real part.
  if (!looksExact(report.value) && !report.value.re.isZero() && !report.value.im.isZero()) return report;
  const digits = report.digits ?? D.precision;
  // Suite-time cut (v1.1 profile): a gap at the precision edge (≤ digits + 16) is rounding dust
  // in 96 of 96 suite retries. digits + 24 already moves dust by 24 decades and fits any real
  // term up to 10^(−(digits+16)), so it decides the same thing for less work than gap + 48.
  const edge = gap <= digits + 16;
  const need = edge ? digits + 24 : gap + 48;
  // At most ONE re-run per result (Ben, v1.1): atPrecision re-enters with pass 2, which returns
  // before this block, so the retry can never retry again.
  if (need <= PRECISION_CAP && need > digits && process.env?.EML_ABSORB_RETRY !== "0") {
    let again: ExactReport;
    const tr = PROF ? performance.now() : 0;
    try {
      again = atPrecision(need, root, env, budget);
    } catch (err) {
      if (isTimeout(err)) throw err;
      again = report;
    }
    prof("absorb retry (one atPrecision)", tr);
    if (PROF) {
      const seenBefore = profRoots.has(root);
      profRoots.add(root);
      prof(`retry root ${seenBefore ? "repeat" : "first"}${Object.keys(env).length ? " env" : ""}`, tr);
      prof(`retry gap-digits ${gap - digits <= 16 ? "<=16" : gap - digits <= 100 ? "17..100" : ">100"}`, tr);
    }
    const left = again.absorbedGap;
    // Rounding dust is absorbed at about 10^(−digits) and moves when the digits rise
    // (cos π: 10^(−120), then 10^(−168)). A real lost term stays at its decade.
    const movedExp = again.absorbedExp !== undefined && report.absorbedExp !== undefined && Math.abs(again.absorbedExp - report.absorbedExp) > 8;
    const resolved = again !== report && (left === undefined || !Number.isFinite(left) || left < need - 2 || movedExp);
    // First-pass gap at the precision edge that moves with the digits: rounding dust.
    if (again !== report && movedExp && edge) {
      if (PROF) prof("retry outcome: dust (moved)", performance.now());
      return again;
    }
    if (PROF) prof(`retry outcome: ${resolved ? (looksExact(again.value) ? "resolved, still integer → nc" : "resolved, new value") : "unresolved → nc"}`, performance.now());
    // Resolved and no longer exact-looking: the raised value is the answer.
    if (resolved && !looksExact(again.value)) return again;
    // Resolved but still rounds to an integer (1 + 10^(−200)): say so instead of printing a bare 1.
    if (resolved) return { ...again, notCertified: { reason: "absorbed", termDecade: report.absorbedExp ?? Number.NEGATIVE_INFINITY, gap } };
  }
  if (PROF) prof("absorb flag without retry", performance.now());
  return { ...report, notCertified: { reason: "absorbed", termDecade: report.absorbedExp ?? Number.NEGATIVE_INFINITY, gap } };
}

function looksExact(v: Z): boolean {
  const part = (d: Decimal) => d.isZero() || (d.isFinite() && exactInteger(d));
  return part(v.re) && part(v.im);
}

function exactReportCore(
  root: Node,
  env: Record<string, C | Z> = {},
  budget: EvalBudget = {},
  pass = 0,
): ExactReport {
  // Evaluate at the current precision first. A result that collapsed to 0 is
  // retried when a known magnitude, or the cancellation itself, does not fit.
  // Past 480 digits the screen says it could not verify. A zero that stays
  // zero once those magnitudes fit is real, unless a series shortcut produced it.
  // A non-zero result stays, so 10^300 and asinh(10^155) keep the digits the
  // rest of the suite compares exactly.
  if (unverifiedKind(root) === 2 || hidesBeside(root)) {
    return { value: { re: NAN, im: NAN }, singular: null, touchedLn0: false, unverified: true, cutHits: 0 };
  }
  // The integer is the value. A later retry would rebuild the circuit and round off its units.
  if (isMarkedExactInt(root)) {
    const big = provenInteger(root);
    if (big !== undefined) {
      const text = big.toString();
      const width = text.startsWith("-") ? text.length - 1 : text.length;
      const saved = D.precision;
      if (width > saved) D.set({ precision: width });
      try {
        return { value: z(text, 0), singular: null, touchedLn0: false, cutHits: 0 };
      } finally {
        if (width > saved) D.set({ precision: saved });
      }
    }
  }
  lossGap = 0;
  shellLoss = 0;
  const report = exactReportOnce(root, env, budget);
  if (pass !== 0) return present(report);
  firstPassGap = Math.max(lossGap, report.absorbedGap ?? 0);
  const firstShell = shellLoss;
  if (vanished(report.value)) {
    if (report.sawLead) {
      // v1.1: an odd series that kept a term below the working digits (seriesKept) is
      // exact to the 480-digit cap, so f(x) − x is raised once to see that term. A zero
      // from the leading-term shortcut (no kept term) still cannot be verified.
      const kept = report.seriesKept;
      if (kept !== undefined && Number.isFinite(kept) && kept + 48 <= PRECISION_CAP && kept + 48 > D.precision) {
        const again = atPrecision(kept + 48, root, env, budget);
        if (!vanished(again.value)) return confirmDust(present(trustDigits(again)), root, env, budget);
      }
      return certifyZero(report);
    }
    const gap = lossGap;
    // Any recorded cancellation can hide the term that should have survived.
    // A structural zero such as 1−1 records no gap and stays certified.
    const fromGap = gap > 8 ? gap + 48 : 0;
    // E1 (v1.1): a press-built circuit has no build-time hints, so demandedTinyDigits is 0
    // and a 1 + 10^(−130) absorbed at 120 digits used to certify 0. The circuit itself
    // computed the tiny value: the smallest nonzero magnitude seen in this pass is a hint
    // that needs no tags and is the same cold or warm.
    const seenTiny = tiniest < -(D.precision - 24) ? -tiniest + 48 : 0;
    const hinted = demandedTinyDigits(root, env);
    const need = Math.max(hinted, fromGap, seenTiny);
    if (need > PRECISION_CAP) return certifyZero(report);
    if (need > D.precision) {
      const te = PROF ? performance.now() : 0;
      const cause = Math.max(hinted, fromGap) > D.precision ? "vanished escalation (hint/gap, as pristine)" : "vanished escalation (seenTiny only, E1)";
      try {
      let digits = Math.min(PRECISION_CAP, need);
      let again = atPrecision(digits, root, env, budget);
      // A snap that still lands on 0 is a deeper cancellation than this precision.
      // Raise again, up to the cap. A clean zero with no such snap is resolved.
      while (vanished(again.value) && !again.sawLead && digits < PRECISION_CAP && lossGap > digits - 24) {
        digits = Math.min(PRECISION_CAP, Math.max(digits + 96, lossGap + 48));
        again = atPrecision(digits, root, env, budget);
      }
      if (vanished(again.value)) {
        const seenNeed = tiniest < -(digits - 24) ? -tiniest + 48 : 0;
        if (again.sawLead || seenNeed > PRECISION_CAP) return certifyZero(again);
        if (seenNeed > digits) {
          again = atPrecision(Math.min(PRECISION_CAP, seenNeed), root, env, budget);
          if (vanished(again.value)) return certifyZero(again);
        } else if (lossGap > digits - 16) return certifyZero(again);
      }
      return confirmDust(present(trustDigits(again)), root, env, budget);
      } finally {
        prof(cause, te);
      }
    }
  }
  let settled = report;
  if (hiddenComponent(report.value)) {
    const digits = Math.min(PRECISION_CAP, Math.max(Math.max(report.value.re.e, report.value.im.e) + 48, D.precision + 32));
    if (digits > D.precision) settled = atPrecision(digits, root, env, budget);
  }
  settled = settleResidue(settled, root, env, budget);
  if (settled.unverified) return settled;
  // A lifted tiny sum keeps (digits − gap) digits: raise until 24 spare digits remain, or
  // say it is not certified past the cap (see shellLoss).
  if (!vanished(settled.value) && firstShell > (settled.digits ?? D.precision) - 24) {
    const need = firstShell + 48;
    if (need > PRECISION_CAP) return { ...settled, notCertified: { reason: "absorbed", termDecade: report.tiniestExp ?? Number.NEGATIVE_INFINITY, gap: firstShell } };
    settled = atPrecision(need, root, env, budget);
    if (settled.unverified) return settled;
  }
  // Finding 4 (v1.1): a Log argument on the cut side of the negative real axis with a tiny
  // value in the circuit. The bank is decided by whether that tiny value reaches the Log, so
  // evaluate once where it fits (the same k + 48 rule), or refuse to certify past the cap.
  let cutFloor: number | undefined;
  // Only a tiny *imaginary* part decides the bank: sin(2·10^(−200)) has 10^(−600) series
  // terms and an EML ln of a negative real in every subtraction, but nothing below the axis.
  const seenIm = report.tiniestImExp ?? 0;
  if (report.cutSeen && (settled.digits ?? D.precision) <= D.precision && seenIm < -(D.precision - 24)) {
    const need = -seenIm + 48;
    const tc = PROF ? performance.now() : 0;
    try {
      if (need > PRECISION_CAP) return certifyZero(settled);
      settled = atPrecision(need, root, env, budget, true);
      if (settled.unverified) return settled;
      cutFloor = need;
    } finally {
      prof("cut-side escalation (Finding 4)", tc);
    }
  }
  // ln(−2 − 10^(−p) i) collapses onto the cut once p passes the working
  // precision, and the composed log then certifies +π. The point is still
  // below the axis. Raise precision until the known power is visible, or
  // refuse to certify once that would pass 480 digits.
  if (nearCut(settled.value.im)) {
    const hinted = demandedTinyDigits(root, env);
    const digits = settled.digits ?? D.precision;
    if (hinted > digits) {
      if (hinted > PRECISION_CAP) return certifyZero(settled);
      settled = atPrecision(hinted, root, env, budget);
      if (settled.unverified) return settled;
    }
  }
  return confirmDust(present(settled, cutFloor), root, env, budget);
}

function exactReportOnce(
  root: Node,
  env: Record<string, C | Z> = {},
  budget: EvalBudget = {},
): ExactReport {
  const maxNodes = budget.maxNodes ?? 80_000;
  const deadline = budget.deadline ?? 0;
  const memo = new Map<Node, Z>();
  const why = new Map<Node, string | null>();
  const logged = new Map<Node, boolean>();
  const work = new Map<Node, Work>();
  const cuts = new Map<Node, number>();
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  let sawLead = false;
  tiniest = 0;
  tiniestIm = 0;
  cutSeen = false;
  let steps = 0;
  // v1.1 (E6): one progress call per pass; a deadline already past stops before the pass.
  budget.onProgress?.({ digits: D.precision });
  if (deadline && performance.now() > deadline) throw new EmlLimitError(EXACT_TIMED_OUT);
  let cache = pureCache.get(D.precision);
  if (!cache) {
    cache = new WeakMap();
    pureCache.set(D.precision, cache);
  }

  while (stack.length) {
    if ((++steps & 31) === 0) {
      if (steps > maxNodes) throw new EmlLimitError(EXACT_TOO_LARGE);
      if (deadline && performance.now() > deadline) throw new EmlLimitError(EXACT_TIMED_OUT);
    }
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n) throw new EmlError("Could not evaluate this circuit.");
    if (isSeriesShortcut(n)) sawLead = true;
    if (memo.has(n)) continue;
    if (isMarkedExactInt(n) && n.type !== "input") {
      const big = provenInteger(n);
      if (big !== undefined) {
        const value = z(big.toString(), 0);
        memo.set(n, value);
        noteSeen(value);
        why.set(n, null);
        logged.set(n, false);
        continue;
      }
    }

    // v1.1: an odd series node is its polynomial in x. Evaluate x, then the polynomial,
    // instead of the lifted circuit (seconds at 333 digits, and its far terms came out wrong).
    const poly = oddSeriesOf(n);
    if (poly) {
      const x = memo.get(poly.arg);
      if (!x) {
        stack.push({ n, seen: false });
        stack.push({ n: poly.arg, seen: false });
        continue;
      }
      if (x.im.isZero() && x.re.isFinite()) {
        const x2 = x.re.times(x.re);
        let acc = x.re;
        let power = x.re;
        // A term below the working precision of x is absorbed, as in a gate (noteAbsorb).
        let gap = Number.NEGATIVE_INFINITY;
        let lostExp = Number.POSITIVE_INFINITY;
        for (const [num, den, sign] of poly.coeffs) {
          power = power.times(x2);
          const term = power.times(num).div(den);
          const before = acc;
          acc = sign < 0 ? acc.minus(term) : acc.plus(term);
          if (!term.isZero() && acc.eq(before) && !before.isZero()) {
            gap = Math.max(gap, before.e - term.e);
            lostExp = Math.min(lostExp, term.e);
          }
        }
        const value: Z = { re: acc, im: ZERO };
        memo.set(n, value);
        noteSeen(value);
        why.set(n, why.get(poly.arg) ?? null);
        logged.set(n, logged.get(poly.arg) ?? false);
        const argWork = work.get(poly.arg);
        const ownWork: Work = { ...(argWork ?? { all: Number.NEGATIVE_INFINITY, re: Number.NEGATIVE_INFINITY, im: Number.NEGATIVE_INFINITY }) };
        // Not an absorbed term (ab): the series is exact to the cap, so a nonzero result
        // stands. `kept` only lets a vanished f(x) − x raise once to see the term.
        ownWork.lead = true;
        if (Number.isFinite(gap)) ownWork.kept = Math.max(ownWork.kept ?? Number.NEGATIVE_INFINITY, gap);
        void lostExp;
        work.set(n, ownWork);
        continue;
      }
    }

    if (n.type === "one") {
      memo.set(n, Z1);
      noteSeen(Z1);
      why.set(n, null);
      logged.set(n, false);
      cuts.set(n, 0);
      continue;
    }
    if (n.type === "input") {
      if (isMarkedExactInt(n)) {
        const big = provenInteger(n);
        if (big !== undefined) {
          const value = z(big.toString(), 0);
          memo.set(n, value);
          noteSeen(value);
          why.set(n, null);
          logged.set(n, false);
          continue;
        }
      }
      const leaf = z(n.value.re, n.value.im);
      memo.set(n, leaf);
      noteSeen(leaf);
      why.set(n, null);
      logged.set(n, false);
      cuts.set(n, 0);
      continue;
    }
    if (n.type === "var") {
      if (!Object.hasOwn(env, n.name)) {
        throw new EmlError(`This expression needs a value for ${n.name}.`);
      }
      const bound = env[n.name];
      if (!bound) throw new EmlError(`This expression needs a value for ${n.name}.`);
      const boundZ = asZ(bound);
      memo.set(n, boundZ);
      noteSeen(boundZ);
      why.set(n, null);
      logged.set(n, false);
      cuts.set(n, 0);
      continue;
    }
    if (!n.a || !n.b) throw new EmlError("Could not evaluate this circuit.");
    const hit = NOCACHE || cutTraceActive() ? undefined : cache.get(n);
    if (hit) {
      memo.set(n, hit.value);
      noteSeen(hit.value);
      // Replay what the skipped subtree told the pass (Finding 1: repeat compute → 0).
      if (hit.work.loss !== undefined && hit.work.loss > lossGap) lossGap = hit.work.loss;
      if (hit.work.sh !== undefined && hit.work.sh > shellLoss) shellLoss = hit.work.sh;
      if (hit.work.tiny !== undefined && hit.work.tiny < tiniest) tiniest = hit.work.tiny;
      if (hit.work.tinyIm !== undefined && hit.work.tinyIm < tiniestIm) tiniestIm = hit.work.tinyIm;
      if (hit.work.lead) sawLead = true;
      if (hit.work.cut) cutSeen = true;
      why.set(n, hit.why);
      logged.set(n, hit.logged);
      work.set(n, hit.work);
      cuts.set(n, hit.cutHits);
      continue;
    }

    if (!frame.seen) {
      if (visiting.has(n)) throw new EmlError("Could not evaluate this circuit.");
      visiting.add(n);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }

    visiting.delete(n);
    const a = memo.get(n.a);
    const b = memo.get(n.b);
    if (!a || !b) throw new EmlError("Could not evaluate this circuit.");
    const childLog = logged.get(n.a) === true || logged.get(n.b) === true || zZero(b);
    emlWork = Number.NEGATIVE_INFINITY;
    emlWorkRe = Number.NEGATIVE_INFINITY;
    emlWorkIm = Number.NEGATIVE_INFINITY;
    loggedCut = false;
    exactTraceNode = n;
    emlAbsorbGap = Number.NEGATIVE_INFINITY;
    emlAbsorbExp = Number.POSITIVE_INFINITY;
    nodeLoss = 0;
    nodeCut = false;
    const value = exactEml(a, b);
    exactTraceNode = null;
    const cutHits = (cuts.get(n.a) ?? 0) + (cuts.get(n.b) ?? 0) + (loggedCut ? 1 : 0);
    cuts.set(n, cutHits);
    const shell = inScaledShell(n);
    const ownShell = shell ? nodeLoss : 0;
    if (ownShell > shellLoss) shellLoss = ownShell;
    const own: Work = shell
      ? { all: Number.NEGATIVE_INFINITY, re: Number.NEGATIVE_INFINITY, im: Number.NEGATIVE_INFINITY }
      : { all: emlWork, re: emlWorkRe, im: emlWorkIm };
    // Sticky: an absorbed term anywhere below stays with every ancestor, shells included.
    own.ab = emlAbsorbGap;
    own.abE = emlAbsorbExp;
    const left = work.get(n.a);
    const right = work.get(n.b);
    const nodeWork: Work = {
      all: Math.max(own.all, left?.all ?? Number.NEGATIVE_INFINITY, right?.all ?? Number.NEGATIVE_INFINITY),
      ab: Math.max(own.ab ?? Number.NEGATIVE_INFINITY, left?.ab ?? Number.NEGATIVE_INFINITY, right?.ab ?? Number.NEGATIVE_INFINITY),
      abE: Math.min(own.abE ?? Number.POSITIVE_INFINITY, left?.abE ?? Number.POSITIVE_INFINITY, right?.abE ?? Number.POSITIVE_INFINITY),
      re: Math.max(own.re, left?.re ?? Number.NEGATIVE_INFINITY, right?.re ?? Number.NEGATIVE_INFINITY),
      im: Math.max(own.im, left?.im ?? Number.NEGATIVE_INFINITY, right?.im ?? Number.NEGATIVE_INFINITY),
      loss: Math.max(nodeLoss, left?.loss ?? 0, right?.loss ?? 0),
      sh: Math.max(ownShell, left?.sh ?? 0, right?.sh ?? 0),
      tiny: Math.min(partExp(value), left?.tiny ?? leafTiny(n.a), right?.tiny ?? leafTiny(n.b)),
      tinyIm: Math.min(imExp(value), left?.tinyIm ?? leafTinyIm(n.a), right?.tinyIm ?? leafTinyIm(n.b)),
      kept: Math.max(left?.kept ?? Number.NEGATIVE_INFINITY, right?.kept ?? Number.NEGATIVE_INFINITY),
      lead: isSeriesShortcut(n) || left?.lead === true || right?.lead === true,
      cut: nodeCut || left?.cut === true || right?.cut === true,
    };
    // A series shortcut drops its higher terms on purpose; its own note covers them.
    if (isSeriesShortcut(n)) {
      nodeWork.ab = Number.NEGATIVE_INFINITY;
      nodeWork.abE = Number.POSITIVE_INFINITY;
    }
    work.set(n, nodeWork);
    const nan = value.re.isNaN() || value.im.isNaN();
    let singular: string | null = null;
    if (nan) singular = SINGULAR_INDET;
    else if (!zFinite(value)) singular = childLog ? SINGULAR_LN0 : why.get(n.a) || why.get(n.b) || SINGULAR_NONFINITE;
    memo.set(n, value);
    noteSeen(value);
    why.set(n, singular);
    logged.set(n, childLog);
    const varA = n.a.type === "var" || hasVarOf.get(n.a) === true;
    const varB = n.b.type === "var" || hasVarOf.get(n.b) === true;
    hasVarOf.set(n, varA || varB);
    if (!varA && !varB) cache.set(n, { value, why: singular, logged: childLog, work: nodeWork, cutHits });
  }

  const out = memo.get(root);
  if (!out) throw new EmlError("Could not evaluate this circuit.");
  let singular = why.get(root) ?? null;
  // Finding 5: a cached subtree is not in memo, so look there too, or a repeat compute loses
  // "near a pole" / "argument too large to reduce".
  const flag = precisionMessage(root, (n) => {
    // A marked integer (tPow, review R4) is read without caching it, so a cached parent
    // skips it. Its integer is its value.
    const big = isMarkedExactInt(n) ? provenInteger(n) : undefined;
    const v = memo.get(n) ?? cache?.get(n)?.value ?? (big !== undefined ? z(big.toString(), 0) : n.type === "input" ? z(n.value.re, n.value.im) : n.type === "one" ? Z1 : undefined);
    return v ? exactToFloat(v) : undefined;
  });
  // A pole is a pole in both engines, including when the gates produced NaN.
  if (flag === SINGULAR_POLE) singular = flag;
  else if (!singular && flag) singular = flag;
  const rootWork = work.get(root);
  return {
    value: out,
    singular,
    touchedLn0: logged.get(root) === true,
    workExp: rootWork?.all,
    workRe: rootWork?.re,
    workIm: rootWork?.im,
    absorbedGap: rootWork?.ab,
    absorbedExp: rootWork?.abE,
    seriesKept: rootWork?.kept,
    digits: D.precision,
    sawLead,
    cutHits: cuts.get(root) ?? 0,
    cutSeen,
    tiniestExp: tiniest,
    tiniestImExp: tiniestIm,
  };
}

/** Re-evaluate at `digits` of precision, then restore the usual working precision. */
export function exactValueAt(root: Node, digits: number, env: Record<string, C | Z> = {}): Z {
  const saved = D.precision;
  D.set({ precision: digits });
  try {
    return exactEvaluate(root, env);
  } finally {
    D.set({ precision: saved });
  }
}

export function exactParts(re: Decimal.Value, im: Decimal.Value = 0): Z {
  return z(re, im);
}

export function exactEvaluate(
  root: Node,
  env: Record<string, C | Z> = {},
  budget: EvalBudget = {},
): Z {
  return exactReport(root, env, budget).value;
}

/** π, e, or the decimal of an integer or dyadic rational such as 1/2. */
function exactGoal(target: number): Decimal {
  if (target === Math.PI) return D.acos(-1);
  if (target === -Math.PI) return D.acos(-1).neg();
  if (target === Math.E) return D.exp(1);
  return new D(target);
}

/**
 * A zero part has to be exactly zero. A nonzero part has to match the
 * mathematical target to 240 digits, not the 15 digits of the float that
 * named it. The comparison uses the current working precision, so the caller
 * raises it before passing a wide value.
 */
export function constantAgrees(got: Decimal, target: number): boolean {
  if (target === 0) return got.isZero();
  const goal = exactGoal(target);
  const tol = new D(10).pow(-240);
  const scale = D.max(got.abs(), goal.abs(), 1);
  return got.sub(goal).abs().lte(scale.mul(tol));
}

/** Compare at 260 digits so a 240-digit tolerance is representable. */
export function valueMatchesTarget(value: Z, targetRe: number, targetIm: number): boolean {
  const saved = D.precision;
  D.set({ precision: Math.max(saved, 260) });
  try {
    return constantAgrees(value.re, targetRe) && constantAgrees(value.im, targetIm);
  } finally {
    D.set({ precision: saved });
  }
}

export function exactClose(got: Z, re: Decimal.Value, im: Decimal.Value = 0, digits = 12): boolean {
  const wantRe = new D(re);
  const wantIm = new D(im);
  const tol = new D(10).pow(-digits);
  const closePart = (a: Decimal, b: Decimal) => {
    if (a.isNaN() || b.isNaN()) return a.isNaN() && b.isNaN();
    if (!a.isFinite() || !b.isFinite()) return a.eq(b);
    const scale = D.max(a.abs(), b.abs(), 1);
    return a.sub(b).abs().lte(scale.mul(tol));
  };
  return closePart(got.re, wantRe) && closePart(got.im, wantIm);
}

/** A float view of an exact value, for the stack and the recognizer. */
export function exactToFloat(v: Z): C {
  const re = v.re.isFinite() ? v.re.toNumber() : v.re.isNaN() ? NaN : v.re.isNeg() ? -Infinity : Infinity;
  const im = v.im.isFinite() ? v.im.toNumber() : v.im.isNaN() ? NaN : v.im.isNeg() ? -Infinity : Infinity;
  return { re, im };
}

/** A non-zero exact component that float64 turns into 0. cos(10^(−200)) − 1 is one. */
export function exactUnderflowsFloat(v: Z): boolean {
  const n = exactToFloat(v);
  const lost = (part: Decimal, num: number) => part.isFinite() && !part.isZero() && num === 0;
  return lost(v.re, n.re) || lost(v.im, n.im);
}

function formatDec(d: Decimal): string {
  if (d.isNaN()) return "undefined";
  if (!d.isFinite()) return d.isNeg() ? "−∞" : "∞";
  if (d.isZero()) return d.isNeg() ? "−0" : "0";
  const sign = d.isNeg() ? "−" : "";
  const abs = d.abs();
  if (abs.lt("1e16") && exactInteger(abs)) return sign + abs.toFixed(0);
  if (abs.lt("1e16") && abs.gte(FIXED_FLOOR)) {
    // v1.1: twelve significant digits, as float mode prints, not twelve decimal places.
    // 0.0000499999999792 kept 8 digits as 0.00005; 1e-8/7 kept 4.
    const sig = Math.max(0, SHOWN_DIGITS - 1 - abs.e);
    const shown = new D(abs.toFixed(sig));
    const gap = abs.sub(shown).abs();
    const intGap = abs.sub(abs.round()).abs();
    const dust = new D(10).pow(-(D.precision - 24));
    // Twelve digits hide 0.5 − 10^(−72) and 1 − 10^(−72). Print the first digits of that tail.
    const hiddenTail = gap.gt(dust) && gap.e < abs.e - (SHOWN_DIGITS + 2);
    const hiddenInt = intGap.gt(dust) && intGap.e < -9;
    if (hiddenTail || hiddenInt) {
      const reveal = hiddenTail && (!hiddenInt || gap.e <= intGap.e) ? gap : intGap;
      const places = Math.min(D.precision - 8, Math.max(sig, -reveal.e + 2));
      return sign + abs.toFixed(places).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    }
    const text = abs.toFixed(sig).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    return sign + text;
  }
  const exp = abs.toExponential(SHOWN_DIGITS - 1).replace(/\.?0+e/, "e").replace("e+", "×10^").replace("e-", "×10^−");
  return sign + exp;
}

function formatDecImag(d: Decimal): string {
  if (d.isNaN()) return "undefined";
  if (!d.isFinite()) return d.isNeg() ? "−∞i" : "∞i";
  const sign = d.isNeg() ? "−" : "";
  if (d.abs().sub(1).abs().lte("1e-12")) return `${sign}i`;
  return `${sign}${formatDec(d.abs())}i`;
}

function formatFullInteger(d: Decimal): string {
  const sign = d.isNeg() ? "−" : "";
  const saved = D.precision;
  const need = Math.max(saved, d.abs().e + 2);
  if (need > saved) D.set({ precision: need });
  try {
    const digits = d.abs().toFixed(0);
    return sign + digits.replace(/(.{20})(?=.)/g, "$1\u200b");
  } finally {
    if (need > saved) D.set({ precision: saved });
  }
}

/**
 * Print as an integer only when the decimal is exactly that integer.
 * A relative neighbourhood of 10^(−30) turned 1 − 10^(−72) into 1.
 * 10^400/7 equals its own round() at low precision and must not: its
 * exponent is past the working precision, so it stays in scientific form.
 */
function exactInteger(d: Decimal): boolean {
  if (!d.isFinite() || d.isZero() || d.abs().lt(0.5)) return false;
  // A marked integer can be wider than the working precision and still hold its units digit.
  if (d.abs().e >= D.precision) return d.sd() > d.abs().e && d.isInt();
  const gap = d.sub(d.round()).abs();
  if (gap.eq(0)) return true;
  // The last 24 digits of a 120-digit run are construction dust.
  // 1 − 10^(−72) and 1 − 10^(−80) sit well above that and stay visible.
  const scale = D.max(d.abs(), 1);
  return gap.lte(scale.mul(new D(10).pow(-(D.precision - 24))));
}

/**
 * True when the float evaluation and the exact evaluation of the same circuit
 * disagree by more than the screen can hide. Twelve digits are shown, so a
 * relative error of 10^(−11) on either component is flagged, and 10^(−12) is not.
 * The components are compared separately: exp(10^(−9)i) − 1 and 10^300 + i drop
 * one component, and that drop is a disagreement even when the other component
 * is huge. A few ulps of a moderate result still agree. Signed zeros agree.
 */
export function beyondFloatBound(got: C, exact: C): boolean {
  const part = (left: number, right: number): boolean => {
    if (!Number.isFinite(left) || !Number.isFinite(right)) return !Object.is(left, right);
    if (Object.is(left, right)) return false;
    // −0 and 0 are the same component. A float 0 against a nonzero exact
    // component is a drop (exp(10^(−9)i) − 1, 10^300 + i). A float-only
    // component is dust when it sits below the digits on screen.
    if (left === 0 && right === 0) return false;
    if (left === 0) return true;
    // v1.1: the same cut tidy() uses, so a component the screen prints is a component the flag sees.
    if (right === 0) return floatShowsComponent(left, Math.hypot(got.re, got.im));
    const mag = Math.max(Math.abs(left), Math.abs(right));
    return Math.abs(left - right) > 5e-12 * mag;
  };
  return part(got.re, exact.re) || part(got.im, exact.im);
}

/** Display an exact value. Each component is printed on its own; float tidy is not applied. */
export function formatExact(v: Z): string {
  if (v.re.isZero() && v.im.isZero()) return v.re.isNeg() || v.im.isNeg() ? "−0" : "0";
  if (v.im.isZero() && exactInteger(v.re)) return formatFullInteger(v.re.round());
  if (v.re.isNaN() || v.im.isNaN()) return "undefined";
  if (v.re.isZero() && v.im.isZero()) return "0";
  if (v.im.isZero()) return formatDec(v.re);
  if (v.re.isZero()) return formatDecImag(v.im);
  const joiner = v.im.isNeg() ? " − " : " + ";
  return `${formatDec(v.re)}${joiner}${formatDecImag(v.im.abs())}`;
}
