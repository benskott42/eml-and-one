import Decimal from "decimal.js";
import type { C } from "./complex";
import {
  EmlError,
  EmlLimitError,
  SINGULAR_INDET,
  SINGULAR_LN0,
  SINGULAR_NONFINITE,
  SINGULAR_POLE,
  type EvalBudget,
  type Node,
  isUnverified,
  precisionMessage,
  provenInteger,
  trigArg,
} from "./node";
import { decadeOf, inScaledShell, isLiftedCombine, isLostTiny, isMarkedExactInt, knownValue } from "./lowering";
import { isSeriesShortcut } from "./node";

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
 * cos and sin. An angle within the working tolerance of a nonzero multiple of
 * π/2 is that axis, so exp(iπ) is −1 and the composed logarithm takes the upper
 * bank. π − 10^(−12) is far outside this tolerance. A tiny angle near 0 is not
 * snapped: sin(6×10^(−120)) is that angle, not 0. An axis snap is not recorded
 * as a cancellation: π itself carries a 10^(−precision) offset, so exp(iπ) + 1
 * would retry to the cap and never certify its 0.
 */
function cosSin(theta: Decimal): { c: Decimal; s: Decimal } {
  const pi = D.acos(-1);
  const half = pi.div(2);
  const steps = theta.div(half).toNearest(1);
  const offset = theta.sub(steps.mul(half));
  if (!steps.isZero() && offset.abs().lte(tol())) {
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
  if (mag.isZero()) return { re: signedZeroFrom(trig.c), im: signedZeroFrom(trig.s) };
  if (!mag.isFinite()) return { re: signedInf(trig.c), im: signedInf(trig.s) };
  return { re: mag.mul(trig.c), im: mag.mul(trig.s) };
}

/**
 * Lower bank, exact cut only. Imaginary dust is a real point off the axis:
 * −2 + 10^(−300)i is not rewritten as −2.
 */
function lnEml(v: Z): Z {
  // Log(NaN) is NaN. A non-finite test is true for NaN and must not turn it into +∞.
  if (v.re.isNaN() || v.im.isNaN()) return { re: NAN, im: NAN };
  const negPi = D.acos(-1).neg();
  if (v.re.isZero() && v.im.isZero()) {
    if (v.re.isNeg()) return { re: NEG_INF, im: negPi };
    return { re: NEG_INF, im: v.im.isNeg() ? new D(-0) : ZERO };
  }
  const mag = D.hypot(v.re, v.im);
  if (mag.isZero()) return { re: NEG_INF, im: v.re.isNeg() ? negPi : ZERO };
  const onCut = v.im.isZero() && v.re.isNeg();
  let arg = onCut ? negPi : (atan2Fast(v.im, v.re) ?? D.atan2(v.im, v.re));
  if (!onCut && !v.im.isZero() && (arg.eq(negPi) || arg.eq(negPi.neg()))) {
    const gap = v.re.e - v.im.e;
    if (Number.isFinite(gap) && gap > 8 && gap < 2000) {
      const local = D.clone({ precision: D.precision + gap + 8 });
      arg = new D(local.atan2(new local(v.im.toString()), new local(v.re.toString())).toString());
    }
  }
  if (!mag.isFinite()) return { re: POS_INF, im: arg.isFinite() ? arg : ZERO };
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
/** Most negative exponent of a nonzero finite value computed in this pass. */
let tiniest = 0;

/** Smallest exponent of a nonzero finite component, or 0, the same floor `tiniest` starts from. */
function exponentFloor(v: Z): number {
  let low = 0;
  for (const part of [v.re, v.im]) if (part.isFinite() && !part.isZero() && part.e < low) low = part.e;
  return low;
}

function noteSeen(v: Z): void {
  const take = (part: Decimal) => {
    if (part.isFinite() && !part.isZero() && part.e < tiniest) tiniest = part.e;
  };
  take(v.re);
  take(v.im);
}
/**
 * Size of the terms that cancelled by at least two decades in the last
 * exactEml call (decimal exponent). Rounding there leaves absolute noise near
 * 10^(size − precision). A gate that does not cancel keeps its relative
 * accuracy, so its size is not counted.
 * A 10^k lift is left out of this only after the cancelled terms reach 1.
 * A shorter lift stays in: that cancellation is the result's rounding.
 */
let emlWork = Number.NEGATIVE_INFINITY;
let emlWorkRe = Number.NEGATIVE_INFINITY;
let emlWorkIm = Number.NEGATIVE_INFINITY;
/** Working precision is never raised past this. A value that still needs more is not certified. */
const PRECISION_CAP = 480;

/** One subtraction's cancelled terms and the residual they left. */
type CancelHit = { part: "re" | "im"; scale: number; diff: number };
/** Hits recorded while the gate under evaluation runs. */
let gateHits: CancelHit[] = [];

/** True when a lift's cancelled terms are still below 1, so the cancellation counts. */
function shortLift(scale: number): boolean {
  return Number.isFinite(scale) && scale < 0;
}

/**
 * A lift that reached 1 can still be the result. e/e cancels up there and
 * leaves a residual far below those terms. An ordinary sum does not.
 */
function liftedResidue(scale: number, hits: CancelHit[], value: Z): boolean {
  if (!Number.isFinite(scale) || scale < 0) return false;
  const produced = (part: "re" | "im", out: Decimal) =>
    out.isFinite() &&
    !out.isZero() &&
    hits.some((h) => h.part === part && Math.abs(h.diff - out.e) <= 4 && h.scale - out.e >= 8);
  return produced("re", value.re) || produced("im", value.im);
}

function noteWork(left: Decimal, right: Decimal, diff: Decimal, part: "re" | "im"): void {
  const scale = D.max(left.abs(), right.abs());
  if (!scale.isFinite() || scale.isZero()) return;
  if (!(diff.isZero() || scale.e - diff.abs().e >= 2)) return;
  if (!diff.isZero()) gateHits.push({ part, scale: scale.e, diff: diff.abs().e });
  emlWork = Math.max(emlWork, scale.e);
  if (part === "re") emlWorkRe = Math.max(emlWorkRe, scale.e);
  else emlWorkIm = Math.max(emlWorkIm, scale.e);
}

function noteLoss(scale: Decimal, residual: Decimal): void {
  if (!scale.isFinite() || scale.isZero() || !residual.isFinite() || residual.isZero()) return;
  const gap = scale.e - residual.abs().e;
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
function scrubDust(v: Z): Z {
  if (!v.re.isFinite() || !v.im.isFinite()) return v;
  const scale = D.max(v.re.abs(), v.im.abs());
  if (!scale.isFinite() || scale.isZero()) return v;
  const floor = scale.mul(new D(10).pow(-(D.precision - 12)));
  const buried = scale.mul(new D(10).pow(-160));
  const limit = D.max(floor, buried);
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
  const re = cancelled(a.re.sub(b.re), a.re, b.re, "re");
  const im = cancelled(a.im.sub(b.im), a.im, b.im, "im");
  if (re.isNaN() || im.isNaN()) return { re: NAN, im: NAN };
  return { re, im };
}

/**
 * What one gate's extended-value rule cannot carry forward. The infinity rules
 * are limits taken one gate at a time, and two of them drop a finite part:
 * - exp(−∞ + iθ) is a zero that keeps only the signs of cos θ and sin θ. A later
 *   ln reads that zero as −∞ or −∞ − iπ, so θ off the real axis is lost. That only
 *   matters when the gate's output is this zero.
 * - exp(+∞ + iθ) off an axis is ±∞ ± ∞i, which is no direction.
 * - ln of an infinity beside a finite nonzero part keeps only the limit angle, so
 *   ln(∞ + iπ) is ∞ and the iπ is gone: (∞ + iπ)·i came out a real ∞, not −π + i∞.
 * An infinity whose partner is exactly 0 loses nothing. The loss travels with
 * the value while it stays 0 or infinite (see carriesLoss); a result that still
 * carries it is not certified.
 */
function gateLosesPart(x: Z, y: Z, out: Z): boolean {
  if (x.re.isNaN() || x.im.isNaN() || y.re.isNaN() || y.im.isNaN()) return false;
  if (!x.re.isFinite() && x.im.isFinite()) {
    const trig = cosSin(x.im);
    if (x.re.isNeg()) {
      if (!trig.s.isZero() && zZero(out)) return true;
    } else if (!axisInfinity(trig.c).isZero() && !axisInfinity(trig.s).isZero()) return true;
  }
  const reInf = !y.re.isFinite();
  const imInf = !y.im.isFinite();
  if (reInf && imInf) return true;
  if (reInf && !y.im.isZero()) return true;
  if (imInf && !y.re.isZero()) return true;
  return false;
}

/**
 * The gate between a 10^k lift and its drop: decades its add or sub cancelled.
 * The lift gates are not in the work tally, so this is the only record of it.
 */
function liftedGap(x: Z, y: Z, out: Z): number {
  const a = expZ(x);
  const b = lnEml(y);
  let gap = 0;
  for (const part of ["re", "im"] as const) {
    const scale = D.max(a[part].abs(), b[part].abs());
    const diff = out[part];
    if (!scale.isFinite() || scale.isZero() || !diff.isFinite() || diff.isZero()) continue;
    gap = Math.max(gap, scale.e - diff.abs().e);
  }
  return gap;
}

/**
 * `lost`: this node's value carries a dropped part. `inherited`: it came from an
 * operand, not from this gate's own zero. `liftGap`: this gate's lifted cancellation.
 */
type GateRisk = { lost: boolean; inherited: boolean; liftGap: number };

/**
 * A dropped part matters only while the value is 0 or infinite: a later ln reads
 * its angle. exp(−∞ + iθ) is 0 for every θ, so a finite nonzero result no longer
 * depends on the lost part, and the routine 4i + 0.5i words that pass through
 * exp(−∞ ± iπ/2) stay certified.
 */
function carriesLoss(own: boolean, a: GateRisk | undefined, b: GateRisk | undefined, out: Z): Pick<GateRisk, "lost" | "inherited"> {
  const none = { lost: false, inherited: false };
  if (out.re.isNaN() || out.im.isNaN() || !(zZero(out) || !zFinite(out))) return none;
  const inherited = a?.lost === true || b?.lost === true;
  return own || inherited ? { lost: true, inherited } : none;
}

/** Pure gates' risk by working precision, for subtrees a cache hit skips. */
const riskCache = new Map<number, WeakMap<Node, GateRisk>>();

function gateRiskStore(): WeakMap<Node, GateRisk> {
  let store = riskCache.get(D.precision);
  if (!store) {
    store = new WeakMap();
    riskCache.set(D.precision, store);
  }
  return store;
}

/** Whether the root carries a lost part, and the largest lifted cancellation under it. */
function riskBelow(root: Node, out: Z, pass: Map<Node, GateRisk>): GateRisk {
  const store = gateRiskStore();
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  // A root zero whose own exp(−∞ + iθ) dropped θ is still 0: no later ln reads that angle.
  const top = riskOf(root, pass, store);
  const rootLost = top !== undefined && top.lost && (top.inherited || !zZero(out));
  const total: GateRisk = { lost: rootLost, inherited: false, liftGap: 0 };
  while (stack.length) {
    const node = stack.pop();
    if (!node || node.type !== "eml" || seen.has(node)) continue;
    seen.add(node);
    const risk = riskOf(node, pass, store);
    if (risk) total.liftGap = Math.max(total.liftGap, risk.liftGap);
    stack.push(node.a, node.b);
  }
  return total;
}

function riskOf(node: Node, pass: Map<Node, GateRisk>, store: WeakMap<Node, GateRisk>): GateRisk | undefined {
  return pass.get(node) ?? (hasVarOf.get(node) === false ? store.get(node) : undefined);
}

/** A lost part refuses any value but undefined. */
function riskReport(out: Z, below: GateRisk): Pick<ExactReport, "unverified" | "liftGap"> {
  const lost = below.lost && !out.re.isNaN() && !out.im.isNaN();
  return lost ? { unverified: true, liftGap: below.liftGap } : { liftGap: below.liftGap };
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
  /** Largest cancelling term size. A full-size lift is left out; a short lift is not. */
  workExp?: number;
  /** Per-component cancellation size. A part with no finite work was not a residue. */
  workRe?: number;
  workIm?: number;
  /**
   * Decade of the terms whose cancellation produced this component.
   * Set only when that residual is the component itself.
   */
  prodRe?: number;
  prodIm?: number;
  /** Precision the value was computed at. */
  digits?: number;
  /** A series shortcut was used. A zero from that shortcut is not certified. */
  sawLead?: boolean;
  /** Decades cancelled between a 10^k lift and its drop. */
  liftGap?: number;
};

type Work = { all: number; re: number; im: number; hits: CancelHit[] };

function mergeHits(left: CancelHit[] | undefined, right: CancelHit[] | undefined, own: CancelHit[]): CancelHit[] {
  const a = left ?? [];
  const b = right ?? [];
  if (a.length === 0 && b.length === 0) return own;
  if (b.length === 0 && own.length === 0) return a;
  if (a.length === 0 && own.length === 0) return b;
  if (a === b && own.length === 0) return a;
  // A shared subtree reaches a node through both children. Concatenating copied its
  // hits once per path, which doubles per level of sharing. Each hit is one object,
  // and both readers (liftedResidue, componentProd) ignore repeats, so keep one copy.
  const merged = new Set(a);
  for (const hit of b) merged.add(hit);
  for (const hit of own) merged.add(hit);
  return [...merged];
}

/** Scale of the cancellation whose residual is this component, when one is that close. */
function componentProd(part: "re" | "im", value: Decimal, hits: CancelHit[]): number | undefined {
  if (!value.isFinite() || value.isZero()) return undefined;
  let best: number | undefined;
  let dist = 5;
  for (const hit of hits) {
    if (hit.part !== part) continue;
    const gap = Math.abs(hit.diff - value.e);
    if (gap < dist) {
      dist = gap;
      best = hit.scale;
    }
  }
  return best;
}
/** `loss`, `tiniest` and `lead` are the subtree's share of the pass state, restored on a hit. */
type Cached = { value: Z; why: string | null; logged: boolean; work: Work; loss: number; tiniest: number; lead: boolean };
/** Var-free subcircuits, by working precision. A rebuilt circuit is new nodes, so it misses this map. */
const pureCache = new Map<number, WeakMap<Node, Cached>>();
const hasVarOf = new WeakMap<Node, boolean>();
/** EML_NOCACHE=1 skips the cache. Read per pass, so a test can toggle it at runtime. */
function cacheOff(): boolean {
  return typeof process !== "undefined" && process.env?.EML_NOCACHE === "1";
}

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

/** True when a past-cap power, or a sum of two underflows, is still in the tree. */
function lostTinyIn(root: Node): boolean {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    if (isLostTiny(node)) return true;
    if (node.type === "eml") {
      stack.push(node.a, node.b);
    }
  }
  return false;
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

function atPrecision(digits: number, root: Node, env: Record<string, C | Z>, budget: EvalBudget, scrub = true): ExactReport {
  const saved = D.precision;
  D.set({ precision: digits });
  try {
    const report = exactReport(root, env, budget, scrub ? 2 : 3);
    if (digits <= saved) return report;
    // The retry can carry hundreds of extra digits. The suite compares the
    // working-precision value, so round back once the hidden component is recovered.
    D.set({ precision: saved });
    const round = (part: Decimal) => (part.isFinite() ? new D(part.toSignificantDigits(saved).toString()) : part);
    const value = { re: round(report.value.re), im: round(report.value.im) };
    return { ...report, digits, value: scrub ? scrubDust(value) : value };
  } finally {
    D.set({ precision: saved });
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

function present(report: ExactReport): ExactReport {
  return { ...report, value: scrubDust(report.value) };
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
  try {
    again = atPrecision((report.digits ?? D.precision) + 24, root, env, budget).value[which];
  } catch {
    return report;
  }
  if (again.isFinite() && part.sub(again).abs().lte(part.abs().mul("1e-6"))) return report;
  const cleared = part.isNeg() ? new D(-0) : ZERO;
  return { ...report, value: which === "re" ? { re: cleared, im: report.value.im } : { re: report.value.re, im: cleared } };
}

/**
 * One component 0 (or scrubbed) beside a nonzero one, with a known leaf below the
 * working precision: 10^(−130) + i/2 rounds the real part away inside the gates.
 * Evaluate where that leaf fits, twice, and keep a part that holds still. The
 * scrub would clear it again (it is more than 108 decades below its sibling),
 * so neither pass is scrubbed. A part that moves is dust and the scrubbed value
 * stands; so does a leaf past 480 digits.
 */
function recoverTinyPart(report: ExactReport, root: Node, env: Record<string, C | Z>, budget: EvalBudget): ExactReport | null {
  // A part the scrub would clear counts as 0 here: exp(6×10^(−120) i) computes the
  // imaginary part, then the scrub drops it beside the 1.
  const v = scrubDust(report.value);
  if (!v.re.isFinite() || !v.im.isFinite() || v.re.isZero() === v.im.isZero()) return null;
  const which: "re" | "im" = v.re.isZero() ? "re" : "im";
  const digits = report.digits ?? D.precision;
  const hinted = demandedTinyDigits(root, env);
  if (hinted <= digits) return null;
  if (hinted > PRECISION_CAP) return null;
  let first: ExactReport;
  let second: ExactReport;
  try {
    first = atPrecision(hinted, root, env, budget, false);
    if (first.unverified || first.value[which].isZero()) return null;
    second = atPrecision(Math.min(PRECISION_CAP, hinted + 24), root, env, budget, false);
  } catch {
    return null;
  }
  // A part under the noise of the terms that cancelled at that precision is a
  // rounding residue even when it holds still: sin(−10^(−400)) leaves ~10^(−801) i.
  const work = which === "re" ? first.workRe : first.workIm;
  if (work !== undefined && Number.isFinite(work) && first.value[which].abs().lt(residueFloor(work, first.digits ?? hinted))) return null;
  // A part that moves with the precision is dust, and the scrubbed value stands.
  if (second.unverified || residueMoved(first.value[which], second.value[which])) return null;
  return first;
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
 * The floor is the cancelled operands' decade on the first pass (digits − 12).
 * A residue that sits below that floor is rounding, including one that holds
 * still across a short step and then keeps falling. A real difference that
 * settles above the floor is kept. exp(ln(10^(−400))) − 10^(−400) falls
 * through the floor. 10^(−400)·(1 + 10^(−100)) − 10^(−400) stops above it.
 */
function settleResidue(
  report: ExactReport,
  root: Node,
  env: Record<string, C | Z>,
  budget: EvalBudget,
): ExactReport {
  let current = report;
  const threshold = (report.digits ?? D.precision) - 12;
  const prodGap = (r: ExactReport, name: "re" | "im"): number | undefined => {
    const part = r.value[name];
    const scale = name === "re" ? r.prodRe : r.prodIm;
    if (!part.isFinite() || part.isZero() || scale === undefined || !Number.isFinite(scale)) return undefined;
    return scale - part.e;
  };
  // A stuck rounding plateau holds until precision passes the residual's
  // exponent by the first-pass margin. A real difference is still there then.
  const confirmAt = (r: ExactReport): number => {
    let past = 0;
    for (const name of ["re", "im"] as const) {
      const part = r.value[name];
      if (prodGap(r, name) === undefined) continue;
      past = Math.max(past, -part.e + threshold);
    }
    return past;
  };
  // Below the floor, and this reading is not yet past the residual's exponent.
  const unproven = (earlier: ExactReport, later: ExactReport): boolean => {
    const digits = later.digits ?? D.precision;
    return (["re", "im"] as const).some((name) => {
      const part = later.value[name];
      if (!part.isFinite() || part.isZero()) return false;
      const gap = prodGap(later, name) ?? prodGap(earlier, name);
      if (gap === undefined || gap <= threshold) return false;
      return digits < -part.e + threshold;
    });
  };

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
    let next = Math.min(PRECISION_CAP, Math.max(digits + step, raised));
    const past = confirmAt(current);
    if (past > next) next = Math.min(PRECISION_CAP, past);
    if (next <= digits) return certifyZero(current);
    let again: ExactReport;
    try {
      again = atPrecision(next, root, env, budget);
    } catch {
      return certifyZero(current);
    }
    const changed = which.some((name) => residueMoved(current.value[name], again.value[name]));
    if (!changed) {
      if (unproven(current, again)) {
        if (next >= PRECISION_CAP) return certifyZero(again);
        current = again;
        continue;
      }
      if (confirmAt(again) > (again.digits ?? next) && (again.digits ?? next) < PRECISION_CAP) {
        current = again;
        continue;
      }
      return current;
    }
    current = again;
  }
  return unproven(current, current) || residueParts(current).length > 0 ? certifyZero(current) : current;
}

/**
 * A huge integer kept beside a non-integer is a mul by a leaf labelled `beside:`.
 * That mul is not the sum: exact evaluation would certify the bare integer.
 * The leaf sits next to the root, so this does not walk the power.
 */
function hidesBeside(root: Node): boolean {
  const stack: { n: Node; depth: number }[] = [{ n: root, depth: 0 }];
  let steps = 0;
  while (stack.length && steps < 64) {
    const frame = stack.pop();
    if (!frame) break;
    steps += 1;
    const node = frame.n;
    if (node.type === "input") {
      if (node.label.startsWith("beside:")) return true;
      continue;
    }
    if (node.type === "eml" && frame.depth < 8) {
      stack.push({ n: node.a, depth: frame.depth + 1 }, { n: node.b, depth: frame.depth + 1 });
    }
  }
  return false;
}

export function exactReport(
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
  if (isUnverified(root) || hidesBeside(root)) {
    return { value: { re: NAN, im: NAN }, singular: null, touchedLn0: false, unverified: true };
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
        return { value: z(text, 0), singular: null, touchedLn0: false };
      } finally {
        if (width > saved) D.set({ precision: saved });
      }
    }
  }
  lossGap = 0;
  const report = exactReportOnce(root, env, budget);
  // Pass 3 is a raised pass whose caller judges a tiny part itself, so it is not scrubbed.
  if (pass !== 0) return pass === 3 ? report : present(report);
  if (vanished(report.value)) {
    if (report.sawLead) return certifyZero(report);
    // 0 − 10^(−500) and ln(1 − 10^(−500)) have no decade to recover. The zero
    // is the cap, not a proof. A direct −10^(−500) is not zero and stays.
    if (lostTinyIn(root)) return certifyZero(report);
    const gap = lossGap;
    // Any recorded cancellation can hide the term that should have survived.
    // A structural zero such as 1−1 records no gap and stays certified.
    const fromGap = gap > 8 ? gap + 48 : 0;
    const need = Math.max(demandedTinyDigits(root, env), fromGap);
    if (need > PRECISION_CAP) return certifyZero(report);
    if (need > D.precision) {
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
      // A nonzero that shows up under the cancelled terms is still rounding
      // until a second reading shows it stayed near the magnitude already seen.
      const nonzeroResidue = residueParts(again).some((name) => !again.value[name].isZero());
      const revealed = nonzeroResidue ? settleResidue(again, root, env, budget) : again;
      if (revealed.unverified) return revealed;
      return confirmDust(present(revealed), root, env, budget);
    }
  }
  let settled = report;
  if (hiddenComponent(report.value)) {
    const digits = Math.min(PRECISION_CAP, Math.max(Math.max(report.value.re.e, report.value.im.e) + 48, D.precision + 32));
    if (digits > D.precision) settled = atPrecision(digits, root, env, budget);
  }
  if (settled.unverified) return settled;
  // A lifted tiny sum keeps (precision − gap) digits, and the work tally does not see it:
  // 10^(−300)·(1 + 10^(−110)) − 10^(−300) kept 10 digits. Raise until 24 spare digits remain.
  const liftGap = settled.liftGap ?? 0;
  if (liftGap > (settled.digits ?? D.precision) - 24) {
    const need = liftGap + 48;
    if (need > PRECISION_CAP) return certifyZero(settled);
    settled = atPrecision(need, root, env, budget);
    if (settled.unverified) return settled;
  }
  settled = settleResidue(settled, root, env, budget);
  if (settled.unverified) return settled;
  const besideTiny = recoverTinyPart(settled, root, env, budget);
  if (besideTiny) return besideTiny;
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
  return confirmDust(present(settled), root, env, budget);
}

/** The imaginary part of an exp argument below the noise floor of the cancellation that made it. */
function angleNoise(v: Z, made: Work | undefined): boolean {
  if (!made || !Number.isFinite(made.im) || !v.im.isFinite() || v.im.isZero()) return false;
  return v.im.abs().lt(residueFloor(made.im, D.precision));
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
  // Per subtree: largest cancellation, smallest exponent seen, and a series shortcut below.
  const lossOf = new Map<Node, number>();
  const tinyOf = new Map<Node, number>();
  const leadOf = new Map<Node, boolean>();
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  let sawLead = false;
  tiniest = 0;
  const risk = new Map<Node, GateRisk>();
  let steps = 0;
  const nocache = cacheOff();
  let cache = pureCache.get(D.precision);
  if (!cache) {
    cache = new WeakMap();
    pureCache.set(D.precision, cache);
  }

  while (stack.length) {
    if ((++steps & 31) === 0) {
      if (steps > maxNodes) throw new EmlLimitError("This circuit is too large for exact mode.");
      if (deadline && performance.now() > deadline) throw new EmlLimitError("Exact evaluation timed out.");
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

    if (n.type === "one") {
      memo.set(n, Z1);
      noteSeen(Z1);
      why.set(n, null);
      logged.set(n, false);
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
      continue;
    }
    if (!n.a || !n.b) throw new EmlError("Could not evaluate this circuit.");
    // A sin, cos, or tan node can be an intermediate of another function and
    // already be cached. The cache entry is the exp formula. Recompute so an
    // infinite argument stays undefined instead of that cached infinity.
    const angle = trigArg(n);
    const hit = nocache || angle ? undefined : cache.get(n);
    if (hit) {
      memo.set(n, hit.value);
      noteSeen(hit.value);
      why.set(n, hit.why);
      logged.set(n, hit.logged);
      work.set(n, hit.work);
      // exactEml did not run below this node, so take its recorded share of the pass state.
      if (hit.loss > lossGap) lossGap = hit.loss;
      if (hit.tiniest < tiniest) tiniest = hit.tiniest;
      if (hit.lead) sawLead = true;
      lossOf.set(n, hit.loss);
      tinyOf.set(n, hit.tiniest);
      leadOf.set(n, hit.lead);
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
    gateHits = [];
    // sin, cos, and tan of ±∞ are undefined. The note travels with the packed circuit.
    // The exp formula otherwise returns an infinity.
    // The argument may sit under a cached intermediate, so this walk never
    // visits it. The earlier evaluation stored it in the pure cache.
    const angleValue = angle ? (memo.get(angle) ?? cache.get(angle)?.value) : undefined;
    const angleInfinite = !!angleValue && (!angleValue.re.isFinite() || !angleValue.im.isFinite());
    const outerLoss = lossGap;
    lossGap = 0;
    // An angle under the rounding noise of the gates that produced it is that
    // noise, and turns as 0 (cosSin no longer snaps a tiny angle to the axis).
    const turn = angleNoise(a, work.get(n.a)) ? { re: a.re, im: ZERO } : a;
    const value = angleInfinite ? { re: NAN, im: NAN } : exactEml(turn, b);
    const ownLoss = lossGap;
    lossGap = Math.max(outerLoss, ownLoss);
    const subLoss = Math.max(ownLoss, lossOf.get(n.a) ?? 0, lossOf.get(n.b) ?? 0);
    const subTiny = Math.min(exponentFloor(value), tinyOf.get(n.a) ?? exponentFloor(a), tinyOf.get(n.b) ?? exponentFloor(b));
    const subLead = isSeriesShortcut(n) || leadOf.get(n.a) === true || leadOf.get(n.b) === true;
    lossOf.set(n, subLoss);
    tinyOf.set(n, subTiny);
    leadOf.set(n, subLead);
    const ownHits = gateHits;
    const shell = inScaledShell(n);
    // A short lift never reaches 1, so its cancellation is the result's rounding.
    // e/e does reach 1 and still leaves that residual; an ordinary sum does not.
    const liftCounts = !shell || shortLift(emlWork) || liftedResidue(emlWork, ownHits, value);
    const own: Work = liftCounts
      ? { all: emlWork, re: emlWorkRe, im: emlWorkIm, hits: ownHits }
      : { all: Number.NEGATIVE_INFINITY, re: Number.NEGATIVE_INFINITY, im: Number.NEGATIVE_INFINITY, hits: ownHits };
    const left = work.get(n.a);
    const right = work.get(n.b);
    const nodeWork: Work = {
      all: Math.max(own.all, left?.all ?? Number.NEGATIVE_INFINITY, right?.all ?? Number.NEGATIVE_INFINITY),
      re: Math.max(own.re, left?.re ?? Number.NEGATIVE_INFINITY, right?.re ?? Number.NEGATIVE_INFINITY),
      im: Math.max(own.im, left?.im ?? Number.NEGATIVE_INFINITY, right?.im ?? Number.NEGATIVE_INFINITY),
      hits: mergeHits(left?.hits, right?.hits, own.hits),
    };
    work.set(n, nodeWork);
    const nan = value.re.isNaN() || value.im.isNaN();
    let singular: string | null = null;
    if (nan) singular = SINGULAR_INDET;
    else if (!zFinite(value)) singular = childLog ? SINGULAR_LN0 : why.get(n.a) || why.get(n.b) || SINGULAR_NONFINITE;
    memo.set(n, value);
    noteSeen(value);
    why.set(n, singular);
    logged.set(n, childLog);
    const store = gateRiskStore();
    const gate: GateRisk = {
      ...carriesLoss(!angleInfinite && gateLosesPart(a, b, value), riskOf(n.a, risk, store), riskOf(n.b, risk, store), value),
      liftGap: isLiftedCombine(n) && !angleInfinite ? liftedGap(a, b, value) : 0,
    };
    risk.set(n, gate);
    if (!(n.a.type === "var" || hasVarOf.get(n.a) === true || n.b.type === "var" || hasVarOf.get(n.b) === true)) store.set(n, gate);
    const varA = n.a.type === "var" || hasVarOf.get(n.a) === true;
    const varB = n.b.type === "var" || hasVarOf.get(n.b) === true;
    hasVarOf.set(n, varA || varB);
    if (!varA && !varB) cache.set(n, { value, why: singular, logged: childLog, work: nodeWork, loss: subLoss, tiniest: subTiny, lead: subLead });
  }

  const out = memo.get(root);
  if (!out) throw new EmlError("Could not evaluate this circuit.");
  let singular = why.get(root) ?? null;
  // A noted argument under a cached subtree is not in this pass's memo. Its
  // value is in the cache; without it a repeat evaluation drops the note.
  // A marked integer power is read without a cache entry, so under a cached
  // parent its own integer is the value.
  const flag = precisionMessage(root, (n) => {
    const big = isMarkedExactInt(n) ? provenInteger(n) : undefined;
    const v = memo.get(n) ?? cache.get(n)?.value ?? (big !== undefined ? z(big.toString(), 0) : undefined);
    return v ? exactToFloat(v) : undefined;
  });
  // A pole is a pole in both engines, including when the gates produced NaN.
  if (flag === SINGULAR_POLE) singular = flag;
  else if (!singular && flag) singular = flag;
  const rootWork = work.get(root);
  const hits = rootWork?.hits ?? [];
  return {
    value: out,
    singular,
    touchedLn0: logged.get(root) === true,
    workExp: rootWork?.all,
    workRe: rootWork?.re,
    workIm: rootWork?.im,
    prodRe: componentProd("re", out.re, hits),
    prodIm: componentProd("im", out.im, hits),
    digits: D.precision,
    sawLead,
    ...riskReport(out, riskBelow(root, out, risk)),
  };
}

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
  if (abs.lt("1e16") && abs.gte("1e-9")) {
    const shown = new D(abs.toFixed(12));
    const gap = abs.sub(shown).abs();
    const intGap = abs.sub(abs.round()).abs();
    const dust = new D(10).pow(-(D.precision - 24));
    // Twelve digits hide 0.5 − 10^(−72) and 1 − 10^(−72). Print the first digits of that tail.
    const hiddenTail = gap.gt(dust) && gap.e < -14;
    const hiddenInt = intGap.gt(dust) && intGap.e < -9;
    if (hiddenTail || hiddenInt) {
      const reveal = hiddenTail && (!hiddenInt || gap.e <= intGap.e) ? gap : intGap;
      const places = Math.min(D.precision - 8, Math.max(12, -reveal.e + 2));
      return sign + abs.toFixed(places).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    }
    const text = abs.toFixed(12).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    return sign + text;
  }
  const exp = abs.toExponential(12).replace(/\.?0+e/, "e").replace("e+", "×10^").replace("e-", "×10^−");
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
  const scale = Math.max(Math.abs(got.re), Math.abs(got.im), Math.abs(exact.re), Math.abs(exact.im));
  const part = (left: number, right: number): boolean => {
    if (!Number.isFinite(left) || !Number.isFinite(right)) return !Object.is(left, right);
    if (Object.is(left, right)) return false;
    // −0 and 0 are the same component. A float 0 against a nonzero exact
    // component is a drop (exp(10^(−9)i) − 1, 10^300 + i). A float-only
    // component is dust when it sits below the digits on screen.
    if (left === 0 && right === 0) return false;
    if (left === 0) return true;
    if (right === 0) return Math.abs(left) > 5e-12 * Math.max(scale, Math.abs(left));
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
  if (v.im.isZero()) return formatDec(v.re);
  if (v.re.isZero()) return formatDecImag(v.im);
  const joiner = v.im.isNeg() ? " − " : " + ";
  return `${formatDec(v.re)}${joiner}${formatDecImag(v.im.abs())}`;
}
