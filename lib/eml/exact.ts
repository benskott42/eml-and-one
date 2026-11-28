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
  isPure,
  precisionMessage,
  trigArg,
} from "./node";
import { besideSumOf, decadeOf, dependsOnUnverified, inScaledShell, isExactUnsure, isLiftedCombine, isLostTiny, isMarkedExactInt, isSeriesShortcut, isUnverified, maxSeriesErrorExp, mayBeInfinite, provenInteger } from "./facts";
import { knownValue } from "./lowering";
import { evaluate as floatEvaluate, precisionNoteOf } from "./node";
import { ballConfirmsValue } from "./exact-ball";

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

/**
 * exp, ln, cos, sin, hypot and atan2 results by working precision and argument.
 * decimal.js values are immutable and these functions depend only on the
 * argument, precision and rounding, so a repeat returns the same digits. A
 * circuit computes the same gate inputs many times (rebuilt shared subcircuits,
 * liftedGap and trigGap re-reading a gate, retries at a precision already run).
 * The key keeps the sign, so sin(-0) stays -0. A value from another constructor
 * (a local clone at its own precision) is not cached.
 */
const MEMO_LIMIT = 8192;
const fnMemo = new Map<string, Map<string, Decimal>>();

function memoKey(x: Decimal): string {
  return (x.isNeg() ? "-" : "+") + x.toString();
}

function memoized(key: string, compute: () => Decimal): Decimal {
  const bucketKey = `${D.precision}|${D.rounding}`;
  let bucket = fnMemo.get(bucketKey);
  if (!bucket) {
    if (fnMemo.size >= 32) fnMemo.clear();
    bucket = new Map();
    fnMemo.set(bucketKey, bucket);
  }
  const known = bucket.get(key);
  if (known !== undefined) return known;
  const value = compute();
  if (bucket.size >= MEMO_LIMIT) bucket.clear();
  bucket.set(key, value);
  return value;
}

function ownD(...parts: Decimal[]): boolean {
  return parts.every((x) => x.constructor === D);
}

function expD(x: Decimal): Decimal {
  return ownD(x) ? memoized(`e${memoKey(x)}`, () => x.exp()) : x.exp();
}

function lnD(x: Decimal): Decimal {
  return ownD(x) ? memoized(`l${memoKey(x)}`, () => D.ln(x)) : D.ln(x);
}

function cosD(x: Decimal): Decimal {
  return ownD(x) ? memoized(`c${memoKey(x)}`, () => x.cos()) : x.cos();
}

function sinD(x: Decimal): Decimal {
  return ownD(x) ? memoized(`s${memoKey(x)}`, () => x.sin()) : x.sin();
}

function hypotD(re: Decimal, im: Decimal): Decimal {
  return ownD(re, im) ? memoized(`h${memoKey(re)},${memoKey(im)}`, () => D.hypot(re, im)) : D.hypot(re, im);
}

function argD(y: Decimal, x: Decimal): Decimal {
  const compute = () => atan2Fast(y, x) ?? D.atan2(y, x);
  return ownD(y, x) ? memoized(`a${memoKey(y)},${memoKey(x)}`, compute) : compute();
}

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
  if (theta.e > 500) {
    // decimal.js's PI_PRECISION is ~1000 and leaves D.precision mutated if getPi throws;
    // an angle past 10^500 cannot be reduced within the 480-digit cap anyway.
    passState.rangeLost = true;
    return { c: NAN, s: NAN };
  }
  const savedPrec = D.precision;
  try {
    return { c: cosD(theta), s: sinD(theta) };
  } catch (err) {
    D.set({ precision: savedPrec });
    if (err instanceof Error && /DecimalError/.test(err.message)) {
      passState.rangeLost = true;
      return { c: NAN, s: NAN };
    }
    throw err;
  }
}

function axisInfinity(part: Decimal): Decimal {
  // exp(+∞ ± iπ/2) is a pure imaginary infinity. The binary64 quarter turn
  // is about 10^(−16) off true π/2, and Infinity times that residual is NaN
  // once a later step subtracts the two infinities.
  if (part.abs().lt("1e-15")) return part.isNeg() ? new D(-0) : ZERO;
  return part.isNeg() ? NEG_INF : POS_INF;
}

const LN10_APPROX = 2.302585092994046;

function expZ(v: Z): Z {
  if (!v.im.isFinite()) return { re: NAN, im: NAN };
  const trig = v.im.isFinite() ? cosSin(v.im) : { c: NAN, s: NAN };
  if (!v.re.isFinite()) {
    if (v.re.isNeg()) return { re: signedZeroFrom(trig.c), im: signedZeroFrom(trig.s) };
    if (v.re.isPos()) return { re: axisInfinity(trig.c), im: axisInfinity(trig.s) };
    return { re: NAN, im: NAN };
  }
  const mag = expD(v.re);
  if (mag.isZero()) {
    // A finite exponent past the decimal range: exp(−10^20) is not 0. Record its
    // decade and mark passState.underflowLost so vanished results and pure towers are refused.
    passState.underflowLost = true;
    const decade = Math.floor(v.re.div(LN10_APPROX).toNumber());
    if (Number.isFinite(decade) && decade < passState.tiniest) passState.tiniest = decade;
    return { re: signedZeroFrom(trig.c), im: signedZeroFrom(trig.s) };
  }
  if (!mag.isFinite()) {
    // A finite exponent past decimal.js's maxE (e.g. T5 = exp(T4)): not a true infinity.
    passState.rangeLost = true;
    return { re: signedInf(trig.c), im: signedInf(trig.s) };
  }
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
  const mag = hypotD(v.re, v.im);
  if (mag.isZero()) return { re: NEG_INF, im: v.re.isNeg() ? negPi : ZERO };
  const onCut = v.im.isZero() && v.re.isNeg();
  noteNearCut(v);
  let arg = onCut ? negPi : argD(v.im, v.re);
  if (!onCut && !v.im.isZero() && (arg.eq(negPi) || arg.eq(negPi.neg()))) {
    const gap = v.re.e - v.im.e;
    if (Number.isFinite(gap) && gap > 8 && gap < 2000) {
      const local = D.clone({ precision: D.precision + gap + 8 });
      arg = new D(local.atan2(new local(v.im.toString()), new local(v.re.toString())).toString());
    }
  }
  if (!mag.isFinite()) return { re: POS_INF, im: arg.isFinite() ? arg : ZERO };
  return { re: lnD(mag), im: arg };
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

/**
 * State one exactReportOnce pass accumulates while it walks the circuit. Gates write it,
 * the pass resets it, and exactReportCore reads it after a pass (a raised pass included).
 * It is one object so every reader and writer names it; before it was twenty module lets.
 */
type PassState = {
  /** Decades cancelled inside one subtraction. A later pass may raise precision. */
  lossGap: number;
  /** Decades cancelled in a subtraction whose residual did NOT snap to 0. */
  surviveLoss: number;
  /**
   * Decades between an imaginary sum and a nonzero term it rounded away. An angle
   * is an imaginary part, and exp turns it back into a value: −π + 2.9×10^(−303)
   * rounds to −π at 120 digits, exp snaps to the axis, and (10^300 + 2i)^(−1) lost
   * its −2×10^(−600) i. recoverTinyPart evaluates again where that term fits.
   */
  absorbIm: number;
  /**
   * Decades between a real sum and a nonzero term it rounded away, and the exponent
   * of that absorbed term. When a later cancellation or division drops the result
   * near that term (e.g. 1e−400 + exp(−800) or hypot((1e−5)², −1e−200) − (1e−5)²),
   * precision must rise past `absorbRe` so the term is not silently lost.
   */
  absorbRe: number;
  /** Gap of a second-order term (x^2/2 of exp, t^2/2 of cos) rounded into 1; judged apart from absorbRe. */
  absorb2: number;
  absorbReTerm: number;
  /**
   * Decades between the real and imaginary parts of a point just off the negative
   * real axis whose log was taken in this pass. Its angle is ±π + δ, and δ falls off
   * the working precision once the gap nears it: −5 − 10^(−300) i reads as −π − 0i,
   * a later exp snaps onto the axis, and the next log takes the other bank, so
   * ln(ln(−5 − 10^(−300) i)) was certified as 1.2613 + 1.0974i (true −1.0974i).
   * The value alone decides this, never a leaf's tag, so a rebuilt circuit agrees,
   * and a plain tiny literal never logs such a point.
   */
  cutGap: number;
  /** True when a finite exp overflowed decimal.js range, or trig exceeded PI_PRECISION. */
  rangeLost: boolean;
  /** True when a finite exp underflowed decimal.js minE to 0 (e.g. exp(−10^20) or exp(−T4)). */
  underflowLost: boolean;
  /** True when the last exactEml call's imaginary part came from the lower-cut convention on the negative real axis. */
  gateCutIm: boolean;
  /** Most negative exponent of a nonzero finite value computed in this pass. */
  tiniest: number;
  /**
   * The same floor per component channel. A value with one nonzero component
   * records only that channel; a value with both nonzero records its smaller
   * exponent in both, since exp and ln of a complex value mix the parts. A real
   * product such as 10^400/7 passes through 10^(−399) in the real channel only,
   * so it says nothing about a lost imaginary part.
   */
  tinyRe: number;
  tinyIm: number;
  /** Largest exponent of a finite value computed in this pass. */
  biggest: number;
  /**
   * Size of the terms that cancelled by at least two decades in the last
   * exactEml call (decimal exponent). Rounding there leaves absolute noise near
   * 10^(size − precision). A gate that does not cancel keeps its relative
   * accuracy, so its size is not counted.
   * A 10^k lift is left out of this only after the cancelled terms reach 1.
   * A shorter lift stays in: that cancellation is the result's rounding.
   */
  emlWork: number;
  emlWorkRe: number;
  emlWorkIm: number;
  /** Hits recorded while the gate under evaluation runs. */
  gateHits: CancelHit[];
  /** The first pass's smallest and largest exponents, for the refusals below. */
  firstTinyParts: TinyParts;
  firstBig: number;
};

function freshPassState(): PassState {
  return {
    lossGap: 0,
    surviveLoss: 0,
    absorbIm: 0,
    absorbRe: 0,
    absorb2: 0,
    absorbReTerm: Number.NEGATIVE_INFINITY,
    cutGap: 0,
    rangeLost: false,
    underflowLost: false,
    gateCutIm: false,
    tiniest: 0,
    tinyRe: 0,
    tinyIm: 0,
    biggest: Number.NEGATIVE_INFINITY,
    emlWork: Number.NEGATIVE_INFINITY,
    emlWorkRe: Number.NEGATIVE_INFINITY,
    emlWorkIm: Number.NEGATIVE_INFINITY,
    gateHits: [],
    firstTinyParts: { re: 0, im: 0 },
    firstBig: Number.NEGATIVE_INFINITY,
  };
}

const passState: PassState = freshPassState();

/**
 * Start one walk. lossGap is reset by its caller, the gate fields by each gate, and
 * firstTinyParts / firstBig are the first pass's snapshot, kept across raised passes.
 */
function resetWalkTallies(): void {
  const fresh = freshPassState();
  passState.tiniest = fresh.tiniest;
  passState.surviveLoss = fresh.surviveLoss;
  passState.absorbIm = fresh.absorbIm;
  passState.absorbRe = fresh.absorbRe;
  passState.absorb2 = fresh.absorb2;
  passState.absorbReTerm = fresh.absorbReTerm;
  passState.cutGap = fresh.cutGap;
  passState.rangeLost = fresh.rangeLost;
  passState.underflowLost = fresh.underflowLost;
  passState.tinyRe = fresh.tinyRe;
  passState.tinyIm = fresh.tinyIm;
  passState.biggest = fresh.biggest;
}

/** Decades above 1 of an angle that exp turns. cos(10^300) carries 10^(300 − digits). */
function angleDecades(x: Z): number {
  if (!x.re.isFinite() || !x.im.isFinite() || x.im.isZero()) return 0;
  return Math.max(0, x.im.e);
}

function noteNearCut(v: Z): void {
  if (v.im.isZero() || !v.re.isNeg() || !v.re.isFinite() || !v.im.isFinite()) return;
  const gap = v.re.e - v.im.e;
  if (gap > D.precision - 24 && gap > passState.cutGap) passState.cutGap = gap;
}

function noteAbsorb(left: Decimal, right: Decimal, out: Decimal): void {
  if (!out.isFinite() || out.isZero() || !left.isFinite() || !right.isFinite()) return;
  for (const term of [left, right]) {
    if (term.isZero()) continue;
    const gap = out.e - term.e;
    if (gap > D.precision - 8 && gap > passState.absorbIm) passState.absorbIm = gap;
  }
}

function noteAbsorbRe(left: Decimal, right: Decimal, out: Decimal, leftNoise: boolean, rightNoise: boolean): void {
  if (!out.isFinite() || out.isZero() || !left.isFinite() || !right.isFinite()) return;
  const pairs: [Decimal, boolean][] = [[left, leftNoise], [right, rightNoise]];
  for (const [term, noisy] of pairs) {
    if (term.isZero() || noisy) continue;
    const gap = out.e - term.e;
    // Strictly past D.precision + 4: 1-ulp rounding dust sits near D.precision and is not a real absorbed term.
    if (gap > D.precision + 4) {
      if (gap > passState.absorbRe) passState.absorbRe = gap;
      if (term.e > passState.absorbReTerm) passState.absorbReTerm = term.e;
    }
  }
}

type TinyParts = { re: number; im: number };

function partsFloor(v: Z): TinyParts {
  const live = (part: Decimal) => part.isFinite() && !part.isZero();
  const reLive = live(v.re);
  const imLive = live(v.im);
  if (reLive && imLive) {
    const low = Math.min(0, v.re.e, v.im.e);
    return { re: low, im: low };
  }
  return { re: reLive ? Math.min(0, v.re.e) : 0, im: imLive ? Math.min(0, v.im.e) : 0 };
}

function minParts(...all: TinyParts[]): TinyParts {
  let re = 0;
  let im = 0;
  for (const p of all) {
    if (p.re < re) re = p.re;
    if (p.im < im) im = p.im;
  }
  return { re, im };
}

/** Smallest exponent of a nonzero finite component, or 0, the same floor `passState.tiniest` starts from. */
function exponentCeil(v: Z): number {
  let high = Number.NEGATIVE_INFINITY;
  for (const part of [v.re, v.im]) if (part.isFinite() && !part.isZero() && part.e > high) high = part.e;
  return high;
}

function exponentFloor(v: Z): number {
  let low = 0;
  for (const part of [v.re, v.im]) if (part.isFinite() && !part.isZero() && part.e < low) low = part.e;
  return low;
}

function noteSeen(v: Z): void {
  const take = (part: Decimal) => {
    if (part.isFinite() && !part.isZero() && part.e < passState.tiniest) passState.tiniest = part.e;
    if (part.isFinite() && !part.isZero() && part.e > passState.biggest) passState.biggest = part.e;
  };
  take(v.re);
  take(v.im);
  const parts = partsFloor(v);
  if (parts.re < passState.tinyRe) passState.tinyRe = parts.re;
  if (parts.im < passState.tinyIm) passState.tinyIm = parts.im;
}
/**
 * A refinement that runs out of budget (time or nodes) must not fall back to the
 * reading it was refining: with a deadline, (−5 − 10^(−300) i) − (10^(−236) + 10^(−236) i)
 * timed out inside the tiny-part recovery and was certified as −5. The limit error
 * goes up to the caller, which says the evaluation timed out or was too large.
 */
function rethrowBudget(err: unknown): void {
  if (err instanceof EmlLimitError) throw err;
}

/** Working precision is never raised past this. A value that still needs more is not certified. */
const PRECISION_CAP = 480;

/** One subtraction's cancelled terms and the residual they left. */
type CancelHit = { part: "re" | "im"; scale: number; diff: number };

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
  if (!diff.isZero()) passState.gateHits.push({ part, scale: scale.e, diff: diff.abs().e });
  passState.emlWork = Math.max(passState.emlWork, scale.e);
  if (part === "re") passState.emlWorkRe = Math.max(passState.emlWorkRe, scale.e);
  else passState.emlWorkIm = Math.max(passState.emlWorkIm, scale.e);
}

function noteLoss(scale: Decimal, residual: Decimal): void {
  if (!scale.isFinite() || scale.isZero() || !residual.isFinite() || residual.isZero()) return;
  const gap = scale.e - residual.abs().e;
  if (Number.isFinite(gap) && gap > passState.lossGap) passState.lossGap = gap;
}

function noteSurviveLoss(scale: Decimal, residual: Decimal): void {
  if (!scale.isFinite() || scale.isZero() || !residual.isFinite() || residual.isZero()) return;
  const gap = scale.e - residual.abs().e;
  if (Number.isFinite(gap) && gap > passState.surviveLoss) passState.surviveLoss = gap;
}

function cancelled(diff: Decimal, left: Decimal, right: Decimal, part: "re" | "im"): Decimal {
  if (!diff.isFinite()) return diff;
  noteWork(left, right, diff, part);
  // Keep a signed zero. exp(−∞ + iπ) is −0, and wiping that sign makes √0 infinite.
  if (diff.isZero()) return diff.isNeg() ? new D(-0) : ZERO;
  const scale = D.max(left.abs(), right.abs());
  noteLoss(scale, diff);
  if (scale.gt(0) && diff.abs().lte(scale.mul(tol()))) return ZERO;
  noteSurviveLoss(scale, diff);
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

function exactEml(x: Z, y: Z, leftNoise = false, rightNoise = false, leftCutIm = false, rightCutIm = false): Z {
  passState.gateCutIm = false;
  if (x.re.isNaN() || x.im.isNaN() || y.re.isNaN() || y.im.isNaN()) return { re: NAN, im: NAN };
  const a = expZ(x);
  const b = lnEml(y);
  if (a.re.isNaN() || a.im.isNaN() || b.re.isNaN() || b.im.isNaN()) return { re: NAN, im: NAN };
  if (sameInfinity(a.re, b.re) || sameInfinity(a.im, b.im)) return { re: NAN, im: NAN };
  const re = cancelled(a.re.sub(b.re), a.re, b.re, "re");
  const im = cancelled(a.im.sub(b.im), a.im, b.im, "im");
  // ln(1 + dust) ≈ dust when y ≈ 1 had cancellation noise, and exp(re) ≈ dust when x had noise.
  const bNoisy = rightNoise || (y.re.isFinite() && y.re.sub(1).abs().lte(new D(10).pow(-(D.precision - 4))));
  noteAbsorbRe(a.re, b.re, re, leftNoise, bNoisy);
  noteAbsorb(a.im, b.im, im);
  if (re.isNaN() || im.isNaN()) return { re: NAN, im: NAN };
  const lnOnCut =
    y.re.isNeg() &&
    (y.im.isZero() || (rightCutIm && y.re.isFinite() && y.im.isFinite() && y.im.abs().lte(y.re.abs().mul(new D(10).pow(-(D.precision - 12))))));
  if (im.isFinite() && !im.isZero()) {
    passState.gateCutIm = lnOnCut || (leftCutIm && a.im.isFinite() && !a.im.isZero());
  }
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
    // The words also carry terms near 1 (exp y ≈ 1 in the sub word, e in the add word), so
    // terms below 1 still leave noise near 10^(−precision): count from 1 at least.
    gap = Math.max(gap, Math.max(scale.e, 0) - diff.abs().e);
  }
  return gap;
}

/**
 * Decades exp(x) loses in a component where cos or sin of x.im is small beside
 * the angle: an angle near a nonzero multiple of π/2. The angle carries absolute
 * rounding near 10^(e(θ) − precision), so cos(π/2 + 10^(−108)) at 120 digits keeps
 * 12 digits, and (10^108 − i)·sin(atanh(−i)) printed a wrong real part. A small
 * angle has no such loss: sin θ ≈ θ keeps θ's relative accuracy. An angle within
 * the snap tolerance is that axis and loses nothing.
 */
function trigGap(x: Z): number {
  if (!x.re.isFinite() || !x.im.isFinite() || x.im.isZero() || x.im.e < 0) return 0;
  const trig = cosSin(x.im);
  let gap = 0;
  for (const part of [trig.c, trig.s]) {
    if (!part.isFinite() || part.isZero()) continue;
    gap = Math.max(gap, x.im.e - part.e);
  }
  return gap;
}

/**
 * `lost`: this node's value carries a dropped part. `inherited`: it came from an
 * operand, not from this gate's own zero. `liftGap`: this gate's lifted cancellation,
 * or the digits its angle lost in cos and sin. `trigGap`: decades of a large angle,
 * which raise the absolute noise of cos and sin by as many.
 */
type GateRisk = { lost: boolean; inherited: boolean; liftGap: number; trigGap: number };

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
  const total: GateRisk = { lost: rootLost, inherited: false, liftGap: 0, trigGap: 0 };
  while (stack.length) {
    const node = stack.pop();
    if (!node || node.type !== "eml" || seen.has(node)) continue;
    seen.add(node);
    const risk = riskOf(node, pass, store);
    if (risk) {
      total.liftGap = Math.max(total.liftGap, risk.liftGap);
      total.trigGap = Math.max(total.trigGap, risk.trigGap ?? 0);
    }
    stack.push(node.a, node.b);
  }
  return total;
}

function riskOf(node: Node, pass: Map<Node, GateRisk>, store: WeakMap<Node, GateRisk>): GateRisk | undefined {
  return pass.get(node) ?? (hasVarOf.get(node) === false ? store.get(node) : undefined);
}

/** A lost part refuses any value but undefined. */
function riskReport(out: Z, below: GateRisk): Pick<ExactReport, "unverified" | "liftGap" | "trigGap"> {
  const lost = below.lost && !out.re.isNaN() && !out.im.isNaN();
  const gaps = { liftGap: below.liftGap, trigGap: below.trigGap };
  return lost ? { unverified: true, ...gaps } : gaps;
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
  /** Decades of the largest angle turned: that many more decades of absolute noise. */
  trigGap?: number;
  /** Largest imaginary term rounded away beside its sum, in decades. */
  absorbIm?: number;
  /** Largest real term rounded away beside its sum, in decades, and its exponent. */
  absorbRe?: number;
  absorbReTerm?: number;
  absorb2?: number;
  /** True when a gate collapsed an absorbed-real subtree to 0 (e.g. ln(1 + 1e-200) -> 0). */
  absorbExposed?: boolean;
  /** Largest cancellation gap in any gate of the pass, in decades. */
  lossGap?: number;
  /** Largest non-snapped cancellation gap in any gate of the pass, in decades. */
  surviveLoss?: number;
  /** Largest gap of a log taken just off the negative real axis, or of a remembered huge sum (see passState.cutGap). */
  cutGap?: number;
  /** True when the displayed value's imaginary part comes from the lower-cut convention on the negative real axis. */
  nearCut?: boolean;
  /** True when a finite exp overflowed decimal.js range, or trig exceeded PI_PRECISION. */
  rangeLost?: boolean;
  /** True when a finite exp underflowed decimal.js minE to 0. */
  underflowLost?: boolean;
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
/** `loss`, `passState.tiniest` and `lead` are the subtree's share of the pass state, restored on a hit. */
type Cached = { value: Z; why: string | null; logged: boolean; work: Work; loss: number; surviveLoss: number; tiniest: number; tinyParts: TinyParts; lead: boolean; big: number; absorb: number; absorbRe: number; absorb2: number; absorbReTerm: number; absorbExposed: boolean; cut: number; rangeLost: boolean; underflowLost: boolean; cutIm: boolean };
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
    // Gates mix the parts, so each part is good to about 10^(top − digits) absolute, where
    // top is the larger part's decade. A part far below the other keeps only the decades
    // above that: (10^100 + i)·2 read at 148 digits has 2 + 8×10^(−49) i, and the 120-digit
    // round kept that noise, so the screen revealed 2.000…0078i.
    const top = Math.max(...[report.value.re, report.value.im].filter((x) => x.isFinite() && !x.isZero()).map((x) => x.e), Number.NEGATIVE_INFINITY);
    const places = Number.isFinite(top) ? digits - 12 - top : Number.POSITIVE_INFINITY;
    const round = (part: Decimal) => {
      if (!part.isFinite()) return part;
      const kept = Number.isFinite(places) && places >= 0 && part.e + places < saved ? part.toDecimalPlaces(places) : part;
      return new D(kept.toSignificantDigits(saved).toString());
    };
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
  // An angle that lost digits in cos or sin (the lift gap) raises the noise by as
  // many decades: sinh(10^300 i) at 348 digits cancels its real part to 4.6×10^(−47).
  const lost = Math.max(0, report.trigGap ?? 0);
  const noise = new D(10).pow(workExp - ((report.digits ?? D.precision) - lost - 12));
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
  // 24 more digits are not enough when the dust is a term the gates absorbed, not
  // rounding: sin(x) for x = 2.77×10^(−87) left x²·i/2, which holds still until
  // 1 + x² fits. Read again where the part sits 24 digits above the noise.
  const digits = report.digits ?? D.precision;
  const workExp = report.workExp ?? 0;
  const fits = Math.min(PRECISION_CAP, Math.max(digits + 24, workExp - part.e + 36));
  let again: Decimal;
  try {
    again = atPrecision(fits, root, env, budget).value[which];
  } catch (err) {
    // Out of budget is never a certificate: see rethrowBudget.
    rethrowBudget(err);
    return report;
  }
  if (again.isFinite() && part.sub(again).abs().lte(part.abs().mul("1e-6"))) return report;
  const cleared = part.isNeg() ? new D(-0) : ZERO;
  return {
    ...report,
    ...(which === "im" ? { nearCut: false } : {}),
    value: which === "re" ? { re: cleared, im: report.value.im } : { re: report.value.re, im: cleared },
  };
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
  const absorbed = report.absorbIm ?? 0;
  const leafHint = demandedTinyDigits(root, env);
  const hinted = Math.max(leafHint, absorbed > 0 ? absorbed + 48 : 0);
  if (hinted <= D.precision) return null;
  if (hinted > PRECISION_CAP) return null;
  const readAt = Math.min(PRECISION_CAP, Math.max(hinted, digits));
  let first: ExactReport;
  let second: ExactReport;
  try {
    first = atPrecision(readAt, root, env, budget, false);
    if (first.unverified || first.value[which].isZero()) return null;
    // The second reading is where the part sits 24 digits above the noise of the
    // terms the gates worked at. A term they absorbed holds still until it fits:
    // sin(2/exp(300)) kept −5.3×10^(−261) i at 179 and 203 digits, and it is 0.
    const fits = (first.workExp ?? 0) - first.value[which].e + 36;
    second = atPrecision(Math.min(PRECISION_CAP, Math.max(readAt + 24, fits)), root, env, budget, false);
  } catch (err) {
    // Out of budget is never a certificate: see rethrowBudget.
    rethrowBudget(err);
    return null;
  }
  // A part under the noise of the terms that cancelled at that precision is a
  // rounding residue even when it holds still: sin(−10^(−400)) leaves ~10^(−801) i.
  // An absorbed angle alone is not a cancellation: (10^300 + 2i)^(−1) rotates its
  // −2×10^(−600) i out of −π + 2.9×10^(−303), under a work tally of size 1.
  const work = which === "re" ? first.workRe : first.workIm;
  if (leafHint > D.precision && work !== undefined && Number.isFinite(work) && first.value[which].abs().lt(residueFloor(work, first.digits ?? readAt))) return null;
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
  const threshold = D.precision - 12;
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
    } catch (err) {
      // Out of budget is never a certificate: see rethrowBudget.
      rethrowBudget(err);
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
/**
 * Whether the circuit uses a remembered huge sum (rememberHugeReal) anywhere. That
 * node's gates hold only the bare integer, so any circuit built on it drops the
 * small term. The walk covers the whole DAG: a depth-8 / 64-step cap missed the
 * marker under the product word, and (10^400+i)·2 was certified as 2×10^400.
 * The refused-sum placeholder (`unverified:`, an input 0) counts too. A user-level
 * sum that returns it is refused, but a library word builds on it as a plain 0:
 * atanh(exp(−50) − 10^400) adds 1 inside its own circuit, and √0/√0 printed
 * undefined, and so did atan(10^400 − 6 + i).
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
    // A remembered sum this module evaluates itself (see the walk in exactReportOnce).
    // Its operands are what count; the bare-integer gates under it are never read.
    const beside = besideSumOf(node);
    if (beside) {
      stack.push(beside.huge, beside.other);
      continue;
    }
    if (node.type === "input") {
      if (node.label.startsWith("beside:") || node.label.startsWith("unverified:")) {
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
 * Results this release refuses rather than certify:
 * - a sin, cos or tan below the root whose argument is too large to reduce
 *   (−cos(10^119), cos(10^125)·cos(10^130)); the root's own note already flags it;
 * - a component cancelled to 0 beside a nonzero one when the pass computed a
 *   value too small for the working precision (((1+1/10^130)−1)+i/2);
 * - a finite result far below a value past float range that the circuit went
 *   through ((exp(800)+1)−exp(800)), or a non-finite one reached that way (exp(800)·0).
 *   A large value alone is not the risk: a term absorbed into it and cancelled
 *   later is. ln(10^400) and √(4×10^(−400)) pass through 10^400 and lose nothing,
 *   so a result an enclosure confirms is kept (see confirmedBeside).
 */
function refusedResult(root: Node, env: Record<string, C | Z>, budget: EvalBudget, out: ExactReport): boolean {
  if (nestedTrigTooLarge(root, env)) return true;
  // A series shortcut scales its argument by its own reciprocal powers, so the
  // smallest and largest values seen say nothing about cancellation there.
  if (out.sawLead) return false;
  if (agreesWithInteger(root, out.value)) return false;
  const v = out.value;
  const digits = out.digits ?? D.precision;
  // A finite exp that overflowed decimal.js range (e.g. T5 = exp(T4) in 111E1E1E1E1EE1E)
  // or a trig argument past PI_PRECISION cannot be certified unless the ball proves it.
  if (out.rangeLost) {
    if (!zFinite(v) || !confirmedBeside(root, env, budget, v, digits)) return true;
  }
  // A finite exp that underflowed minE to 0 (e.g. exp(−T4) or exp(−10^20)) cannot certify
  // a non-finite result (such as ln(exp(−1e20)) -> −∞ or 1/exp(−1e20) -> ∞), a vanished 0,
  // nor an exact-looking deep tower program.
  if (out.underflowLost && (!zFinite(v) || vanished(v) || (isPure(root) && passState.firstBig > 308))) {
    if (!zFinite(v) || !confirmedBeside(root, env, budget, v, digits)) return true;
  }
  // An imaginary term absorbed past the 480-digit cap can hide a component or flip a branch cut.
  if ((out.absorbIm ?? 0) > PRECISION_CAP) {
    if (!zFinite(v) || !confirmedBeside(root, env, budget, v, digits, 24)) return true;
  }
  // Pure 1-and-E tower impostors must never silently certify as exact integers or short
  // terminating decimals when an extra real term was absorbed past working precision
  // inside a deep tower (passState.firstBig > 308, e.g. 111E1E1E1EE11EE = −1 + e/T4,
  // 111111EEEE1E1E1EE11EE), sits inside the exactInteger dust band
  // (1111EE1E1E1EE11EE = −1 + 4.4×10^(−116)), or was snapped to 0 and then exp'd to 1
  // (1111EE1E1E1EE1E11EE1E).
  if (isPure(root)) {
    const deepAbsorb = (out.absorbRe ?? 0) > PRECISION_CAP || ((passState.firstBig > 308 || !out.touchedLn0) && (out.absorbRe ?? 0) > digits - 12);
    if (deepAbsorb && zFinite(v) && (looksExactDecimal(v.re) || looksExactDecimal(v.im))) {
      return true;
    }
    if (!out.touchedLn0 && v.im.isZero() && exactInteger(v.re)) {
      const rounded = v.re.round();
      const gap = v.re.sub(rounded).abs();
      const snapped = (out.lossGap ?? 0) > digits - 12;
      if (!gap.isZero() || snapped) {
        const firstNext = snapped ? Math.min(PRECISION_CAP, Math.max(digits + 24, (out.lossGap ?? 0) + 48)) : Math.min(PRECISION_CAP, digits + 24);
        if (firstNext > digits) {
          const again = atPrecision(firstNext, root, env, budget, false);
          if (!again.unverified && again.value.re.isFinite()) {
            const gap2 = again.value.re.sub(rounded).abs();
            if (!gap.isZero()) {
              if (!gap2.isZero() && !residueMoved(gap, gap2)) return true;
            } else if (!gap2.isZero()) {
              const secondNext = Math.min(PRECISION_CAP, firstNext + 24);
              if (secondNext <= firstNext) return true;
              const check = atPrecision(secondNext, root, env, budget, false);
              if (check.unverified || !check.value.re.isFinite()) return true;
              const gap3 = check.value.re.sub(rounded).abs();
              if (!gap3.isZero() && !residueMoved(gap2, gap3)) return true;
            }
          }
        }
      }
    }
  }
  if (v.re.isFinite() && v.im.isFinite() && v.re.isZero() !== v.im.isZero()) {
    // A value below the precision went through the pass: retry with room for it.
    // If the zero part comes back nonzero above the noise, or the room needed is
    // past the cap, the 0 is not certified.
    const which = v.re.isZero() ? "re" : "im";
    const other = which === "re" ? v.im : v.re;
    // Only a value that could reach the zero component counts: its own channel.
    // An angle that lost digits in cos or sin leaves that much more noise:
    // cosh(10^20 i) cancels its imaginary part to about 10^(20 − digits).
    const lost = Math.max(0, out.trigGap ?? 0);
    const need = other.e - passState.firstTinyParts[which] + 30 + lost;
    if (need > digits) {
      // Ball enclosure as first judge: if it proves the zero component is exact 0 and the
      // nonzero component matches, no precision retry or refusal is needed.
      if (confirmedBeside(root, env, budget, v, digits, 24)) return false;
      if (need > PRECISION_CAP) return true;
      const wide = atPrecision(need, root, env, budget, false).value[which];
      if (!wide.isFinite() || (!wide.isZero() && wide.e > other.e - need + lost + 20)) return true;
    }
  }
  if (passState.firstBig > 308) {
    if (!zFinite(v)) return out.singular === SINGULAR_NONFINITE;
    const top = exponentCeil(v);
    if (top >= -300 && top < passState.firstBig - (digits - 12)) {
      if (!confirmedBeside(root, env, budget, v, digits)) return true;
    }
  }
  // A second-order term (x²/2 of exp or cos) was rounded into 1 inside a gate and the
  // result vanished to 0 or sits at the working-precision floor (e.g. exp(10^(−237)) − 1 − 10^(−237)):
  // confirm with a rigorous ball enclosure, or refuse.
  if (
    (out.absorb2 ?? 0) > digits - 12 &&
    !out.sawLead &&
    !agreesWithInteger(root, v) &&
    (vanished(v) || (digits > D.precision && zFinite(v) && Math.abs(exponentCeil(v) + digits) <= 4))
  ) {
    if (!zFinite(v) || !confirmedBeside(root, env, budget, v, digits, 24)) return true;
  }
  return false;
}

/** True when formatExact would display `d` as an exact integer or short terminating decimal (no 12-place tail). */
function looksExactDecimal(d: Decimal): boolean {
  if (!d.isFinite() || d.isZero()) return false;
  if (exactInteger(d)) return true;
  const abs = d.abs();
  if (abs.lt("1e16") && abs.gte("1e-6")) {
    const trimmed = abs.toFixed(12).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    const places = (trimmed.split(".")[1] ?? "").length;
    if (places <= 9) return true;
  } else if (abs.lt("1e-6")) {
    const sig = abs.toExponential(11).split("e")[0].replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    const places = (sig.split(".")[1] ?? "").length;
    if (places <= 9) return true;
  }
  return false;
}

/**
 * The size rule above stands in for what it cannot see: whether a term was
 * absorbed into a large value and then cancelled away with it. An enclosure sees
 * it directly (exact-ball.ts): its radius carries every rounding, so an absorbed
 * term leaves the radius as large as the value it was absorbed into. A result the
 * enclosure confirms at 60 more digits than the pass, to all but 20 of the pass's
 * digits, with each zero part exactly 0, is kept. (exp(800)+1)−exp(800) leaves a
 * radius near 10^168 and stays refused; ln(10^400) is confirmed.
 */
function confirmedBeside(
  root: Node,
  env: Record<string, C | Z>,
  budget: EvalBudget,
  v: Z,
  passDigits = D.precision,
  agree = D.precision - 20,
): boolean {
  // Try 180 digits first when passDigits is already high: many large/absorbed expressions
  // confirm immediately at 180 digits without paying for a 480-digit ball pass.
  if (passDigits > 180 && ballConfirmsValue(root, env, v, 180, agree, budget)) return true;
  const prec = Math.min(480, Math.max(D.precision, passDigits) + 60);
  return ballConfirmsValue(root, env, v, prec, agree, budget);
}

/**
 * A root the compiler built as an exact integer (a sum, product or integer power
 * of integers; see rangeOf in lowering.ts) whose gates agree with that integer to
 * the working precision. An integer has no imaginary part and no small real one,
 * so the zero-part and size rules have nothing left to find there. (−10^200)^3 is
 * −10^600: its gates pass through 10^(−5) i, and ruling out a part that small
 * beside 10^600 needed 635 digits, past the cap.
 */
function agreesWithInteger(root: Node, v: Z): boolean {
  const big = provenInteger(root);
  if (big === undefined || !v.re.isFinite() || !v.im.isFinite() || !v.im.isZero()) return false;
  const want = new D(big.toString());
  if (want.isZero()) return v.re.isZero();
  return v.re.sub(want).abs().lte(want.abs().mul(new D(10).pow(-(D.precision - 12))));
}

function nestedTrigTooLarge(root: Node, env: Record<string, C | Z>): boolean {
  const floatEnv: Record<string, C> = {};
  for (const [name, value] of Object.entries(env)) floatEnv[name] = value.re instanceof Decimal ? exactToFloat(value as Z) : (value as C);
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    const note = precisionNoteOf(n);
    // A lowered sum can rebuild its operands, so the noted originals are walked too.
    if (note?.kind === "add") stack.push(note.left, note.right);
    else if (note) stack.push(note.arg);
    if (n !== root) {
      if (note && (note.kind === "trig" || note.kind === "pole")) {
        let arg: C | undefined;
        try {
          arg = floatEvaluate(note.arg, floatEnv);
        } catch {
          arg = undefined;
        }
        if (arg && Number.isFinite(arg.re) && Number.isFinite(arg.im) && Math.abs(arg.im) <= 1 && Math.abs(arg.re) > 1e15) return true;
      }
    }
    if (n.type === "eml" && n.a && n.b) stack.push(n.a, n.b);
  }
  return false;
}

export function exactReport(
  root: Node,
  env: Record<string, C | Z> = {},
  budget: EvalBudget = {},
  pass = 0,
): ExactReport {
  if (pass !== 0) return exactReportCore(root, env, budget, pass);
  passState.firstTinyParts = { re: 0, im: 0 };
  passState.firstBig = Number.NEGATIVE_INFINITY;
  const out = exactReportCore(root, env, budget, pass);
  if (overflowNaN(root, env, out)) return { ...out, singular: null, unverified: true };
  if (out.unverified) return out;
  // A value read off a node refused below the root is not certified either.
  // An undefined result stays: (1 + 1/0) − 1/0 is still the indeterminate ∞ − ∞.
  if (!(out.value.re.isNaN() && out.value.im.isNaN()) && dependsOnUnverified(root)) return { ...out, singular: null, unverified: true };
  // If a crude linear series shortcut (e.g. sinh/artanh for |z| < 1e-6) was used and the
  // result is small enough to be contaminated by the dropped z³ term, refuse to certify.
  const crudeErr = maxSeriesErrorExp(root);
  if (crudeErr !== undefined && zFinite(out.value)) {
    const top = vanished(out.value) ? Number.NEGATIVE_INFINITY : exponentCeil(out.value);
    if (top <= crudeErr + 12) return { ...out, singular: null, unverified: true };
  }
  if (refusedResult(root, env, budget, out)) return { ...out, unverified: true };
  return squaredTinyPart(root, env, budget, out);
}

/**
 * The probe pass in squaredTinyPart. `limit` is the decade below which a value's
 * square no longer fits the working precision; `low` is the smallest decade lifted.
 */
let probe: { limit: number; low: number; follows: WeakSet<Z> } | null = null;

function wholeTiny(v: Z, limit: number): boolean {
  return zFinite(v) && !zZero(v) && exponentCeil(v) < limit;
}

/**
 * In the probe pass, a tiny value made from operands that are not tiny (a leaf, or
 * exp of a large negative real such as the 1/10^100 word) is lifted to about
 * 10^(−30), each component on its own: 10^(−100) + 10^(−150) i lifted as one keeps
 * its 50-decade gap, and the product of the two parts would still not fit. Values
 * computed from lifted ones follow them and are not lifted again.
 */
function lifted(v: Z, x?: Z, y?: Z): Z {
  if (!probe) return v;
  if (x && y && (probe.follows.has(x) || probe.follows.has(y))) {
    probe.follows.add(v);
    return v;
  }
  if (!wholeTiny(v, probe.limit)) return v;
  if (x && y) {
    // Only exp of a large negative real makes a new tiny value. A residue of a
    // cancellation is the circuit's rounding, and lifting it would invent a part.
    if (!x.re.isFinite() || !x.re.lt(probe.limit * LN10_APPROX) || wholeTiny(x, probe.limit) || wholeTiny(y, probe.limit)) return v;
  }
  probe.low = Math.min(probe.low, exponentCeil(v));
  // The nearest decade, not the exponent: 9.99…×10^(−301) and 10^(−300) are one value
  // reached by two words, and must be lifted by the same factor.
  const lift = (part: Decimal) => {
    if (part.isZero() || !part.isFinite() || part.e >= -30) return part;
    const mant = part.abs().div(new D(10).pow(part.e)).toNumber();
    const decade = part.e + Math.round(Math.log10(mant));
    return part.mul(new D(10).pow(-30 - decade));
  };
  const out = { re: lift(v.re), im: lift(v.im) };
  probe.follows.add(out);
  return out;
}

/**
 * A component 0 beside a nonzero one, when the circuit holds an input so small that
 * its square is below the working precision. Second-order parts are rounded away
 * before any cancellation sees them: cosh(10^(−100)) is 1 + 5×10^(−201), which is 1
 * at 120 digits, so cosh(10^(−100))^i certified 1 (true 1 + 5×10^(−201) i), and
 * cos(10^(−100) + 10^(−150) i) lost −10^(−250) i. The tally of tiny values is per
 * channel, and ·i moves a real one into the other channel.
 * A probe pass lifts each such input to about 10^(−30), where squares and cubes fit.
 * A component that stays 0 there does not depend on them (cos(10^(−300)) stays real).
 * One that appears is read again where the square fits, and kept if it holds still;
 * past 480 digits, or if it moves, the result is not certified.
 */
function squaredTinyPart(root: Node, env: Record<string, C | Z>, budget: EvalBudget, out: ExactReport): ExactReport {
  const v = out.value;
  if (!v.re.isFinite() || !v.im.isFinite() || v.re.isZero() === v.im.isZero()) return out;
  const which: "re" | "im" = v.re.isZero() ? "re" : "im";
  const other = which === "re" ? "im" : "re";
  const limit = -Math.floor((D.precision - 24) / 2);
  if (Math.min(passState.firstTinyParts.re, passState.firstTinyParts.im) >= limit) return out;
  // The probe's verdict: the part depends on the lifted inputs, does not, or the
  // lifted circuit gave no usable reading (a 10^k lift word overflows once its
  // operand is lifted), in which case only a raised reading can show the part.
  let seen: Z | null = null;
  let low = 0;
  try {
    probe = { limit, low: 0, follows: new WeakSet() };
    seen = exactReportOnce(root, env, budget).value;
    low = probe.low;
  } catch (err) {
    // Out of budget is never a certificate: see rethrowBudget.
    rethrowBudget(err);
    seen = null;
  } finally {
    probe = null;
  }
  if (seen && low >= limit) return out;
  // A large angle leaves as many more decades of noise (see dustPart): sinh(10^300 i)
  // reads 5×10^(−87) in the lifted real part, and it is noise.
  const lost = Math.max(0, out.trigGap ?? 0);
  const usable = !!seen && zFinite(seen) && !seen[other].isZero();
  if (usable && seen) {
    const part = seen[which];
    // Measured against 1 as well: the gates work near 1, so their noise is about
    // 10^(−precision) even beside a small part (tanh of 10^(−30) i leaves 6×10^(−121)).
    if (part.isZero() || part.e <= Math.max(seen[other].e, 0) - (D.precision - 24 - lost)) return out;
  }
  const dependent = usable;
  const floor = Math.min(low, passState.firstTinyParts.re, passState.firstTinyParts.im);
  const need = -2 * floor + 48;
  const first = Math.min(PRECISION_CAP - 24, Math.max(D.precision + 24, need));
  // A reading that fits the square and shows no part settles it: the part is 0.
  // One that cannot fit it (past 480 digits) refuses when the probe saw the part.
  const refuse = (): ExactReport => (dependent && need > first ? { ...out, unverified: true } : out);
  let a: ExactReport;
  let b: ExactReport;
  try {
    a = atPrecision(first, root, env, budget, false);
    if (a.unverified) return { ...out, unverified: true };
    // A part under the noise of terms near 1 is not a reading: tanh(10^(−100) i/3)
    // leaves about 10^(−452) in the real part at 450 digits, and it moves.
    const shown = a.value[which];
    const scale = Math.max(a.value[other].isZero() ? 0 : a.value[other].e, 0);
    if (shown.isZero() || !shown.isFinite() || shown.e <= scale - (first - 24 - lost)) return refuse();
    const work = which === "re" ? a.workRe : a.workIm;
    const fits = (work !== undefined && Number.isFinite(work) ? work : 0) - a.value[which].e + 36;
    b = atPrecision(Math.min(PRECISION_CAP, Math.max(first + 24, fits)), root, env, budget, false);
  } catch (err) {
    // Out of budget is never a certificate: see rethrowBudget.
    rethrowBudget(err);
    // Out of budget: a part the probe saw is not certified as 0.
    return dependent ? { ...out, unverified: true } : out;
  }
  // A part that appears and then moves is rounding, and the result is not certified.
  if (b.unverified || residueMoved(a.value[which], b.value[which]) || residueMoved(a.value[other], b.value[other])) return { ...out, unverified: true };
  return { ...out, value: a.value, digits: a.digits };
}

/**
 * ∞ − ∞ that no ln 0, pole, or division by 0 of the expression produced. The
 * words overflowed on the way: asinh(1/10^(−200)) is 461.2…, not undefined.
 * Not certified either way.
 */
/** Any node below is an infinite source (ln 0, a pole, a division by 0) or a non-finite leaf. */
function infinityBelow(root: Node): boolean {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    if (mayBeInfinite(node)) return true;
    if (node.type === "input" && !(Number.isFinite(node.value.re) && Number.isFinite(node.value.im))) return true;
    if (node.type === "eml") stack.push(node.a, node.b);
  }
  return false;
}

function overflowNaN(root: Node, env: Record<string, C | Z>, out: ExactReport): boolean {
  if (out.singular !== SINGULAR_INDET) return false;
  if (!out.value.re.isNaN() && !out.value.im.isNaN()) return false;
  if (infinityBelow(root)) return false;
  for (const value of Object.values(env)) {
    const re = value.re instanceof Decimal ? value.re.isFinite() : Number.isFinite(value.re as number);
    const im = value.im instanceof Decimal ? value.im.isFinite() : Number.isFinite(value.im as number);
    if (!re || !im) return false;
  }
  return true;
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
  if (isUnverified(root) || isExactUnsure(root) || hidesBeside(root)) {
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
  passState.lossGap = 0;
  const report = exactReportOnce(root, env, budget);
  if (pass === 0) {
    passState.firstTinyParts = { re: passState.tinyRe, im: passState.tinyIm };
    passState.firstBig = passState.biggest;
  }
  // Pass 3 is a raised pass whose caller judges a tiny part itself, so it is not scrubbed.
  if (pass !== 0) return pass === 3 ? report : present(report);
  // A nonzero real term was absorbed into a larger real value inside a gate, and
  // either the result is at or below that absorbed term's scale, or a cancellation
  // uncovered it. Raise precision so the absorbed term is kept, or refuse past cap.
  const firstOrderGap = (r: ExactReport): number => {
    const gap = r.absorbRe ?? 0;
    const digits = r.digits ?? D.precision;
    if (gap <= digits + 1) return 0;
    if (r.sawLead || agreesWithInteger(root, r.value)) return 0;
    if (vanished(r.value) || r.absorbExposed) return gap;
    const top = exponentCeil(r.value);
    const termExp = r.absorbReTerm ?? Number.NEGATIVE_INFINITY;
    if (Number.isFinite(top) && top <= termExp + 24) return gap;
    if ((r.surviveLoss ?? 0) > 8 || (r.lossGap ?? 0) > 8) return gap;
    return 0;
  };
  // A second-order term (x^2/2 of exp, t^2/2 of cos) matters when the result vanished or sits at its
  // scale. A smaller one beside a larger result (sqrt(1 + 1e-130) - 1 - 0.5e-130, sin(2/exp(200)),
  // where the tiny angle is cancellation noise) is hundreds of digits below it and is left alone.
  const secondOrderGap = (r: ExactReport): number => {
    const gap = r.absorb2 ?? 0;
    const digits = r.digits ?? D.precision;
    if (gap <= digits - 12) return 0;
    if (r.sawLead || agreesWithInteger(root, r.value)) return 0;
    if (vanished(r.value)) return gap;
    const top = exponentCeil(r.value);
    if (Number.isFinite(top) && top <= 24 - gap) return gap;
    return 0;
  };
  const absorbedGap = (r: ExactReport): number => Math.max(firstOrderGap(r), secondOrderGap(r));
  const absorbedMatters = (r: ExactReport): boolean => absorbedGap(r) > 0;
  // Raise precision until the absorbed term fits (up to the cap), or refuse. A result that
  // still has an absorbed term past the cap, or after three hops, is kept only if a rigorous
  // ball enclosure confirms its nonzero finite value.
  const canRescueAbsorbed = (cur: ExactReport): boolean =>
    !vanished(cur.value) &&
    zFinite(cur.value) &&
    !nestedTrigTooLarge(root, env) &&
    !dependsOnUnverified(root) &&
    confirmedBeside(root, env, budget, cur.value, cur.digits ?? D.precision, 24);
  const raiseForAbsorbed = (start: ExactReport): ExactReport => {
    let cur = start;
    for (let hop = 0; hop < 3 && absorbedMatters(cur); hop += 1) {
      const gap = absorbedGap(cur);
      const minNeed = gap + 48;
      if (minNeed > PRECISION_CAP) return canRescueAbsorbed(cur) ? cur : certifyZero(cur);
      // Leave 24 digits of headroom below PRECISION_CAP when gap + 48 fits there, so
      // settleResidue can still take a stability check rather than refusing at the cap.
      const cap = minNeed <= PRECISION_CAP - 24 ? PRECISION_CAP - 24 : PRECISION_CAP;
      const next = Math.min(cap, Math.max((cur.digits ?? D.precision) + 48, gap + D.precision));
      if (next <= (cur.digits ?? D.precision)) return canRescueAbsorbed(cur) ? cur : certifyZero(cur);
      cur = atPrecision(next, root, env, budget);
      if (cur.unverified) return cur;
    }
    if (absorbedMatters(cur)) return canRescueAbsorbed(cur) ? cur : certifyZero(cur);
    return { ...cur, absorbIm: Math.max(cur.absorbIm ?? 0, start.absorbIm ?? 0) };
  };
  if (vanished(report.value)) {
    if (report.sawLead) return certifyZero(report);
    // 0 − 10^(−500) and ln(1 − 10^(−500)) have no decade to recover. The zero
    // is the cap, not a proof. A direct −10^(−500) is not zero and stays.
    if (lostTinyIn(root)) return certifyZero(report);
    const gap = report.lossGap ?? passState.lossGap;
    // Any recorded cancellation can hide the term that should have survived.
    // A structural zero such as 1−1 records no gap and stays certified.
    const fromGap = gap > 8 ? gap + 48 : 0;
    // A value below the precision that no gap recorded can still be the answer:
    // atanh(2/exp(300)) adds 1.03×10^(−130) to 1, which absorbs it, and printed 0.
    // Raise to fit it, up to the cap.
    const fromTiny = passState.tiniest < -(D.precision - 24) ? Math.min(PRECISION_CAP, -passState.tiniest + 48) : 0;
    const need = Math.max(demandedTinyDigits(root, env), fromGap, fromTiny);
    if (need > PRECISION_CAP) return certifyZero(report);
    if (need > D.precision) {
      let digits = Math.min(PRECISION_CAP, need);
      let again = atPrecision(digits, root, env, budget);
      // A snap that still lands on 0 is a deeper cancellation than this precision.
      // Raise again, up to the cap. A clean zero with no such snap is resolved.
      while (vanished(again.value) && !again.sawLead && digits < PRECISION_CAP && (again.lossGap ?? passState.lossGap) > digits - 24) {
        digits = Math.min(PRECISION_CAP, Math.max(digits + 96, (again.lossGap ?? passState.lossGap) + 48));
        again = atPrecision(digits, root, env, budget);
      }
      // If a real term is still absorbed inside a gate after the raise (e.g.
      // hypot(10^(−10), −10^(−200)) − 10^(−10)), raise to keep that term or refuse.
      if (vanished(again.value) && !again.sawLead && lostGapOf(again) > digits + 4) {
        const abNeed = lostGapOf(again) + 48;
        if (abNeed > PRECISION_CAP) return certifyZero(again);
        digits = abNeed;
        again = atPrecision(digits, root, env, budget);
      }
      if (vanished(again.value)) {
        const seenNeed = passState.tiniest < -(digits - 24) ? -passState.tiniest + 48 : 0;
        if (again.sawLead || seenNeed > PRECISION_CAP) return certifyZero(again);
        if (seenNeed > digits) {
          again = atPrecision(Math.min(PRECISION_CAP, seenNeed), root, env, budget);
          if (vanished(again.value)) return certifyZero(again);
        } else if ((again.lossGap ?? passState.lossGap) > digits - 16 || lostGapOf(again) > digits + 4) return certifyZero(again);
      }
      // A nonzero that shows up under the cancelled terms is still rounding
      // until a second reading shows it stayed near the magnitude already seen.
      const nonzeroResidue = residueParts(again).some((name) => !again.value[name].isZero());
      let revealed = nonzeroResidue ? settleResidue(again, root, env, budget) : again;
      if (revealed.unverified) return revealed;
      // Ensure full D.precision digits survived any deep cancellation
      // (e.g. (1e200 + 0.5) − (1e200 − 0.5) at 249 digits leaves 10^−49 dust, or
      // tanh(10^(−122) i) − 10^(−122) i at 365 digits leaves 5e−366 real dust).
      const sl = revealed.surviveLoss ?? 0;
      const lg = revealed.lossGap ?? 0;
      const rd = revealed.digits ?? D.precision;
      if (!vanished(revealed.value) && (sl > 8 || lg > rd - 24) && rd - Math.max(sl, lg > rd - 24 ? lg : 0) < D.precision - 12 && rd < PRECISION_CAP) {
        const full = Math.min(PRECISION_CAP, Math.max(sl + D.precision, lg > rd - 24 ? rd + 48 : 0));
        if (full > rd) {
          const wider = atPrecision(full, root, env, budget);
          if (!wider.unverified) {
            const widerNonzeroResidue = residueParts(wider).some((name) => !wider.value[name].isZero());
            revealed = widerNonzeroResidue ? settleResidue(wider, root, env, budget) : wider;
            if (revealed.unverified) return revealed;
          }
        }
      }
      // A part that vanished at the first pass and came back nonzero can still be the
      // rounding of a term a gate absorbed (exp(-10^(-240)) - 1 + 10^(-240) read 5e-465
      // at 288, 312 and 360 digits). Keep the term or refuse.
      if (!vanished(revealed.value) && absorbedMatters(revealed)) {
        const raised = raiseForAbsorbed(revealed);
        if (raised.unverified) return raised;
        revealed = raised;
      }
      return confirmDust(present(revealed), root, env, budget);
    }
    if (lostGapOf(report) > D.precision + 4) {
      const abNeed = lostGapOf(report) + 48;
      if (abNeed > PRECISION_CAP) return certifyZero(report);
      const again = atPrecision(abNeed, root, env, budget);
      if (again.unverified) return again;
      if (vanished(again.value) && lostGapOf(again) > abNeed + 4) return certifyZero(again);
      const nonzeroResidue = residueParts(again).some((name) => !again.value[name].isZero());
      const revealed = nonzeroResidue ? settleResidue(again, root, env, budget) : again;
      if (revealed.unverified) return revealed;
      return confirmDust(present(revealed), root, env, budget);
    }
    return present(report);
  }
  let initial = report;
  // A cancellation in the dust band, about 10^-(digits-8), snaps to 0, and a later
  // ln reads that 0 as ln 0. exp(e − exp(exp(e−1))) − 1 is about 10^(−114): real at
  // 120 digits, and eml(1, that) is exp(exp(e−1)), not +∞. Rounding noise sits on the
  // last digit and still snaps after the raise, so a true ln 0 (e − ln(exp(e)), or an
  // exact 0 with no gap) stays the infinity it is. The gap is the one recorded on the
  // report (passState.lossGap for this pass).
  if (!zFinite(initial.value) && !initial.value.re.isNaN() && !initial.value.im.isNaN() && !initial.sawLead) {
    const gap = initial.lossGap ?? 0;
    const digits = initial.digits ?? D.precision;
    const need = gap + 48;
    if (gap > digits - 24 && need <= PRECISION_CAP) {
      const again = atPrecision(need, root, env, budget);
      if (!again.unverified && zFinite(again.value)) {
        const next = Math.min(PRECISION_CAP, need + 24);
        const check = next > need ? atPrecision(next, root, env, budget) : again;
        if (
          !check.unverified &&
          zFinite(check.value) &&
          !residueMoved(again.value.re, check.value.re) &&
          !residueMoved(again.value.im, check.value.im)
        ) {
          initial = again;
        }
      }
    }
  }
  if (absorbedMatters(initial)) {
    const raised = raiseForAbsorbed(initial);
    if (raised.unverified) return raised;
    initial = raised;
  }
  let settled = initial;
  if (hiddenComponent(initial.value)) {
    const digits = Math.min(PRECISION_CAP, Math.max(Math.max(initial.value.re.e, initial.value.im.e) + 48, (initial.digits ?? D.precision) + 32));
    if (digits > (initial.digits ?? D.precision)) settled = atPrecision(digits, root, env, budget);
  }
  if (settled.unverified) return settled;
  // A log just off the negative real axis lost its side (see passState.cutGap). Read again where
  // that side fits, or refuse once that would pass 480 digits. The read is not scrubbed:
  // a part it shows that the scrub would clear is not certified as 0. The K 35 word
  // 11111111E11E1EE1EEEEEE1E1E11E1E1EEE is −9×10^(−307) − i(π − 4×10^(−307)), not −iπ,
  // and the later refusal checks no longer retry once this pass has those digits.
  const sideGap = settled.cutGap ?? 0;
  if (sideGap > (settled.digits ?? D.precision) - 24) {
    const need = sideGap + 48;
    if (need > PRECISION_CAP) return certifyZero(settled);
    settled = atPrecision(need, root, env, budget, false);
    if (settled.unverified) return settled;
    const shown = scrubDust(settled.value);
    const hidden = (["re", "im"] as const).filter((name) => !settled.value[name].isZero() && shown[name].isZero());
    if (hidden.length > 0) {
      // A true tiny part holds still on a second reading, as in recoverTinyPart:
      // sqrt(−4 − 10^(−200) i) is 2.5×10^(−201) − 2i. Rounding moves, and is refused.
      const first = settled;
      const work = first.workExp !== undefined && Number.isFinite(first.workExp) ? first.workExp : 0;
      const past = Math.max(...hidden.map((name) => work - first.value[name].e + 36));
      const next = Math.min(PRECISION_CAP, Math.max(need + 24, past));
      if (next <= need) return certifyZero(first);
      let second: ExactReport;
      try {
        second = atPrecision(next, root, env, budget, false);
      } catch (err) {
        // Out of budget is never a certificate: see rethrowBudget.
        rethrowBudget(err);
        return certifyZero(first);
      }
      if (second.unverified || hidden.some((name) => residueMoved(first.value[name], second.value[name]))) return certifyZero(first);
      return first;
    }
  }
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
  // A deep non-snapped cancellation anywhere in the pass leaves fewer surviving digits
  // than D.precision (e.g. (1e200+0.5)−(1e200−0.5) leaves rounding dust at 10^−49, or
  // ln(noise) turns 10^−119 cancellation noise into −273). Raise so full D.precision
  // digits survive, and refuse if a near-total cancellation still moves with precision.
  if (!settled.sawLead && !agreesWithInteger(root, settled.value)) {
    const sl = settled.surviveLoss ?? 0;
    const digits = settled.digits ?? D.precision;
    const top = zFinite(settled.value) && !vanished(settled.value) ? exponentCeil(settled.value) : Number.POSITIVE_INFINITY;
    // Serial cancellations can lose digits across multiple gates even when no single gate
    // exceeds digits − 24: passState.firstBig − top >= digits − 24 signals that rounding noise from
    // an earlier large scale can reach the final result.
    const serialRisk = Number.isFinite(passState.firstBig) && Number.isFinite(top) && passState.firstBig - top >= digits - 24 && (sl > 8 || (settled.lossGap ?? 0) > 8);
    if (sl > digits - 24 || serialRisk) {
      const target = Math.min(PRECISION_CAP, Math.max(digits + 24, sl + D.precision));
      const probeDigits = target > digits ? target : Math.max(D.precision, digits - 24);
      if (probeDigits !== digits) {
        const other = atPrecision(probeDigits, root, env, budget);
        if (other.unverified) return other;
        const moved = residueMoved(settled.value.re, other.value.re) || residueMoved(settled.value.im, other.value.im);
        if (moved) {
          if (target <= digits || target >= PRECISION_CAP) return certifyZero(target > digits ? other : settled);
          const check = atPrecision(Math.min(PRECISION_CAP, target + 48), root, env, budget);
          if (check.unverified || residueMoved(other.value.re, check.value.re) || residueMoved(other.value.im, check.value.im)) {
            return certifyZero(other);
          }
          settled = check;
        } else if (target > digits && sl > digits - 24) {
          settled = other;
        }
      }
    } else if (sl > 8 && digits - sl < D.precision - 12 && digits < PRECISION_CAP) {
      const target = Math.min(PRECISION_CAP, sl + D.precision);
      if (target > digits) {
        const raised = atPrecision(target, root, env, budget);
        if (!raised.unverified) settled = raised;
      }
    }
  }
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

/**
 * The second-order term of exp(x) and cos(t), as a decade below 1, when it is rounded into the
 * leading 1: x^2 / 2 for the real part, t^2 / 2 for the angle. Null when it still fits in
 * D.precision - 12 digits. The order-1 term of a tiny real part is recorded where this is called.
 * Higher orders are not tracked: they sit below this one by as many decades again.
 */
function absorbedOrder(turn: Z, realIsNoise: boolean): { gap: number; term: number } | null {
  // Fewer than 12 digits of the term survive past -(P - 12), so it is counted as lost.
  const limit = -(D.precision - 12);
  let best: { gap: number; term: number } | null = null;
  const scan = (part: Decimal): void => {
    if (!part.isFinite() || part.isZero() || part.e >= 0 || 2 * part.e > limit + 1) return;
    const term = part.abs().pow(2).div(2).e;
    if (term < limit && (best === null || term > best.term)) best = { gap: -term, term };
  };
  if (!realIsNoise) scan(turn.re);
  scan(turn.im);
  return best;
}

/** The larger of the two absorbed gaps, on the scale where > digits + 4 means lost (a second-order term is lost from digits - 12, so it counts 16 more). */
function lostGapOf(r: ExactReport): number {
  return Math.max(r.absorbRe ?? 0, (r.absorb2 ?? 0) > 0 ? (r.absorb2 ?? 0) + 16 : 0);
}

/** The real part of an exp argument below the noise floor of the cancellation that made it. */
function realNoise(v: Z, made: Work | undefined): boolean {
  if (!made || !Number.isFinite(made.re) || !v.re.isFinite() || v.re.isZero()) return false;
  return v.re.abs().lt(residueFloor(made.re, D.precision));
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
  const surviveLossOf = new Map<Node, number>();
  const absorbOf = new Map<Node, number>();
  const absorbReOf = new Map<Node, number>();
  const absorb2Of = new Map<Node, number>();
  const absorbReTermOf = new Map<Node, number>();
  const absorbExposedOf = new Map<Node, boolean>();
  const cutOf = new Map<Node, number>();
  const rangeLostOf = new Map<Node, boolean>();
  const underflowLostOf = new Map<Node, boolean>();
  const cutImOf = new Map<Node, boolean>();
  const tinyOf = new Map<Node, number>();
  const tinyPartsOf = new Map<Node, TinyParts>();
  const leadOf = new Map<Node, boolean>();
  const bigOf = new Map<Node, number>();
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  let sawLead = false;
  let absorbExposed = false;
  resetWalkTallies();
  const risk = new Map<Node, GateRisk>();
  let steps = 0;
  // The probe's lifted values must not reach the caches.
  const probing = probe !== null;
  const nocache = cacheOff() || probing;
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
      const leaf = lifted(z(n.value.re, n.value.im));
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
      const boundZ = lifted(asZ(bound));
      memo.set(n, boundZ);
      noteSeen(boundZ);
      why.set(n, null);
      logged.set(n, false);
      continue;
    }
    if (!n.a || !n.b) throw new EmlError("Could not evaluate this circuit.");
    // A huge integer kept beside a non-integer: its gates hold only the integer, so
    // evaluate the remembered sum itself. (10^400 + i)/7 was refused for this.
    // A rebuilt circuit has no such record and is still refused by hidesBeside.
    const beside = besideSumOf(n);
    if (beside) {
      const kids = [beside.huge, beside.other];
      if (!frame.seen) {
        if (visiting.has(n)) throw new EmlError("Could not evaluate this circuit.");
        visiting.add(n);
        stack.push({ n, seen: true });
        for (const kid of kids) stack.push({ n: kid, seen: false });
        continue;
      }
      visiting.delete(n);
      const h = memo.get(beside.huge);
      const w = memo.get(beside.other);
      if (!h || !w) throw new EmlError("Could not evaluate this circuit.");
      const op = beside.op === "add" ? (x: Decimal, y: Decimal) => x.add(y) : (x: Decimal, y: Decimal) => x.sub(y);
      const value = lifted({ re: op(h.re, w.re), im: op(h.im, w.im) }, h, w);
      // A real part rounded away beside the integer is recorded like any other gate's.
      const outerAbsorbRe = passState.absorbRe;
      const outerAbsorbReTerm = passState.absorbReTerm;
      const outerAbsorb = passState.absorbIm;
      passState.absorbRe = 0;
      passState.absorbReTerm = Number.NEGATIVE_INFINITY;
      passState.absorbIm = 0;
      // At the root the sum is the answer, rounded once; no later gate mixes its parts.
      const atRoot = n === root;
      if (!atRoot) {
        noteAbsorbRe(h.re, w.re, value.re, false, false);
        noteAbsorb(h.im, w.im, value.im);
      }
      const own = { absorbRe: passState.absorbRe, absorbReTerm: passState.absorbReTerm, absorbIm: passState.absorbIm };
      // The small operand sits far below the integer. A later exp or ln mixes the parts,
      // and an angle of 10^(−400) beside ±π is gone at 120 or 240 digits: (10^400 + i)·2
      // printed 2.000…00442i. Ask for digits that span the gap, as a log near the cut does
      // (see passState.cutGap), and past 480 digits the result is refused, as before.
      let ownGap = 0;
      const top = Math.max(...[value.re, value.im].filter((x) => x.isFinite() && !x.isZero()).map((x) => x.e), Number.NEGATIVE_INFINITY);
      for (const part of [w.re, w.im]) {
        if (atRoot || !part.isFinite() || part.isZero() || !Number.isFinite(top)) continue;
        const gap = top - part.e;
        if (gap > D.precision - 24 && gap > ownGap) ownGap = gap;
      }
      if (ownGap > passState.cutGap) passState.cutGap = ownGap;
      passState.absorbRe = Math.max(outerAbsorbRe, passState.absorbRe);
      passState.absorbReTerm = Math.max(outerAbsorbReTerm, passState.absorbReTerm);
      passState.absorbIm = Math.max(outerAbsorb, passState.absorbIm);
      const maxOf = (map: Map<Node, number>, own0: number) => Math.max(own0, ...kids.map((k) => map.get(k) ?? 0));
      const anyOf = (map: Map<Node, boolean>) => kids.some((k) => map.get(k) === true);
      lossOf.set(n, maxOf(lossOf, 0));
      surviveLossOf.set(n, maxOf(surviveLossOf, 0));
      absorbOf.set(n, maxOf(absorbOf, own.absorbIm));
      absorbReOf.set(n, maxOf(absorbReOf, own.absorbRe));
      absorb2Of.set(n, maxOf(absorb2Of, 0));
      absorbReTermOf.set(n, Math.max(own.absorbReTerm, ...kids.map((k) => absorbReTermOf.get(k) ?? Number.NEGATIVE_INFINITY)));
      absorbExposedOf.set(n, anyOf(absorbExposedOf));
      cutOf.set(n, maxOf(cutOf, ownGap));
      rangeLostOf.set(n, anyOf(rangeLostOf));
      underflowLostOf.set(n, anyOf(underflowLostOf));
      cutImOf.set(n, anyOf(cutImOf));
      tinyOf.set(n, Math.min(exponentFloor(value), ...kids.map((k) => tinyOf.get(k) ?? exponentFloor(memo.get(k) as Z))));
      tinyPartsOf.set(n, minParts(partsFloor(value), ...kids.map((k) => tinyPartsOf.get(k) ?? partsFloor(memo.get(k) as Z))));
      leadOf.set(n, anyOf(leadOf));
      bigOf.set(n, Math.max(exponentCeil(value), ...kids.map((k) => bigOf.get(k) ?? exponentCeil(memo.get(k) as Z))));
      const kw = kids.map((k) => work.get(k));
      work.set(n, {
        all: Math.max(...kw.map((x) => x?.all ?? Number.NEGATIVE_INFINITY)),
        re: Math.max(...kw.map((x) => x?.re ?? Number.NEGATIVE_INFINITY)),
        im: Math.max(...kw.map((x) => x?.im ?? Number.NEGATIVE_INFINITY)),
        hits: mergeHits(kw[0]?.hits, kw[1]?.hits, []),
      });
      const kidLog = kids.some((k) => logged.get(k) === true);
      let singular: string | null = null;
      if (value.re.isNaN() || value.im.isNaN()) singular = SINGULAR_INDET;
      else if (!zFinite(value)) singular = why.get(beside.huge) || why.get(beside.other) || SINGULAR_NONFINITE;
      memo.set(n, value);
      noteSeen(value);
      why.set(n, singular);
      logged.set(n, kidLog);
      hasVarOf.set(n, kids.some((k) => k.type === "var" || hasVarOf.get(k) === true));
      continue;
    }
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
      if (hit.loss > passState.lossGap) passState.lossGap = hit.loss;
      if (hit.surviveLoss > passState.surviveLoss) passState.surviveLoss = hit.surviveLoss;
      surviveLossOf.set(n, hit.surviveLoss);
      if (hit.absorb > passState.absorbIm) passState.absorbIm = hit.absorb;
      absorbOf.set(n, hit.absorb);
      if (hit.absorbRe > passState.absorbRe) passState.absorbRe = hit.absorbRe;
      if (hit.absorb2 > passState.absorb2) passState.absorb2 = hit.absorb2;
      absorb2Of.set(n, hit.absorb2);
      if (hit.absorbReTerm > passState.absorbReTerm) passState.absorbReTerm = hit.absorbReTerm;
      if (hit.absorbExposed) absorbExposed = true;
      absorbReOf.set(n, hit.absorbRe);
      absorbReTermOf.set(n, hit.absorbReTerm);
      absorbExposedOf.set(n, hit.absorbExposed);
      if (hit.cut > passState.cutGap) passState.cutGap = hit.cut;
      cutOf.set(n, hit.cut);
      if (hit.rangeLost) passState.rangeLost = true;
      rangeLostOf.set(n, hit.rangeLost);
      if (hit.underflowLost) passState.underflowLost = true;
      underflowLostOf.set(n, hit.underflowLost);
      cutImOf.set(n, hit.cutIm);
      if (hit.tiniest < passState.tiniest) passState.tiniest = hit.tiniest;
      if (hit.tinyParts.re < passState.tinyRe) passState.tinyRe = hit.tinyParts.re;
      if (hit.tinyParts.im < passState.tinyIm) passState.tinyIm = hit.tinyParts.im;
      if (hit.lead) sawLead = true;
      if (hit.big > passState.biggest) passState.biggest = hit.big;
      bigOf.set(n, hit.big);
      lossOf.set(n, hit.loss);
      tinyOf.set(n, hit.tiniest);
      tinyPartsOf.set(n, hit.tinyParts);
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
    passState.emlWork = Number.NEGATIVE_INFINITY;
    passState.emlWorkRe = Number.NEGATIVE_INFINITY;
    passState.emlWorkIm = Number.NEGATIVE_INFINITY;
    passState.gateHits = [];
    // sin, cos, and tan of ±∞ are undefined. The note travels with the packed circuit.
    // The exp formula otherwise returns an infinity.
    // The argument may sit under a cached intermediate, so this walk never
    // visits it. The earlier evaluation stored it in the pure cache.
    const angleValue = angle ? (memo.get(angle) ?? cache.get(angle)?.value) : undefined;
    const angleInfinite = !!angleValue && (!angleValue.re.isFinite() || !angleValue.im.isFinite());
    const outerLoss = passState.lossGap;
    passState.lossGap = 0;
    const outerSurviveLoss = passState.surviveLoss;
    passState.surviveLoss = 0;
    const outerAbsorb = passState.absorbIm;
    passState.absorbIm = 0;
    const outerAbsorbRe = passState.absorbRe;
    passState.absorbRe = 0;
    const outerAbsorb2 = passState.absorb2;
    passState.absorb2 = 0;
    const outerAbsorbReTerm = passState.absorbReTerm;
    passState.absorbReTerm = Number.NEGATIVE_INFINITY;
    // passState.tiniest also takes a decade past the decimal range from expZ; keep this gate's
    // own share for the cache, so a hit still refuses exp(−10^20).
    const outerTiny = passState.tiniest;
    passState.tiniest = 0;
    const outerCut = passState.cutGap;
    passState.cutGap = 0;
    const outerRangeLost: boolean = passState.rangeLost;
    passState.rangeLost = false;
    const outerUnderflowLost: boolean = passState.underflowLost;
    passState.underflowLost = false;
    // An angle under the rounding noise of the gates that produced it is that
    // noise, and turns as 0 (cosSin no longer snaps a tiny angle to the axis).
    const turn = angleNoise(a, work.get(n.a)) ? { re: a.re, im: ZERO } : a;
    const aNoisy = realNoise(turn, work.get(n.a));
    const bNoisy = realNoise(b, work.get(n.b));
    // Record when exp(turn.re) silently absorbs a genuine tiny real term into 1.
    // Strictly below −(D.precision + 1) excludes 1-ulp rounding dust near −D.precision.
    if (!angleInfinite && turn.re.isFinite() && !turn.re.isZero() && turn.re.e < -(D.precision + 1)) {
      const gap = -turn.re.e;
      if (gap > passState.absorbRe) passState.absorbRe = gap;
      if (turn.re.e > passState.absorbReTerm) passState.absorbReTerm = turn.re.e;
    }
    // exp(x) = 1 + x + x^2/2 + ..., and cos(t) = 1 - t^2/2 + ..., round to P digits. A higher-order
    // term below 10^(-P) is gone from the 1 even when x itself is not. exp(-10^(-200)) - 1 +
    // 10^(-200) kept an exact 0 at 249 digits, where the answer is 5e-401.
    if (!angleInfinite) {
      const hidden = absorbedOrder(turn, aNoisy);
      if (hidden !== null) {
        if (hidden.gap > passState.absorb2) passState.absorb2 = hidden.gap;
      }
    }
    const value = lifted(
      angleInfinite ? { re: NAN, im: NAN } : exactEml(turn, b, aNoisy, bNoisy, cutImOf.get(n.a) === true, cutImOf.get(n.b) === true),
      a,
      b,
    );
    const subCutIm = !angleInfinite && passState.gateCutIm;
    cutImOf.set(n, subCutIm);
    const subRangeLost = passState.rangeLost || rangeLostOf.get(n.a) === true || rangeLostOf.get(n.b) === true;
    passState.rangeLost = outerRangeLost || subRangeLost;
    rangeLostOf.set(n, subRangeLost);
    const subUnderflowLost = passState.underflowLost || underflowLostOf.get(n.a) === true || underflowLostOf.get(n.b) === true;
    passState.underflowLost = outerUnderflowLost || subUnderflowLost;
    underflowLostOf.set(n, subUnderflowLost);
    const ownLoss = passState.lossGap;
    passState.lossGap = Math.max(outerLoss, ownLoss);
    const ownSurviveLoss = passState.surviveLoss;
    passState.surviveLoss = Math.max(outerSurviveLoss, ownSurviveLoss);
    const subSurviveLoss = Math.max(ownSurviveLoss, surviveLossOf.get(n.a) ?? 0, surviveLossOf.get(n.b) ?? 0);
    surviveLossOf.set(n, subSurviveLoss);
    const subAbsorb = Math.max(passState.absorbIm, absorbOf.get(n.a) ?? 0, absorbOf.get(n.b) ?? 0);
    passState.absorbIm = Math.max(outerAbsorb, passState.absorbIm);
    absorbOf.set(n, subAbsorb);
    const subAbsorbRe = Math.max(passState.absorbRe, absorbReOf.get(n.a) ?? 0, absorbReOf.get(n.b) ?? 0);
    const subAbsorbReTerm = Math.max(passState.absorbReTerm, absorbReTermOf.get(n.a) ?? Number.NEGATIVE_INFINITY, absorbReTermOf.get(n.b) ?? Number.NEGATIVE_INFINITY);
    // A gate that outputs 0 from a subtree with an absorbed real term (e.g. ln(1 + 1e-200) -> 0
    // inside (1 + 1e-200)^1e200, or (1 + 1e-200) - 1 -> 0) exposed the absorbed term.
    const ownAbsorbExposed = zZero(value) && Math.max(absorbReOf.get(n.a) ?? 0, absorbReOf.get(n.b) ?? 0) > D.precision + 1;
    const subAbsorbExposed = ownAbsorbExposed || absorbExposedOf.get(n.a) === true || absorbExposedOf.get(n.b) === true;
    if (subAbsorbExposed) absorbExposed = true;
    const subAbsorb2 = Math.max(passState.absorb2, absorb2Of.get(n.a) ?? 0, absorb2Of.get(n.b) ?? 0);
    passState.absorb2 = Math.max(outerAbsorb2, passState.absorb2);
    absorb2Of.set(n, subAbsorb2);
    passState.absorbRe = Math.max(outerAbsorbRe, passState.absorbRe);
    passState.absorbReTerm = Math.max(outerAbsorbReTerm, passState.absorbReTerm);
    absorbReOf.set(n, subAbsorbRe);
    absorbReTermOf.set(n, subAbsorbReTerm);
    absorbExposedOf.set(n, subAbsorbExposed);
    const subCut = Math.max(passState.cutGap, cutOf.get(n.a) ?? 0, cutOf.get(n.b) ?? 0);
    passState.cutGap = Math.max(outerCut, passState.cutGap);
    cutOf.set(n, subCut);
    const subLoss = Math.max(ownLoss, lossOf.get(n.a) ?? 0, lossOf.get(n.b) ?? 0);
    const gateTiny = passState.tiniest;
    passState.tiniest = Math.min(outerTiny, gateTiny);
    const subTiny = Math.min(gateTiny, exponentFloor(value), tinyOf.get(n.a) ?? exponentFloor(a), tinyOf.get(n.b) ?? exponentFloor(b));
    const subLead = isSeriesShortcut(n) || leadOf.get(n.a) === true || leadOf.get(n.b) === true;
    lossOf.set(n, subLoss);
    tinyOf.set(n, subTiny);
    const subTinyParts = minParts(partsFloor(value), tinyPartsOf.get(n.a) ?? partsFloor(a), tinyPartsOf.get(n.b) ?? partsFloor(b));
    tinyPartsOf.set(n, subTinyParts);
    leadOf.set(n, subLead);
    const subBig = Math.max(exponentCeil(value), bigOf.get(n.a) ?? exponentCeil(a), bigOf.get(n.b) ?? exponentCeil(b));
    bigOf.set(n, subBig);
    const ownHits = passState.gateHits;
    const shell = inScaledShell(n);
    // A short lift never reaches 1, so its cancellation is the result's rounding.
    // e/e does reach 1 and still leaves that residual; an ordinary sum does not.
    const liftCounts = !shell || shortLift(passState.emlWork) || liftedResidue(passState.emlWork, ownHits, value);
    const own: Work = liftCounts
      ? { all: passState.emlWork, re: passState.emlWorkRe, im: passState.emlWorkIm, hits: ownHits }
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
      liftGap: angleInfinite ? 0 : Math.max(isLiftedCombine(n) ? liftedGap(a, b, value) : 0, trigGap(turn)),
      trigGap: angleInfinite ? 0 : angleDecades(turn),
    };
    risk.set(n, gate);
    if (probing) continue;
    if (!(n.a.type === "var" || hasVarOf.get(n.a) === true || n.b.type === "var" || hasVarOf.get(n.b) === true)) store.set(n, gate);
    const varA = n.a.type === "var" || hasVarOf.get(n.a) === true;
    const varB = n.b.type === "var" || hasVarOf.get(n.b) === true;
    hasVarOf.set(n, varA || varB);
    if (!varA && !varB) cache.set(n, { value, why: singular, logged: childLog, work: nodeWork, loss: subLoss, surviveLoss: subSurviveLoss, tiniest: subTiny, tinyParts: subTinyParts, lead: subLead, big: subBig, absorb: subAbsorb, absorbRe: subAbsorbRe, absorb2: subAbsorb2, absorbReTerm: subAbsorbReTerm, absorbExposed: subAbsorbExposed, cut: subCut, rangeLost: subRangeLost, underflowLost: subUnderflowLost, cutIm: subCutIm });
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
    absorbIm: passState.absorbIm,
    absorbRe: passState.absorbRe,
    absorb2: passState.absorb2,
    absorbReTerm: passState.absorbReTerm,
    absorbExposed,
    lossGap: passState.lossGap,
    surviveLoss: passState.surviveLoss,
    cutGap: passState.cutGap,
    nearCut: cutImOf.get(root) === true && out.re.isFinite() && out.im.isFinite() && nearCut(out.im),
    rangeLost: rangeLostOf.get(root) === true,
    underflowLost: underflowLostOf.get(root) === true,
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

/** A finite exact component that overflows float64 to ±Infinity. exp(800) and 10^400 are examples. */
export function exactOverflowsFloat(v: Z): boolean {
  const n = exactToFloat(v);
  const over = (part: Decimal, num: number) => part.isFinite() && !Number.isFinite(num);
  return over(v.re, n.re) || over(v.im, n.im);
}

function formatDec(d: Decimal): string {
  if (d.isNaN()) return "undefined";
  if (!d.isFinite()) return d.isNeg() ? "−∞" : "∞";
  if (d.isZero()) return d.isNeg() ? "−0" : "0";
  const sign = d.isNeg() ? "−" : "";
  const abs = d.abs();
  if (abs.lt("1e16") && exactInteger(abs)) return sign + abs.toFixed(0);
  // Fixed notation has twelve places, so below 10^(−6) it shows six digits or fewer
  // (0.000000271828, where float shows 2.718282×10^−7). Scientific keeps twelve.
  if (abs.lt("1e16") && abs.gte("1e-6")) {
    const shown = new D(abs.toFixed(12));
    const gap = abs.sub(shown).abs();
    const intGap = abs.sub(abs.round()).abs();
    const dust = new D(10).pow(-(D.precision - 24));
    // Twelve digits hide 0.5 − 10^(−72) and 1 − 10^(−72). Print the first digits of that tail.
    // Only when the 12 places look rounder than the value (trailing zeros dropped): when
    // places 13–14 merely happen to be 0, as in 0.019930868458|0096, twelve places are the
    // usual display, not a hidden tail. A twelfth place of 0 is common (one value in ten),
    // and 0.73105857863|000488 is sigma(1), so a value with only that one trailing zero is
    // a hidden tail only when the rest is below 10^(−17), as in cosh(0.00005i) =
    // 0.99999999875|00000000026. Three or more trailing zeros (0.5 − 10^(−16)) are rare
    // enough for a tail under 10^(−14).
    const trimmed = abs.toFixed(12).replace(/(\.\d*?)0+$/, "$1").replace(/\.$/, "");
    const places = (trimmed.split(".")[1] ?? "").length;
    const hiddenTail = gap.gt(dust) && ((gap.e < -14 && places <= 9) || (gap.e < -17 && places <= 11));
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
  // The coefficient is printed as the real part would be: (1 + 10^(−12))i and
  // (1 − 10^(−72))i keep their digits. A 10^(−12) neighbourhood of 1 printed both as i.
  const text = formatDec(d.abs());
  return text === "1" ? `${sign}i` : `${sign}${text}i`;
}

function formatFullInteger(d: Decimal): string {
  const sign = d.isNeg() ? "−" : "";
  const saved = D.precision;
  const need = Math.max(saved, d.abs().e + 2);
  if (need > saved) D.set({ precision: need });
  try {
    return sign + d.abs().toFixed(0);
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

// beyondFloatBound lives in ./float-bound so the screen can load it without decimal.js.
export { beyondFloatBound } from "./float-bound";

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
