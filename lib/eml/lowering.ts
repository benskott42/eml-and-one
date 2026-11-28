import { E, ONE, ROT_IM_MAX, ROT_IM_MIN, input, notePrecision, onCircuitIsolate, type Node } from "./node";
import { applyProgram, programNode } from "./programs";
import { builtSubOf, builtSumOf, clearProvenInt, decadeOf, dependsOnUnverified, factsOf, inScaledShell, intDecade, intProductFits, isExactUnsure, isLiftedCombine, isLostTiny, isMarkedExactInt, isNonfiniteNode, isSeriesShortcut, isTwoScaled, isUnverified, learn, markExactUnsure, markInfiniteSource, markMaybeInfinite, markSeriesShortcut, markTwoScaled, markUnverified, mayBeInfinite, noteBesideSum, noteBuiltFrom, noteBuiltSub, noteBuiltSum, noteDecade, noteLiftedCombine, noteLostTiny, noteMarkedExactInt, noteNonfinite, noteOverflow, noteProvenInt, noteScaledShell, provenInteger, recordedPoleSign, resetExpressionFacts } from "./facts";

export { decadeOf, inScaledShell, isLiftedCombine, isLostTiny, isMarkedExactInt, isNonfiniteNode, isTwoScaled, markInfiniteSource, markMaybeInfinite, markTwoScaled, mayBeInfinite, noteDecade, noteLiftedCombine, noteLostTiny, noteNonfinite, noteOverflow, noteScaledShell };

/**
 * Structural ranges for subtraction and the exponential.
 *
 * A float is not a mathematical point. Endpoints are rounded outward by one
 * ulp, so a later cancellation is an interval, not a proof that the value is
 * zero. Zero is folded only when the two operands are the same finite node or the
 * same constructed integer. Infinity is not interned, and ∞ − ∞ is not zero.
 *
 * eml(ln a, exp b) = a − b only while Im(b) is at least 10^(−3) inside
 * (−π, π) and the real parts are moderate. A known subtrahend inside the
 * float strip uses unscaled rotSub. An unknown range, or a value outside
 * that strip, uses k · rotSub(a/k, b/k). The code's k is 1 + √(b²), built
 * from b for a sum as well as a difference. The log inside that square root
 * has imaginary part in [−π, π] on this branch, so the root has nonnegative
 * real part and Re k ≥ 1. Another branch of that log need not keep k off
 * zero. rotSub(u, v) = raw(c·raw(u, v), c·raw(v, v)) / c.
 * c is the K 21 word for +iπ, so the unscaled rotation is K 131 with 34 eml
 * nodes. The scale is part of the same circuit: dividing by k brings a huge
 * subtrahend back into the range where exp is finite, and multiplying by k
 * puts the difference back. A known large real away from the cut still
 * scales by exp(n). An unproven subtrahend is never a divisor by itself.
 * Corless and Jeffrey define the unwinding number in "The unwinding number",
 * ACM SIGSAM Bulletin 30(2):28–35, 1996, doi:10.1145/235699.235705.
 * The rotation above is this calculator's construction. It uses the unwinding
 * number; the rotation itself is not in that paper. Inside the strip, raw(b, b)
 * is 0, so the next multiplication logs 0. rotSub needs ln 0 = −∞ for almost
 * every input, not only when exp(b) underflows.
 * Unscaled float64 is exact to a few ulps on (−71π, 71π). The top end
 * underflows: [73π, 75π) is degraded, and past 75π the exponential is 0.
 *
 * |exp(x)| is at most e^(sup Re x) even when the argument is complex. A
 * logarithm that is not a point has imaginary part in the closed interval
 * [−π, π]. A product or exponential with no real bound stays unknown.
 */

type Iv = { lo: number; hi: number };

export type Range = {
  re: Iv | null;
  im: Iv | null;
};

const UNKNOWN: Range = { re: null, im: null };
const ranges = new WeakMap<Node, Range>();

onCircuitIsolate(() => {
  resetExpressionFacts();
  negZero = undefined;
  minusOne = undefined;
  two = undefined;
  zero = undefined;
  turn = undefined;
  ints.clear();
  powersOfTen.clear();
});

const CUT_MARGIN = 1e-3;
/**
 * The short negation and the axis check stay off the branch cut by this much,
 * and they refuse a real part past 500. Beyond that the exponential in the
 * short word overflows, so the caller uses the scaled circuit.
 */
const REAL_CAP = 500;
/**
 * Below this magnitude the short add and the short sub lose digits: their
 * absolute error is about 10^(−16). Both operations lift by the same power of ten.
 */
const TINY_MAG = 1e-4;
/**
 * The short identity is faithful below this magnitude. At and above it, add and
 * sub scale so the exponential stays finite.
 */
const SHORT_MAG = 20;
/**
 * Unscaled rotSub overflows once the real part reaches about 700.
 * A known value past that is scaled before it is rotated.
 */
const ROT_REAL_MAX = 700;
/**
 * exp(n) for a known large real. exp(800) already overflows float64,
 * so the scale stops there and the result is flagged out of range.
 */
const EXP_SCALE_MAX = 800;
/**
 * exp(re) underflows to 0 in float64 once re is below about −700,
 * because ln(2^(−1022)) ≈ −708. A finite real part past that is a known
 * zero for choosing a circuit. The node itself still evaluates.
 */
const EXP_UNDERFLOW_RE = -700;
/** 10^308 is not a finite float64. Add and sub share this lift. */
const TEN_POW_MAX = 307;
const SAFE = BigInt(Number.MAX_SAFE_INTEGER);

function keepsInteger(range: Range, value: bigint): boolean {
  if (!range.im || range.im.lo !== 0 || range.im.hi !== 0 || !range.re) return false;
  const approx = Number(value);
  if (!Number.isFinite(approx)) return false;
  return range.re.lo <= approx && range.re.hi >= approx;
}

function setRange(node: Node, range: Range, int?: bigint): Node {
  if (int === undefined && node.type !== "one") {
    const previous = provenInteger(node);
    if (previous !== undefined && !keepsInteger(range, previous)) clearProvenInt(node);
  }
  ranges.set(node, range);
  if (int !== undefined) noteProvenInt(node, int);
  return node;
}

export function rangeOf(node: Node): Range {
  if (node.type === "one") return { re: { lo: 1, hi: 1 }, im: { lo: 0, hi: 0 } };
  const hit = ranges.get(node);
  if (hit) return hit;
  if (node.type === "input") {
    const { re, im } = node.value;
    if (Number.isFinite(re) && Number.isFinite(im)) return point(re, im);
  }
  return UNKNOWN;
}

/**
 * arctan of a real off zero stays real and keeps that sign, inside (−π/2, π/2).
 * The closed form does not record a range, so a later 0·arctan could not see it.
 */
export function noteRealArctan(node: Node, arg: Node): Node {
  const range = rangeOf(arg);
  if (!range.re || !range.im || range.im.lo !== 0 || range.im.hi !== 0) return node;
  if (!Number.isFinite(range.re.lo) || !Number.isFinite(range.re.hi)) return node;
  const pad = 1e-12;
  if (range.re.hi < 0) {
    const far = Math.atan(range.re.lo);
    const near = Math.atan(range.re.hi);
    const hi = Math.min(near + pad, -Number.MIN_VALUE);
    const lo = far - pad;
    if (!(hi < 0) || !Number.isFinite(lo)) return node;
    return setRange(node, { re: { lo: Math.min(lo, hi), hi }, im: { lo: 0, hi: 0 } });
  }
  if (range.re.lo > 0) {
    const near = Math.atan(range.re.lo);
    const far = Math.atan(range.re.hi);
    const lo = Math.max(near - pad, Number.MIN_VALUE);
    const hi = far + pad;
    if (!(lo > 0) || !Number.isFinite(hi)) return node;
    return setRange(node, { re: { lo, hi: Math.max(lo, hi) }, im: { lo: 0, hi: 0 } });
  }
  return node;
}

/**
 * A real image of a narrow real argument, with the sign Math.f records.
 * cos(1) is built as a complex exponential and its box crosses zero, so
 * 0·cos(1) could not see that cos(1) is positive. The pad is one ulp of
 * slack plus the Lipschitz bound over the argument's width. A wide argument,
 * or a value that the pad reaches across zero, keeps the box it had.
 */
export function noteRealImage(node: Node, arg: Node, fn: (x: number) => number, lipschitz: number, side: "any" | "negative" = "any"): Node {
  if (isUnverified(node) || isExactUnsure(node)) return node;
  // Keep a range that already decides the sign, and keep a point. A slack
  // interval in place of cos(0)'s box made acos(cos(0)) unverified.
  const existing = rangeOf(node);
  if (existing.re && existing.im && existing.im.lo === 0 && existing.im.hi === 0 && Number.isFinite(existing.re.lo) && Number.isFinite(existing.re.hi)) {
    if (existing.re.lo === existing.re.hi || existing.re.lo > 0 || existing.re.hi < 0) return node;
  }
  const range = rangeOf(arg);
  if (!range.re || !range.im || range.im.lo !== 0 || range.im.hi !== 0) return node;
  const lo = range.re.lo;
  const hi = range.re.hi;
  if (!Number.isFinite(lo) || !Number.isFinite(hi) || hi < lo) return node;
  const width = hi - lo;
  if (width > 1e-4) return node;
  const mid = (lo + hi) / 2;
  // Past this, a float evaluation of sin or cos no longer has a trustworthy sign.
  if (Math.abs(mid) > 1e8) return node;
  const y = fn(mid);
  if (!Number.isFinite(y) || !Number.isFinite(lipschitz) || lipschitz < 0) return node;
  const slack = width * lipschitz + 1e-12;
  if (y > slack) {
    // A positive image is a new sign. ln(2.5)·0 then certifies a zero the
    // product word prints with the other sign, so a caller can ask for the
    // negative image only.
    if (side === "negative") return node;
    const left = y - slack;
    if (!(left > 0)) return node;
    return setRange(node, { re: { lo: left, hi: y + slack }, im: { lo: 0, hi: 0 } });
  }
  if (y < -slack) {
    const right = y + slack;
    if (!(right < 0)) return node;
    return setRange(node, { re: { lo: y - slack, hi: right }, im: { lo: 0, hi: 0 } });
  }
  return node;
}

function ulp(x: number): number {
  const ax = Math.abs(x);
  if (!(ax > 0) || !Number.isFinite(ax)) return 0;
  return 2 ** (Math.floor(Math.log2(ax)) - 52);
}

/**
 * A product of two nonzero floats that underflowed to 0. That 0 is not the integer 0:
 * (10^(−200))² was the point 0, so 0^((10^(−200))²) folded to 1 and
 * (10^(−170))²·10^300 to a certified 0. The true product is below 2^(−1074).
 */
function underflowed(x: number, y: number, product: number): boolean {
  return x !== 0 && y !== 0 && product === 0;
}

/** The interval grown by `pad` on each side. */
function pad(iv: Iv, by: number): Iv {
  return { lo: iv.lo - by, hi: iv.hi + by };
}

function outLo(x: number): number {
  if (!Number.isFinite(x)) return x;
  return x - ulp(x);
}

function outHi(x: number): number {
  if (!Number.isFinite(x)) return x;
  return x + ulp(x);
}

function widen(lo: number, hi: number): Iv | null {
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) return null;
  const a = Math.min(lo, hi);
  const b = Math.max(lo, hi);
  return { lo: outLo(a), hi: outHi(b) };
}

/** A tagged float. Explicit tags stay exact; arithmetic widens on the way out. */
export function point(re: number, im = 0): Range {
  if (!Number.isFinite(re) || !Number.isFinite(im)) return UNKNOWN;
  return { re: { lo: re, hi: re }, im: { lo: im, hi: im } };
}

function isPoint(range: Range): boolean {
  return !!range.re && !!range.im && range.re.lo === range.re.hi && range.im.lo === range.im.hi;
}

function safeInt(value: bigint): boolean {
  return value >= -SAFE && value <= SAFE;
}

function intRange(value: bigint): Range {
  if (safeInt(value)) {
    const n = Number(value);
    return { re: { lo: n, hi: n }, im: { lo: 0, hi: 0 } };
  }
  const approx = Number(value);
  const re = Number.isFinite(approx) ? widen(approx, approx) : null;
  return { re, im: { lo: 0, hi: 0 } };
}

function attachInt(node: Node, value: bigint): Node {
  return setRange(node, intRange(value), value);
}

export function tagValue(node: Node, value: { re: number; im: number }): Node {
  if (!Number.isFinite(value.re) || !Number.isFinite(value.im)) return node;
  return setRange(node, point(value.re, value.im === 0 ? 0 : value.im));
}

export function tagReal(node: Node, re: number): Node {
  const range = point(re, 0);
  const existing = provenInteger(node);
  const int = existing !== undefined ? existing : Number.isInteger(re) && Number.isSafeInteger(re) ? BigInt(re) : undefined;
  return setRange(node, range, int);
}

export function tagInteger(node: Node, value: bigint): Node {
  return attachInt(node, value);
}

export function knownValue(node: Node): { re: number; im: number } | null {
  const int = provenInteger(node);
  if (int !== undefined && safeInt(int)) return { re: Number(int), im: 0 };
  const range = rangeOf(node);
  if (!isPoint(range) || !range.re || !range.im) return null;
  return { re: range.re.lo, im: range.im.lo };
}

function absEnd(iv: Iv | null): number | null {
  if (!iv || !Number.isFinite(iv.lo) || !Number.isFinite(iv.hi)) return null;
  return Math.max(Math.abs(iv.lo), Math.abs(iv.hi));
}

function extent(node: Node): { re: number; im: number } | null {
  const range = rangeOf(node);
  const re = absEnd(range.re);
  const im = absEnd(range.im);
  if (re === null || im === null) return null;
  return { re, im };
}

function maxMag(a: Node, b: Node): number | null {
  const ea = extent(a);
  const eb = extent(b);
  if (!ea || !eb) return null;
  return Math.max(ea.re, ea.im, eb.re, eb.im);
}

/** True when the imaginary interval meets the 10^(−3) neighborhood of ±π. */
function nearCut(range: Range): boolean {
  if (!range.im) return true;
  const edge = Math.PI - CUT_MARGIN;
  return range.im.hi > edge || range.im.lo < -edge;
}

function isNegInf(range: Range): boolean {
  return !!range.re && range.re.lo === -Infinity && range.re.hi === -Infinity && !!range.im && range.im.lo === 0 && range.im.hi === 0;
}

/**
 * |exp(x)| ≤ exp(sup Re x). A real argument stays real and positive.
 * Anything else is the outward box [−M, M] × [−M, M], or unknown when the
 * real part is unbounded or the exponential overflows float64.
 */
function expRange(range: Range): Range {
  if (!range.re) return UNKNOWN;
  const lo = Math.exp(range.re.lo);
  const hi = Math.exp(range.re.hi);
  const mag = Math.max(lo, hi);
  // exp of a large negative real underflows in float64. A point at 0 would be
  // the integer 0, and negation would fold to −0. The enclosure stays positive.
  if (!(mag > 0) || !Number.isFinite(mag)) {
    if (Number.isFinite(range.re.hi) && range.re.hi < EXP_UNDERFLOW_RE) {
      const tiny = Number.MIN_VALUE;
      if (range.im && range.im.lo === 0 && range.im.hi === 0) return { re: { lo: 0, hi: tiny }, im: { lo: 0, hi: 0 } };
      return { re: { lo: -tiny, hi: tiny }, im: { lo: -tiny, hi: tiny } };
    }
    return UNKNOWN;
  }
  const M = outHi(mag);
  const m = outLo(Math.min(lo, hi));
  if (range.im && range.im.lo === 0 && range.im.hi === 0) {
    return { re: { lo: Math.max(0, m), hi: M }, im: { lo: 0, hi: 0 } };
  }
  return { re: { lo: -M, hi: M }, im: { lo: -M, hi: M } };
}

function lnRange(range: Range): Range {
  if (range.re && range.im && range.re.lo === 0 && range.re.hi === 0 && range.im.lo === 0 && range.im.hi === 0) {
    return { re: { lo: -Infinity, hi: -Infinity }, im: { lo: 0, hi: 0 } };
  }
  if (isPoint(range) && range.re && range.im) {
    const re = range.re.lo;
    const im = range.im.lo;
    const mag = Math.log(Math.hypot(re, im));
    const arg = re < 0 && im === 0 ? Math.PI : Math.atan2(im, re);
    if (Number.isFinite(mag) && Number.isFinite(arg)) return point(mag, arg);
  }
  return { re: null, im: { lo: -Math.PI, hi: Math.PI } };
}

export function noteExp(node: Node, arg: Node): Node {
  return setRange(node, expRange(rangeOf(arg)));
}

export function noteLn(node: Node, arg: Node): Node {
  return setRange(node, lnRange(rangeOf(arg)));
}

function expOf(t: Node): Node {
  return noteExp(E(t, ONE), t);
}

function ivAdd(a: Iv, b: Iv, sign: 1 | -1): Iv | null {
  const lo = sign === 1 ? a.lo + b.lo : a.lo - b.hi;
  const hi = sign === 1 ? a.hi + b.hi : a.hi - b.lo;
  return cancelledPoint(widen(lo, hi), Math.max(Math.abs(a.lo), Math.abs(a.hi), Math.abs(b.lo), Math.abs(b.hi)));
}

/**
 * A tagged float is the nearest float to its value, not the value: π, e, √2, ln 2 and
 * a decimal such as 3.141592653589793e0. Two of them can cancel to the float 0 when
 * their values differ, and the point 0 is then the exact 0 that the 0·x, 0/x and x^0
 * folds use: (3.141592653589793e0 − π)·10^20 was a certified 0 (it is −23846.26…).
 * A 0 from nonzero terms keeps two ulps of the larger term on each side.
 */
function cancelledPoint(iv: Iv | null, scale: number): Iv | null {
  if (!iv || iv.lo !== 0 || iv.hi !== 0 || !(scale > 0)) return iv;
  const by = 2 * ulp(scale);
  return { lo: -by, hi: by };
}

function ivMul(a: Range, b: Range): Range {
  if (!a.re || !a.im || !b.re || !b.im) return UNKNOWN;
  let reLo = Infinity;
  let reHi = -Infinity;
  let imLo = Infinity;
  let imHi = -Infinity;
  let reUnder = false;
  let imUnder = false;
  for (const ar of [a.re.lo, a.re.hi]) {
    for (const ai of [a.im.lo, a.im.hi]) {
      for (const br of [b.re.lo, b.re.hi]) {
        for (const bi of [b.im.lo, b.im.hi]) {
          const re = ar * br - ai * bi;
          const im = ar * bi + ai * br;
          if (underflowed(ar, br, ar * br) || underflowed(ai, bi, ai * bi)) reUnder = true;
          if (underflowed(ar, bi, ar * bi) || underflowed(ai, br, ai * br)) imUnder = true;
          if (!Number.isFinite(re) || !Number.isFinite(im)) return UNKNOWN;
          reLo = Math.min(reLo, re);
          reHi = Math.max(reHi, re);
          imLo = Math.min(imLo, im);
          imHi = Math.max(imHi, im);
        }
      }
    }
  }
  const re = widen(reLo, reHi);
  const im = widen(imLo, imHi);
  if (!re || !im) return UNKNOWN;
  // Each underflowed term is below 2^(−1074); two terms per part.
  return { re: reUnder ? pad(re, 2 * Number.MIN_VALUE) : re, im: imUnder ? pad(im, 2 * Number.MIN_VALUE) : im };
}

type CombinedRange = { range: Range; int?: bigint };

/**
 * The largest exact integer product a circuit keeps: twice the largest literal
 * (1e1000000), so a literal and its square stay exact and a chain of products stops.
 * Uncapped, x·x·…·x with x = 1e1000000 multiplied ever larger integers, and counting
 * their digits took 32 s on the page's main thread (parse fuzz, seed 3).
 */
const CIRCUIT_INT_DIGITS_MAX = 2_100_000;

function combine(a: Node, b: Node, op: "add" | "sub" | "mul" | "div"): CombinedRange {
  const ra = rangeOf(a);
  const rb = rangeOf(b);
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  // A product past CIRCUIT_INT_DIGITS_MAX is tracked by its range, not as an integer.
  const exactInt =
    op === "add" || op === "sub" || (op === "mul" && ia !== undefined && ib !== undefined && intProductFits(ia, ib, CIRCUIT_INT_DIGITS_MAX));
  if (ia !== undefined && ib !== undefined && exactInt) {
    const value = op === "add" ? ia + ib : op === "sub" ? ia - ib : ia * ib;
    return { range: intRange(value), int: value };
  }
  if (op === "mul") {
    const product = ivMul(ra, rb);
    if (product !== UNKNOWN && (ia === undefined || ib === undefined)) return { range: product };
  }
  if (ra.im && rb.im && ra.re && rb.re && op !== "mul" && op !== "div") {
    const sign = op === "sub" ? -1 : 1;
    const re = ivAdd(ra.re, rb.re, sign);
    const im = ivAdd(ra.im, rb.im, sign);
    if (re && im) return { range: { re, im } };
  }
  if (!isPoint(ra) || !isPoint(rb) || !ra.re || !ra.im || !rb.re || !rb.im) return { range: UNKNOWN };
  const ar = ra.re.lo;
  const ai = ra.im.lo;
  const br = rb.re.lo;
  const bi = rb.im.lo;
  let re = 0;
  let im = 0;
  if (op === "add") {
    re = ar + br;
    im = ai + bi;
  } else if (op === "sub") {
    re = ar - br;
    im = ai - bi;
  } else if (op === "mul") {
    // Reached only when ivMul gave nothing, and ivMul is what pads an underflow.
    if ([[ar, br], [ai, bi], [ar, bi], [ai, br]].some(([x, y]) => underflowed(x, y, x * y))) return { range: UNKNOWN };
    re = ar * br - ai * bi;
    im = ar * bi + ai * br;
  } else {
    const den = br * br + bi * bi;
    if (!(den > 0) || !Number.isFinite(den)) return { range: UNKNOWN };
    // A quotient read from underflowed terms, or one that itself underflowed, is
    // not a point: 10^(−300)/10^100 came out the point 0.
    const terms = [[ar, br], [ai, bi], [ai, br], [ar, bi], [br, br], [bi, bi]];
    if (terms.some(([x, y]) => underflowed(x, y, x * y))) return { range: UNKNOWN };
    re = (ar * br + ai * bi) / den;
    im = (ai * br - ar * bi) / den;
    if (underflowed(ar * br + ai * bi, 1, re) || underflowed(ai * br - ar * bi, 1, im)) return { range: UNKNOWN };
  }
  const rv = widen(re, re);
  const iv = widen(im, im);
  if (!rv || !iv) return { range: UNKNOWN };
  return { range: { re: rv, im: iv } };
}

function subRange(a: Node, b: Node): CombinedRange {
  return combine(a, b, "sub");
}

export function naiveSub(a: Node, b: Node): Node {
  const { range, int } = subRange(a, b);
  return setRange(applyProgram("sub", { x: a, y: b }), range, int);
}

/**
 * naiveSub when a = exp(H) as a word (mul, div, and sqrt end in an exp):
 * sub(a, b) = eml(ln a, exp b), and exp(ln(exp H)) = exp H on every branch,
 * so eml(H, exp b) is the same value and eight tokens shorter.
 */
function subOfExp(a: Node, b: Node): Node {
  if (a.type === "eml" && a.a && a.b.type === "one") {
    const { range, int } = subRange(a, b);
    return setRange(E(a.a, E(b, ONE)), range, int);
  }
  return naiveSub(a, b);
}

function rawAdd(a: Node, b: Node): Node {
  const { range, int } = combine(a, b, "add");
  const node = setRange(applyProgram("add", { x: a, y: b }), range, int);
  return int !== undefined ? attachInt(node, int) : node;
}

export function rawMul(a: Node, b: Node): Node {
  const { range, int } = combine(a, b, "mul");
  const node = setRange(applyProgram("mul", { x: a, y: b }), range, int);
  const tagged = int !== undefined ? attachInt(node, int) : node;
  const out = markMaybeInfinite(tagged, a, b);
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) unresolvedHuge.add(out);
  return out;
}

function poleSignOf(node: Node): -1 | 1 | null {
  const typed = realInfinitySign(node);
  if (typed !== null) return typed;
  return recordedPoleSign(node);
}

function realZeroValue(v: { re: number; im: number } | null): boolean {
  if (!v) return false;
  return (Object.is(v.re, 0) || Object.is(v.re, -0)) && (v.im === 0 || Object.is(v.im, -0));
}

/**
 * Sign of a zero leaf: the −0 input, a typed ±0, or the integer 0.
 * A computed point whose float is +0 is not one of these. An underflowed
 * power prints that point, and dividing it has to keep the exact circuit.
 */
function leafZeroSign(node: Node): -1 | 1 | null {
  if (isUnverified(node) || isExactUnsure(node) || dependsOnUnverified(node)) return null;
  if (node === negZero) return -1;
  if (provenInteger(node) === BigInt(0)) return 1;
  if (node.type === "input") {
    const { re, im } = node.value;
    if ((im === 0 || Object.is(im, -0)) && (Object.is(re, 0) || Object.is(re, -0))) {
      return Object.is(re, -0) ? -1 : 1;
    }
  }
  return null;
}

/** +1 or −1 when the range is a finite real that does not contain 0. */
function realSide(node: Node): -1 | 1 | null {
  if (isUnverified(node) || isExactUnsure(node) || dependsOnUnverified(node)) return null;
  const range = rangeOf(node);
  if (!range.re || !range.im || range.im.lo !== 0 || range.im.hi !== 0) return null;
  if (!Number.isFinite(range.re.lo) || !Number.isFinite(range.re.hi)) return null;
  if (range.re.lo > 0) return 1;
  if (range.re.hi < 0) return -1;
  return null;
}

export function rawDiv(a: Node, b: Node): Node {
  const num = knownValue(a);
  const den = knownValue(b);
  if (
    num &&
    den &&
    realZeroValue(num) &&
    !isUnverified(a) &&
    !isExactUnsure(a) &&
    !dependsOnUnverified(a) &&
    (den.im === 0 || Object.is(den.im, -0)) &&
    den.re !== 0 &&
    Number.isFinite(den.re)
  ) {
    // +0/(−1) is −0. The div word logs +0 and would return +0, so the
    // reciprocal would be the wrong infinity. This leaf is the signed zero.
    const neg = Object.is(num.re, -0) !== den.re < 0;
    return neg ? negativeZero() : zeroNode();
  }
  // 0 over a real interval that stays positive or stays negative is that
  // signed zero. The div word is what exact mode then refuses: the denominator
  // is not a point, so the shortcut above never saw it.
  const znum = leafZeroSign(a);
  const side = realSide(b);
  if (znum !== null && side !== null) return znum === side ? zeroNode() : negativeZero();
  const node = setRange(applyProgram("div", { x: a, y: b }), combine(a, b, "div").range);
  if (provenInteger(b) === BigInt(0) && provenInteger(a) !== BigInt(0)) {
    const numerator = provenInteger(a);
    const neg = numerator !== undefined && numerator < BigInt(0);
    return markQuotient(noteNonfinite(node, neg ? -1 : 1), a, b);
  }
  if (certifiedZeroSign(b) === -1) {
    // The div program logs +0, so a/(−0) comes out with the sign of a/(+0).
    // A real numerator is negated after that division, which flips the
    // infinity and keeps the ln 0 note. i/(−0) is (−i)/(+0): negating the
    // numerator first keeps the axis, so the result is −∞i and not +∞i.
    // 0/(−0) is indeterminate. A typed infinity leaf had the sign and dropped the note.
    if (certifiedZeroSign(a) !== null) return markUnverified(markQuotient(node, a, b));
    const num = knownValue(a);
    const real =
      a.type === "one" ||
      (num !== null && (num.im === 0 || Object.is(num.im, -0)) && Number.isFinite(num.re) && num.re !== 0 && !Object.is(num.re, -0));
    if (real) return domainNeg(rawDiv(a, zeroNode()));
    return rawDiv(domainNeg(a), zeroNode());
  }
  return markQuotient(node, a, b);
}

/** 0/0 and any quotient whose denominator is zero. The numerator's mark propagates either way. */
function markQuotient(node: Node, numerator: Node, denominator: Node): Node {
  if (denominatorMayBeZero(denominator)) markInfiniteSource(node);
  return markMaybeInfinite(node, numerator);
}

function denominatorMayBeZero(den: Node): boolean {
  if (provenInteger(den) === BigInt(0)) return true;
  const v = knownValue(den);
  return v !== null && realZeroValue(v);
}

let negZero: Node | undefined;

/** Literal −0. The zero program is +0, and negating it must keep the sign. */
export function negativeZero(): Node {
  negZero ??= input({ re: -0, im: 0 }, "-0");
  return negZero;
}

/**
 * Sign of a zero whose sign is actually certified: the −0 leaf, an input ±0,
 * the integer 0, or a computed point whose real part is +0. A magnitude the
 * cap erased is not one of these: the sign did not survive. A point whose
 * real part is −0 is not a sign either. That is what two negative zeros used
 * to print, and exact mode will not stand behind it.
 */
export function certifiedZeroSign(node: Node): -1 | 1 | null {
  if (isUnverified(node) || isExactUnsure(node) || dependsOnUnverified(node)) return null;
  if (node === negZero) return -1;
  if (provenInteger(node) === BigInt(0)) return 1;
  if (node.type === "input") {
    const { re, im } = node.value;
    if ((im === 0 || Object.is(im, -0)) && (Object.is(re, 0) || Object.is(re, -0))) {
      return Object.is(re, -0) ? -1 : 1;
    }
  }
  // A computed point with real part +0 is the exact 0 already used as an identity.
  // A point whose real part is −0 is not: two negative zeros print that, and it is not a sign.
  const known = knownValue(node);
  if (known && (known.im === 0 || Object.is(known.im, -0)) && known.re === 0 && !Object.is(known.re, -0)) return 1;
  return null;
}

let minusOne: Node | undefined;
let two: Node | undefined;
let zero: Node | undefined;
const ints = new Map<number, Node>();
const building = new Set<number>();
let integerBuilder: ((n: number) => Node) | null = null;

/** Library integers are built with the short programs. Scaling uses the same builder. */
export function installIntegerBuilder(build: (n: number) => Node): void {
  integerBuilder = build;
}

export function beginInteger(n: number): void {
  building.add(n);
}

export function endInteger(n: number): void {
  building.delete(n);
}

/** True while the library builds an integer from smaller ones (its own adds and muls must not fold). */
export function buildingInteger(): boolean {
  return building.size > 0;
}

function zeroNode(): Node {
  if (!zero) zero = tagReal(programNode("0"), 0);
  return zero;
}

function oneNeg(): Node {
  if (!minusOne) minusOne = tagReal(programNode("-1"), -1);
  return minusOne;
}

function twoNode(): Node {
  if (!two) two = tagReal(programNode("2"), 2);
  return two;
}

function smallInt(n: number): Node {
  if (integerBuilder && !building.has(n)) return integerBuilder(n);
  if (n === 0) return zeroNode();
  if (n === 1) return setRange(ONE, { re: { lo: 1, hi: 1 }, im: { lo: 0, hi: 0 } }, BigInt(1));
  if (n === 2) return twoNode();
  if (n === -1) return oneNeg();
  const hit = ints.get(n);
  if (hit) return hit;
  const node = n < 0 ? rawMul(oneNeg(), smallInt(-n)) : n % 2 === 0 ? rawMul(smallInt(n / 2), twoNode()) : rawAdd(smallInt(n - 1), ONE);
  ints.set(n, tagReal(node, n));
  return ints.get(n) ?? node;
}

function expInt(n: number): Node {
  return expOf(smallInt(n));
}

function scaleFor(mag: number): Node {
  const n = Math.max(1, Math.ceil(Math.log(Math.max(mag, 1))));
  return expInt(Math.min(n, EXP_SCALE_MAX));
}

/** True when the range cannot contain 0. An unknown endpoint is not a proof. */
function provenNonzero(node: Node): boolean {
  const int = provenInteger(node);
  if (int !== undefined) return int !== BigInt(0);
  const range = rangeOf(node);
  if (range.re && (range.re.lo > 0 || range.re.hi < 0)) return true;
  if (range.im && (range.im.lo > 0 || range.im.hi < 0)) return true;
  return false;
}

function scaled(a: Node, b: Node, k: Node, op: "add" | "sub"): Node {
  const left = rawDiv(a, k);
  const right = rawDiv(b, k);
  const mixed = op === "sub" ? naiveSub(left, right) : rawAdd(left, right);
  return rawMul(k, mixed);
}

/**
 * k = 1 + √(b²). The log inside the square root has imaginary part in
 * [−π, π] on this branch, so the root has nonnegative real part, Re k ≥ 1,
 * and k ≠ 0. A different branch of that log can make k zero. |b/k| ≤ 1.
 * b² overflows float only past |b| ≈ 1.3×10^154. At b = 0 the square root
 * word is 0, so k = 1, and a variable bound to 0 still runs this circuit.
 * The 1 is a subtraction of −1, not domainAdd, so the scale does not build
 * another scaled subtraction.
 */
function magnitudeScale(b: Node): Node {
  return subOfExp(applyProgram("sqrt", { x: applyProgram("sqr", { x: b }) }), oneNeg());
}

/** k · rotSub(a/k, b/k). The scale is inside the circuit, not applied afterwards. */
function scaledRot(a: Node, b: Node, kFrom: Node = b): Node {
  const k = magnitudeScale(kFrom);
  return rawMul(k, rotSub(rawDiv(a, k), rawDiv(b, k)));
}

function pureReal(node: Node): boolean {
  if (provenInteger(node) !== undefined) return true;
  const range = rangeOf(node);
  return !!range.re && !!range.im && range.im.lo === 0 && range.im.hi === 0;
}

function pureImag(node: Node): boolean {
  const range = rangeOf(node);
  if (!range.re || !range.im) return false;
  const re = Math.max(Math.abs(range.re.lo), Math.abs(range.re.hi));
  const im = Math.max(Math.abs(range.im.lo), Math.abs(range.im.hi));
  if (!(im > 0)) return false;
  return re === 0 || re <= 32 * ulp(Math.max(im, 1));
}

function axisAligned(a: Node, b: Node): boolean {
  return (pureReal(a) && pureImag(b)) || (pureImag(a) && pureReal(b));
}

/**
 * A non-integer kept beside an integer past 2^1024, or a later use of that node.
 * Cancelling the recorded huge integer is exact. Any other meeting is not a value.
 */
const unresolvedHuge = new WeakSet<Node>();

function noteUnresolvedHuge(node: Node, a: Node, b: Node): void {
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) {
    unresolvedHuge.add(node);
    return;
  }
  const leftHuge = floatOverflowInt(a) !== null;
  const rightHuge = floatOverflowInt(b) !== null;
  if (leftHuge === rightHuge) return;
  const other = leftHuge ? b : a;
  if (provenInteger(other) === undefined) unresolvedHuge.add(node);
}

function noteRealSum(node: Node, left: Node, right: Node): void {
  if (node === left || node === right) return;
  noteBuiltSum(node, left, right);
  noteUnresolvedHuge(node, left, right);
}

function rememberSub(node: Node, left: Node, right: Node): Node {
  if (node === left || node === right) return node;
  noteBuiltSub(node, left, right);
  noteUnresolvedHuge(node, left, right);
  return node;
}

let unverifiedCount = 0;

/** The existing uncertified result: no number, in either mode. */
function unverifiedResult(): Node {
  unverifiedCount += 1;
  const node = markUnverified(input({ re: 0, im: 0 }, `unverified:${unverifiedCount}`));
  unresolvedHuge.add(node);
  return node;
}

/** a − (a + c) = −c, when the sum was recorded and both summands are finite. */
function sumComplement(subtrahend: Node, minuend: Node): Node | null {
  const parts = builtSumOf(subtrahend);
  if (!parts || !provenFinite(parts.left) || !provenFinite(parts.right)) return null;
  if (parts.left === minuend) return parts.right;
  if (parts.right === minuend) return parts.left;
  return null;
}

/**
 * a − (a − c) = c and (a − c) − a = −c, when both parts are finite.
 * (a − c) − c is a − 2c. Folding that arm back to a cancels one subtraction.
 */
function subComplement(minuend: Node, subtrahend: Node): Node | null {
  const inner = builtSubOf(subtrahend);
  if (inner && provenFinite(inner.left) && provenFinite(inner.right) && inner.left === minuend) return inner.right;
  const outer = builtSubOf(minuend);
  if (!outer || !provenFinite(outer.left) || !provenFinite(outer.right)) return null;
  if (outer.left === subtrahend) return zeroValued(outer.right) ? zeroNode() : domainNeg(outer.right);
  return null;
}

/** The integer 0 or the −0 leaf. Its fold is a − a, which is +0, not its negation. */
function zeroValued(node: Node): boolean {
  if (provenInteger(node) === BigInt(0)) return true;
  return node.type === "input" && node.value.re === 0 && node.value.im === 0;
}

/** An integer past the float range. Number(10^400) is already Infinity. */
function floatOverflowInt(node: Node): -1 | 1 | null {
  const n = provenInteger(node);
  if (n === undefined) return null;
  const limit = BigInt(2) ** BigInt(1024);
  if (n >= limit) return 1;
  if (n <= -limit) return -1;
  return null;
}

function finiteBeside(node: Node): boolean {
  if (floatOverflowInt(node)) return false;
  if (provenInteger(node) !== undefined) return true;
  const v = knownValue(node);
  if (v !== null && Number.isFinite(v.re) && Number.isFinite(v.im)) return true;
  // 0.5 is a narrow interval, not a point. Dust such as 10^(−15) stays on the ordinary circuit.
  if (!provenFinite(node)) return false;
  const range = rangeOf(node);
  const re = range.re ? Math.max(Math.abs(range.re.lo), Math.abs(range.re.hi)) : 0;
  const im = range.im ? Math.max(Math.abs(range.im.lo), Math.abs(range.im.hi)) : 0;
  return Math.max(re, im) >= 1e-6;
}

/**
 * An unknown range is not a proof, and a typed infinity is not finite.
 * A past-cap power is finite: it is only too small to certify inside 480 digits.
 */
export function provenFinite(node: Node): boolean {
  if (isNonfiniteNode(node) || realInfinitySign(node) !== null) return false;
  if (isLostTiny(node)) return true;
  if (provenInteger(node) !== undefined) return true;
  const range = rangeOf(node);
  if (!range.re || !range.im) return false;
  return [range.re.lo, range.re.hi, range.im.lo, range.im.hi].every((end) => Number.isFinite(end));
}

function cancelledSummand(sum: Node, part: Node): Node | null {
  const parts = builtSumOf(sum);
  // (1 + ∞) − ∞ is ∞ − ∞, not 1. Fold only when both summands are finite.
  if (!parts || !provenFinite(parts.left) || !provenFinite(parts.right)) return null;
  if (parts.left === part) return parts.right;
  if (parts.right === part) return parts.left;
  return null;
}

function realInfinitySign(node: Node): -1 | 1 | null {
  if (node.type !== "input") return null;
  if (node.value.im !== 0 && !Object.is(node.value.im, -0)) return null;
  if (node.value.re === Infinity) return 1;
  if (node.value.re === -Infinity) return -1;
  return null;
}

let turn: Node | undefined;

/** The K 21 word. Under this cut it is +iπ, and it is the rotator for every rotSub. */
function ipiNode(): Node {
  if (!turn) {
    turn = learn(tagValue(programNode("ipi"), { re: 0, im: Math.PI }), {
      angle: { q: { n: BigInt(1), d: BigInt(1) }, unit: "imag" },
    });
  }
  return turn;
}

/**
 * a − b = raw(c·raw(a, b), c·raw(b, b)) / c with c = +iπ, for all a, b in ℂ,
 * given ln 0 = −∞ and the extended model where exp(+∞ + iθ) = +∞.
 * Each inner subtraction is subOfExp, never domainSub: a minuend that is
 * already an exponential drops ln(exp(H)).
 * Known values inside the float strip use this circuit. Unknown ranges and
 * values outside the strip scale first.
 */
function rotSub(a: Node, b: Node, c = ipiNode()): Node {
  const turned = subOfExp(rawMul(c, subOfExp(a, b)), rawMul(c, subOfExp(b, b)));
  return rawDiv(turned, c);
}

/** The rotSub circuit, so the suite can check its length. */
export function rotSubCircuit(a: Node, b: Node): Node {
  return rotSub(a, b);
}

function imagInsideRot(range: Range): boolean {
  if (!range.im) return false;
  return range.im.lo > ROT_IM_MIN && range.im.hi < ROT_IM_MAX;
}

/** Known and inside the strip where unscaled rotSub is exact in float. */
function knownInsideStrip(b: Node): boolean {
  const range = rangeOf(b);
  if (!range.re || !range.im) return false;
  const ends = [range.re.lo, range.re.hi, range.im.lo, range.im.hi];
  if (!ends.every((end) => Number.isFinite(end))) return false;
  // The exact strip is (−71π, 71π). The next step, out to 73π, is already subnormal.
  if (!(range.im.lo > ROT_IM_MIN && range.im.hi < -ROT_IM_MIN)) return false;
  const re = Math.max(Math.abs(range.re.lo), Math.abs(range.re.hi));
  return re < ROT_REAL_MAX;
}

function finish(node: Node, combined: CombinedRange): Node {
  if (combined.int !== undefined) return attachInt(node, combined.int);
  return setRange(node, combined.range);
}

function moderate(a: Node, b: Node): boolean {
  const mag = maxMag(a, b);
  return mag !== null && mag < SHORT_MAG && !nearCut(rangeOf(b));
}

function buildSub(a: Node, b: Node, kFrom: Node = b): Node {
  const range = subRange(a, b);
  const rb = rangeOf(b);
  if (provenInteger(b) === BigInt(0)) return a;
  if (isNegInf(rb)) return finish(naiveSub(a, b), range);
  const tiny = scaledTinySub(a, b);
  if (tiny) return tiny;

  // Short subtraction is faithful for moderate reals, and for a real beside a
  // small imaginary. Two imaginaries, or anything near the cut, take the rotation.
  if (moderate(a, b) && absEnd(rb.re) !== null && (absEnd(rb.re) ?? 0) < REAL_CAP && (pureReal(a) && pureReal(b) || axisAligned(a, b))) {
    return finish(naiveSub(a, b), range);
  }

  // A known large real, away from the cut, scales by exp(n). The subtrahend
  // is real, so this does not divide an imaginary part away.
  const mag = maxMag(a, b);
  if (mag !== null && pureReal(b) && !nearCut(rb) && imagInsideRot(rb) && mag >= SHORT_MAG && provenNonzero(b)) {
    return finish(scaled(a, b, scaleFor(mag), "sub"), range);
  }
  // Known and inside the float strip: the unscaled rotation is already exact.
  if (knownInsideStrip(b)) return finish(rotSub(a, b), range);
  // Unknown, or too large for the strip: scale, then rotate.
  return finish(scaledRot(a, b, kFrom), range);
}

/**
 * A real that float64 has already lost, or a decade below the working precision.
 * 2·exp(−1000) is not a point at Number.MIN_VALUE: its enclosure is about 10^(−323).
 * Anything that small is still invisible to the 120-digit subtraction.
 */
function underflowedReal(node: Node): boolean {
  const decade = decadeOf(node);
  if (decade !== undefined && decade <= -300) return true;
  const size = extent(node);
  if (!size) return false;
  const mag = Math.max(size.re, size.im);
  return mag > 0 && mag <= 1e-300;
}

export function markExactInt(node: Node, value: bigint): Node {
  noteMarkedExactInt(node, value);
  return attachInt(node, value);
}

/**
 * One node per integer. Two sums that share a float, such as 10^400+1 and 10^400+3,
 * must not be the same node: the second write would replace the first integer.
 * A finite float is an input leaf labelled with the full decimal.
 * An overflow stays a multiple of its source, so dividing it does not become ln 0.
 * The factor is a fresh 1 keyed by the decimal, so those multiples do not merge.
 */
function carryHugeInt(value: bigint, a: Node, b: Node): Node {
  const approx = Number(value);
  if (Number.isFinite(approx)) return markExactInt(input({ re: approx, im: 0 }, `int:${value.toString()}`), value);
  const signA = floatOverflowInt(a);
  const source = signA ? a : b;
  const sourceSign = signA ?? floatOverflowInt(b) ?? 1;
  const want = value > BigInt(0) ? 1 : -1;
  const one = input({ re: 1, im: 0 }, `int:${value.toString()}`);
  const scaled = rawMul(source, one);
  const node = want === sourceSign ? scaled : rawMul(oneNeg(), scaled);
  return markExactInt(node, value);
}

/**
 * A distinct copy of `huge`. The real sum rotates through ln 0 and comes out negative,
 * so the node only remembers the two operands. A later cancellation returns the small one.
 * The factor is a fresh 1, so two different small parts of the same huge integer stay different nodes.
 */
function rememberHugeReal(huge: Node, other: Node, op: "add" | "sub"): Node {
  const one = input({ re: 1, im: 0 }, `beside:${other.id}:${op}`);
  const node = rawMul(huge, one);
  noteBesideSum(node, huge, other, op);
  if (op === "add") noteRealSum(node, huge, other);
  else rememberSub(node, huge, other);
  // The factor's label is how exact mode sees that this mul is not the sum.
  // Evaluating the mul would certify the bare integer and drop the small term.
  return node;
}

function overflowIntDiff(a: Node, b: Node): Node | null {
  if (!floatOverflowInt(a) && !floatOverflowInt(b)) return null;
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia === undefined || ib === undefined) return null;
  const diff = ia - ib;
  if (diff === BigInt(0)) return zeroNode();
  if (diff <= SAFE && diff >= -SAFE) return smallInt(Number(diff));
  return rememberSub(carryHugeInt(diff, a, b), a, b);
}

function overflowIntSum(a: Node, b: Node): Node | null {
  if (!floatOverflowInt(a) && !floatOverflowInt(b)) return null;
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia === undefined || ib === undefined) return null;
  const sum = ia + ib;
  if (sum === BigInt(0)) return zeroNode();
  if (sum <= SAFE && sum >= -SAFE) return smallInt(Number(sum));
  const node = carryHugeInt(sum, a, b);
  noteRealSum(node, a, b);
  return node;
}

/** Exact quotient of an integer past the float range, when the quotient itself still fits in a float. */
export function integerQuotient(a: Node, b: Node): Node | null {
  if (!floatOverflowInt(a) && !floatOverflowInt(b)) return null;
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia === undefined || ib === undefined || ib === BigInt(0)) return null;
  if (ia % ib !== BigInt(0)) return null;
  const q = ia / ib;
  if (!Number.isFinite(Number(q))) return null;
  if (q <= SAFE && q >= -SAFE) return smallInt(Number(q));
  return markExactInt(input({ re: Number(q), im: 0 }, `int:${q.toString()}`), q);
}

export function domainSub(a: Node, b: Node, kFrom: Node = b): Node {
  return markMaybeInfinite(domainSubBuild(a, b, kFrom), a, b);
}

function domainSubBuild(a: Node, b: Node, kFrom: Node = b): Node {
  const folded = cancelledSummand(a, b);
  if (folded) return folded;
  const complement = sumComplement(b, a);
  // a − (a + 0) is a − a, which is +0. Negating the 0 gave −0, so ln of it was −∞ + iπ.
  if (complement) return zeroValued(complement) ? zeroNode() : domainNeg(complement);
  const rest = subComplement(a, b);
  if (rest) return rest;
  // Same-sign infinities are indeterminate. That check stays ahead of the identical-node fold.
  const pa = poleSignOf(a);
  const pb = poleSignOf(b);
  if (pa !== null && pb !== null && pa === pb) return rememberSub(naiveSub(a, b), a, b);
  // Identical nodes cancel before a huge term is rewritten. A marked node stays on the ordinary circuit.
  if (a === b && !mayBeInfinite(a)) {
    // The shared zero leaf must stay unmarked. A series shortcut that returned
    // its argument makes f(x) − x the same node twice; that zero is not certified
    // (and must not feed into further arithmetic as a certified 0).
    if (isSeriesShortcut(a)) return markExactUnsure(markSeriesShortcut(naiveSub(ONE, ONE)));
    if (isExactUnsure(a)) return markExactUnsure(naiveSub(ONE, ONE));
    // a − a of a refused node is not the certified +0. The fresh difference stays refused.
    if (isUnverified(a) || dependsOnUnverified(a)) return markUnverified(naiveSub(ONE, ONE));
    return zeroNode();
  }
  const carried = overflowIntDiff(a, b);
  if (carried) return carried;
  // A finite non-integer beside an integer past the float range is not dropped.
  // The real difference rotates through ln 0 and comes out negative, so the node only remembers both operands.
  if (floatOverflowInt(a) && finiteBeside(b)) return rememberHugeReal(a, b, "sub");
  // Two huge-carried terms whose small parts are not both exact integers.
  // The real circuit drops one of them and would certify the rest.
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) return unverifiedResult();
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia !== undefined && ib !== undefined) {
    const diff = ia - ib;
    if (diff === BigInt(0)) return zeroNode();
    const huge = ia > SAFE || ia < -SAFE || ib > SAFE || ib < -SAFE;
    if (huge && diff <= SAFE && diff >= -SAFE) return smallInt(Number(diff));
    const node = buildSub(a, b, kFrom);
    return rememberSub(huge ? node : attachInt(node, diff), a, b);
  }
  // 0 − b is −b. The subtraction circuit rounds a sub-120-digit b to exact 0.
  // A past-cap quotient such as 1/10^433 has no decade, but it is still −b.
  if (ia === BigInt(0) && (underflowedReal(b) || isLostTiny(b))) return domainNeg(b);
  return rememberSub(buildSub(a, b, kFrom), a, b);
}

function safeNeg(b: Node): Node {
  const size = extent(b);
  const ib = provenInteger(b);
  if (size && size.im < Math.PI - CUT_MARGIN && size.re < REAL_CAP) {
    const node = applyProgram("minus", { x: b });
    if (ib !== undefined) return attachInt(node, -ib);
    const range = rangeOf(b);
    if (range.re && range.im) {
      const re = widen(-range.re.hi, -range.re.lo);
      const im = widen(-range.im.hi, -range.im.lo);
      if (re && im) return setRange(node, { re, im });
    }
    return node;
  }
  const node = rawMul(oneNeg(), b);
  if (ib !== undefined) return attachInt(node, -ib);
  const range = rangeOf(b);
  if (range.re && range.im) {
    const re = widen(-range.re.hi, -range.re.lo);
    const im = widen(-range.im.hi, -range.im.lo);
    if (re && im) return setRange(node, { re, im });
  }
  return node;
}

const powersOfTen = new Map<number, Node>();

/** 10^k by squaring. An integer power stays exact far past the point where 2^k·x does not. */
function tenPow(k: number): Node {
  const hit = powersOfTen.get(k);
  if (hit) return hit;
  let result: Node = ONE;
  let base = smallInt(10);
  let n = k;
  while (n > 0) {
    if (n % 2 === 1) result = result === ONE ? base : rawMul(result, base);
    n = Math.floor(n / 2);
    if (n > 0) base = rawMul(base, base);
  }
  powersOfTen.set(k, result);
  return result;
}

/**
 * Power of ten that lifts `mag` up to about 1. A term a hundred digits below
 * the operands then sits inside the 120-digit circuit. 10^308 is not a finite float,
 * so a subnormal operand is lifted in two steps (see liftSteps).
 */
function liftExponent(mag: number): number {
  if (!(mag > 0) || !Number.isFinite(mag)) return 1;
  return Math.min(2 * TEN_POW_MAX, Math.max(1, Math.ceil(-Math.log10(mag))));
}

/**
 * The lift as powers of ten that are each a finite float. Capping a subnormal's
 * lift at 10^307 left 1e−320 at 1e−13, where the sub word keeps only about
 * 10^(−120) absolute: 1e−320·(1 + 1e−100) − 1e−320 kept 7 digits, unseen by the
 * exact engine because the lift gates are not counted as work.
 */
function liftSteps(k: number): number[] {
  return k <= TEN_POW_MAX ? [k] : [TEN_POW_MAX, k - TEN_POW_MAX];
}

function liftBy(node: Node, k: number): Node {
  return liftSteps(k).reduce((acc, step) => rawMul(acc, tenPow(step)), node);
}

function dropBy(node: Node, k: number): Node {
  return liftSteps(k).reverse().reduce((acc, step) => rawDiv(acc, tenPow(step)), node);
}

/** x·10^k in float, in the same steps, so a subnormal's lift does not overflow. */
function liftedFloat(x: number, k: number): number {
  if (x === 0) return x;
  return liftSteps(k).reduce((acc, step) => acc * 10 ** step, x);
}

/** An underflow with no decade and no known nonzero value. Raising precision cannot recover it. */
export function hiddenUnderflow(node: Node): boolean {
  if (decadeOf(node) !== undefined) return false;
  const known = knownValue(node);
  if (known && (known.re !== 0 || known.im !== 0)) return false;
  return underflowedReal(node);
}

function noteNegation(node: Node, arg: Node): Node {
  return noteBuiltFrom(node, { negationOf: arg });
}

/** floor(log10 |z|) when the node is a known nonzero real or a known integer. */
function magnitudeDecade(node: Node): number | null {
  const decade = decadeOf(node);
  if (decade !== undefined) return decade;
  const known = knownValue(node);
  if (known && known.im === 0 && known.re !== 0 && Number.isFinite(known.re)) {
    return Math.floor(Math.log10(Math.abs(known.re)) + 1e-10);
  }
  const n = provenInteger(node);
  if (n === undefined || n === BigInt(0)) return null;
  return intDecade(n < BigInt(0) ? -n : n);
}

/**
 * A quotient or product keeps the decade of a tiny real, so 0 − (1/10^400)
 * and 0 − (exp(−1000)/3) see the same term a bare power would.
 * Past the 480-digit cap the result is marked, not given a decade: a series
 * shortcut must not resolve it.
 */
export function carryTinyScale(node: Node, a: Node, b: Node, op: "mul" | "div"): Node {
  if (provenInteger(node) === BigInt(0)) return node;
  const da = magnitudeDecade(a);
  const db = magnitudeDecade(b);
  if (da !== null && db !== null) {
    const decade = op === "div" ? da - db : da + db;
    if (decade <= -300) {
      if (-decade + 48 <= 480) noteDecade(node, decade);
      else noteLostTiny(node);
    }
    return node;
  }
  // exp(−1000)/3 has no decade of its own. Dividing or scaling by a modest
  // finite factor leaves it below the cap.
  const hidden = (term: Node) => decadeOf(term) === undefined && (isLostTiny(term) || underflowedReal(term));
  const modest = (decade: number | null) => decade !== null && decade >= 0 && decade <= 8;
  if (op === "div" && hidden(a) && modest(db)) noteLostTiny(node);
  if (op === "mul" && ((hidden(a) && modest(db)) || (hidden(b) && modest(da)))) noteLostTiny(node);
  return node;
}

/**
 * A real whose leading term sits at `decade`, signed when that sign is known.
 * The interval is wide enough that the next series term stays inside it, and
 * narrow enough that a later cancellation still sees a tiny real.
 * Past the float range only the decade is recorded.
 */
export function noteTinyReal(node: Node, decade: number, negative: boolean): Node {
  const marked = noteDecade(node, decade);
  const mag = 10 ** decade;
  if (!(mag > 0) || !Number.isFinite(mag)) return marked;
  const lo = negative ? -10 * mag : mag / 10;
  const hi = negative ? -mag / 10 : 10 * mag;
  return setRange(marked, { re: { lo, hi }, im: { lo: 0, hi: 0 } });
}

/** Hide a lift's internal cancellation so it is not mistaken for the value's work. */
export function shieldLift(root: Node, operands: Node[]): Node {
  return markShell(root, operands);
}

function markShell(root: Node, operands: Node[]): Node {
  const stop = new Set(operands);
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || stop.has(node) || seen.has(node)) continue;
    seen.add(node);
    if (node.type !== "eml") continue;
    noteScaledShell(node);
    stack.push(node.a, node.b);
  }
  return root;
}

/** Imaginary interval, or null when the range does not prove one. */
function imagSpan(node: Node): { lo: number; hi: number } | null {
  const im = rangeOf(node).im;
  if (!im || !Number.isFinite(im.lo) || !Number.isFinite(im.hi)) return null;
  return im;
}

/**
 * The raw add word equals x + y only for Im(x + y) in (−π, π].
 * After the power-of-ten lift that sum can leave the strip, so the short word is refused.
 */
function inAddStrip(lo: number, hi: number): boolean {
  return lo > -Math.PI && hi <= Math.PI;
}

function scaledSumInAddStrip(a: Node, b: Node, k: number): boolean {
  const ia = imagSpan(a);
  const ib = imagSpan(b);
  if (!ia || !ib) return false;
  const up = (x: number) => liftedFloat(x, k);
  // The raw add wraps when either scaled imaginary part leaves (−π, π], and when their sum does.
  if (!inAddStrip(up(ia.lo), up(ia.hi)) || !inAddStrip(up(ib.lo), up(ib.hi))) return false;
  return inAddStrip(up(ia.lo + ib.lo), up(ia.hi + ib.hi));
}

function scaledTiny(a: Node, b: Node, k: number): Node {
  const combined = liftedCombine(rawAdd(liftBy(a, k), liftBy(b, k)));
  return markTwoScaled(markShell(dropBy(combined, k), [a, b]));
}

function liftedCombine(node: Node): Node {
  noteLiftedCombine(node);
  return node;
}

/** (a·10^k − b·10^k) / 10^k. The short subtraction loses a difference near 10^(−20). */
function scaledTinySub(a: Node, b: Node): Node | null {
  if (nearCut(rangeOf(a)) || nearCut(rangeOf(b))) return null;
  const mag = maxMag(a, b);
  if (mag === null || !(mag > 0 && mag < TINY_MAG)) return null;
  const k = liftExponent(mag);
  const ib = imagSpan(b);
  if (!ib) return null;
  // The short sub word is exact for Im y in [−π, π). The lift can push a tiny imaginary past that.
  // One decade less keeps it inside: |Im y|·10^(k−1) < 1. Without the lift, 5×10^(−200)i − 4×10^(−200)i
  // took the unscaled rotation, which loses the subtrahend under its 120 digits.
  const fits = (lift: number) => liftedFloat(ib.lo, lift) >= -Math.PI && liftedFloat(ib.hi, lift) < Math.PI;
  const lift = fits(k) ? k : k > 1 && fits(k - 1) ? k - 1 : null;
  if (lift === null) return null;
  const combined = liftedCombine(naiveSub(liftBy(a, lift), liftBy(b, lift)));
  return markTwoScaled(markShell(dropBy(combined, lift), [a, b]));
}

export function domainAdd(a: Node, b: Node): Node {
  return markMaybeInfinite(domainAddBuild(a, b), a, b);
}

function domainAddBuild(a: Node, b: Node): Node {
  const cancelled = sumOfNegation(a, b);
  if (cancelled) return cancelled;
  const carried = overflowIntSum(a, b);
  if (carried) return carried;
  // A finite non-integer beside an integer past the float range is not dropped.
  // Building the sum rotates through ln 0 and comes out negative, so the node only remembers both operands.
  if (floatOverflowInt(a) && finiteBeside(b)) return rememberHugeReal(a, b, "add");
  if (floatOverflowInt(b) && finiteBeside(a)) return rememberHugeReal(b, a, "add");
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) return unverifiedResult();
  // exp(−1000)+exp(−1000) is 2·exp(−1000). The add circuit prints 0, and the
  // product is the same node as a written 2·exp, so the difference folds to 0.
  if (a === b && decadeOf(a) === undefined && (isLostTiny(a) || underflowedReal(a))) return rawMul(twoNode(), a);
  // (−x) + x is 0. The sum circuit cannot see a past-cap x.
  // A refused operand is not that cancellation: the shared +0 would drop the refusal.
  const refusedSum = isUnverified(a) || isUnverified(b) || isExactUnsure(a) || isExactUnsure(b) || dependsOnUnverified(a) || dependsOnUnverified(b);
  if (!refusedSum && (factsOf(a).builtFrom?.negationOf === b || factsOf(b).builtFrom?.negationOf === a)) return zeroNode();
  // 0 + b is b. The add circuit rounds an underflowed b to exact 0.
  if (!refusedSum && provenInteger(a) === BigInt(0) && (underflowedReal(b) || isLostTiny(b))) return b;
  if (!refusedSum && provenInteger(b) === BigInt(0) && (underflowedReal(a) || isLostTiny(a))) return a;
  const { range, int } = combine(a, b, "add");
  const mag = maxMag(a, b);
  let node: Node;
  let unknown = false;
  const bothReal = pureReal(a) && pureReal(b);
  const cut = nearCut(rangeOf(a)) || nearCut(rangeOf(b));
  if (mag !== null && mag > 0 && mag < TINY_MAG && !cut) {
    const k = liftExponent(mag);
    // A scaled imaginary sum outside (−π, π] is not the raw add word. One decade less
    // lift keeps it inside. The rotation fallback negates b with the minus word, which
    // rounds a b under 10^(−120) to 0: 5×10^(−200)i + 3×10^(−200)i certified 5×10^(−200)i.
    const lift = scaledSumInAddStrip(a, b, k) ? k : k > 1 && scaledSumInAddStrip(a, b, k - 1) ? k - 1 : null;
    node = lift !== null ? scaledTiny(a, b, lift) : domainSub(a, safeNeg(b));
  } else if (mag !== null && mag < SHORT_MAG && !cut && (bothReal || axisAligned(a, b))) {
    node = rawAdd(a, b);
  } else if (mag !== null && mag < SHORT_MAG) node = domainSub(a, safeNeg(b));
  else if (mag !== null) node = scaled(a, b, scaleFor(mag), "add");
  else {
    // k(−b) = 1 + √(b²) = k(b). Build the scale from b, not from the negation.
    node = domainSub(a, safeNeg(b), b);
    unknown = true;
  }
  const tagged = int !== undefined ? attachInt(node, int) : setRange(node, range);
  noteRealSum(tagged, a, b);
  if (unknown) notePrecision(tagged, { kind: "add", left: a, right: b });
  // exp(−1000)+exp(−1000) is a real tiny sum the circuit prints as 0.
  // A recorded decade can still be recovered by raising precision, so leave those sums alone.
  if (underflowedReal(a) && underflowedReal(b) && decadeOf(a) === undefined && decadeOf(b) === undefined) noteLostTiny(tagged);
  return tagged;
}

/** b was built as −a, or a as −b. */
export function isNegationPair(a: Node, b: Node): boolean {
  return factsOf(b).builtFrom?.negOf === a || factsOf(a).builtFrom?.negOf === b;
}

/** a + (−a) is 0 when a is unmarked. A marked a falls through to the ordinary sum. */
export function sumOfNegation(a: Node, b: Node): Node | null {
  const base = factsOf(b).builtFrom?.negOf === a ? a : factsOf(a).builtFrom?.negOf === b ? b : null;
  if (base === null) return null;
  if (isSeriesShortcut(a) || isSeriesShortcut(b) || isExactUnsure(a) || isExactUnsure(b)) return null;
  if (isUnverified(a) || isUnverified(b) || dependsOnUnverified(a) || dependsOnUnverified(b)) return null;
  if (mayBeInfinite(base)) return null;
  return zeroNode();
}

export function domainNeg(b: Node): Node {
  const out = markMaybeInfinite(domainNegBuild(b), b);
  if (out !== b && factsOf(out).builtFrom?.negOf === undefined) noteBuiltFrom(out, { negOf: b });
  if (unresolvedHuge.has(b)) unresolvedHuge.add(out);
  return out;
}

function domainNegBuild(b: Node): Node {
  // A refused operand stays refused. Returning the shared ±0 leaf here dropped
  // the refusal and certified the opposite zero.
  if (isUnverified(b) || isExactUnsure(b) || dependsOnUnverified(b)) return markUnverified(safeNeg(b));
  const z = certifiedZeroSign(b);
  if (z === 1) return negativeZero();
  if (z === -1) return zeroNode();
  // The minus program collapses a tiny value to 0. −x = (−1)·x keeps it.
  const size = extent(b);
  if (size && Math.max(size.re, size.im) > 0 && Math.max(size.re, size.im) < TINY_MAG) return noteNegation(rawMul(oneNeg(), b), b);
  // The negation stays finite, so 0 times it is an exact 0 and does not inherit the cap mark.
  if (isLostTiny(b)) return noteLostTiny(noteNegation(rawMul(oneNeg(), b), b));
  return safeNeg(b);
}
