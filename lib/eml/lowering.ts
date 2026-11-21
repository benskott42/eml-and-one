import { E, ONE, ROT_IM_MAX, ROT_IM_MIN, clearProvenInt, input, isSeriesShortcut, markSeriesShortcut, markUnverified, notePrecision, noteProvenInt, onCircuitIsolate, provenInteger, type Node } from "./node";
import { noteBuilder } from "./provenance";
import { applyProgram, programNode } from "./programs";

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
  /** Present only when the node was built as that integer. */
  int?: bigint;
};

const UNKNOWN: Range = { re: null, im: null };
const ranges = new WeakMap<Node, Range>();
/**
 * Build-time only: (left + right) − left is the other summand. Evaluation never reads this.
 * Cleared with each top-level expression, so one expression cannot fold another's sum.
 */
let realSum = new WeakMap<Node, { left: Node; right: Node }>();
let realSub = new WeakMap<Node, { left: Node; right: Node }>();

onCircuitIsolate(() => {
  realSum = new WeakMap();
  realSub = new WeakMap();
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

function setRange(node: Node, range: Range): Node {
  const previous = provenInteger(node);
  if (previous !== undefined && range.int === undefined) {
    if (keepsInteger(range, previous)) range = { ...range, int: previous };
    else clearProvenInt(node);
  }
  ranges.set(node, range);
  if (range.int !== undefined) noteProvenInt(node, range.int);
  return node;
}

export function rangeOf(node: Node): Range {
  if (node.type === "one") return { re: { lo: 1, hi: 1 }, im: { lo: 0, hi: 0 }, int: BigInt(1) };
  const hit = ranges.get(node);
  if (hit) return hit;
  if (node.type === "input") {
    const { re, im } = node.value;
    if (Number.isFinite(re) && Number.isFinite(im)) return point(re, im);
  }
  return UNKNOWN;
}

function ulp(x: number): number {
  const ax = Math.abs(x);
  if (!(ax > 0) || !Number.isFinite(ax)) return 0;
  return 2 ** (Math.floor(Math.log2(ax)) - 52);
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

function attachInt(node: Node, value: bigint): Node {
  if (safeInt(value)) {
    const n = Number(value);
    return setRange(node, { re: { lo: n, hi: n }, im: { lo: 0, hi: 0 }, int: value });
  }
  const approx = Number(value);
  const re = Number.isFinite(approx) ? widen(approx, approx) : null;
  return setRange(node, { re, im: { lo: 0, hi: 0 }, int: value });
}

export function tagValue(node: Node, value: { re: number; im: number }): Node {
  if (!Number.isFinite(value.re) || !Number.isFinite(value.im)) return node;
  return setRange(node, point(value.re, value.im === 0 ? 0 : value.im));
}

export function tagReal(node: Node, re: number): Node {
  const range = point(re, 0);
  const existing = rangeOf(node).int;
  if (existing !== undefined) range.int = existing;
  else if (Number.isInteger(re) && Number.isSafeInteger(re)) range.int = BigInt(re);
  return setRange(node, range);
}

export function tagInteger(node: Node, value: bigint): Node {
  return attachInt(node, value);
}

export function knownValue(node: Node): { re: number; im: number } | null {
  const range = rangeOf(node);
  if (range.int !== undefined && safeInt(range.int)) return { re: Number(range.int), im: 0 };
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
  // exp of a large negative real underflows to 0 in float64. That is a known
  // zero for choosing a circuit; the node itself still evaluates.
  if (!(mag > 0) || !Number.isFinite(mag)) {
    if (Number.isFinite(range.re.hi) && range.re.hi < EXP_UNDERFLOW_RE) return point(0, 0);
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
  return noteBuilder(noteExp(E(t, ONE), t), "expOf");
}

function ivAdd(a: Iv, b: Iv, sign: 1 | -1): Iv | null {
  const lo = sign === 1 ? a.lo + b.lo : a.lo - b.hi;
  const hi = sign === 1 ? a.hi + b.hi : a.hi - b.lo;
  return widen(lo, hi);
}

function ivMul(a: Range, b: Range): Range {
  if (!a.re || !a.im || !b.re || !b.im) return UNKNOWN;
  let reLo = Infinity;
  let reHi = -Infinity;
  let imLo = Infinity;
  let imHi = -Infinity;
  for (const ar of [a.re.lo, a.re.hi]) {
    for (const ai of [a.im.lo, a.im.hi]) {
      for (const br of [b.re.lo, b.re.hi]) {
        for (const bi of [b.im.lo, b.im.hi]) {
          const re = ar * br - ai * bi;
          const im = ar * bi + ai * br;
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
  return { re, im };
}

function combine(a: Range, b: Range, op: "add" | "sub" | "mul" | "div"): Range {
  if (op !== "div" && a.int !== undefined && b.int !== undefined && (op === "add" || op === "sub" || op === "mul")) {
    const value = op === "add" ? a.int + b.int : op === "sub" ? a.int - b.int : a.int * b.int;
    if (safeInt(value)) {
      const n = Number(value);
      return { re: { lo: n, hi: n }, im: { lo: 0, hi: 0 }, int: value };
    }
    const approx = Number(value);
    return { re: Number.isFinite(approx) ? widen(approx, approx) : null, im: { lo: 0, hi: 0 }, int: value };
  }
  if (op === "mul") {
    const product = ivMul(a, b);
    if (product !== UNKNOWN && (a.int === undefined || b.int === undefined)) return product;
  }
  if (a.im && b.im && a.re && b.re && op !== "mul" && op !== "div") {
    const sign = op === "sub" ? -1 : 1;
    const re = ivAdd(a.re, b.re, sign);
    const im = ivAdd(a.im, b.im, sign);
    if (re && im) return { re, im };
  }
  if (!isPoint(a) || !isPoint(b) || !a.re || !a.im || !b.re || !b.im) return UNKNOWN;
  const ar = a.re.lo;
  const ai = a.im.lo;
  const br = b.re.lo;
  const bi = b.im.lo;
  let re = 0;
  let im = 0;
  if (op === "add") {
    re = ar + br;
    im = ai + bi;
  } else if (op === "sub") {
    re = ar - br;
    im = ai - bi;
  } else if (op === "mul") {
    re = ar * br - ai * bi;
    im = ar * bi + ai * br;
  } else {
    const den = br * br + bi * bi;
    if (!(den > 0) || !Number.isFinite(den)) return UNKNOWN;
    re = (ar * br + ai * bi) / den;
    im = (ai * br - ar * bi) / den;
  }
  const rv = widen(re, re);
  const iv = widen(im, im);
  if (!rv || !iv) return UNKNOWN;
  return { re: rv, im: iv };
}

function subRange(a: Node, b: Node): Range {
  return combine(rangeOf(a), rangeOf(b), "sub");
}

export function naiveSub(a: Node, b: Node): Node {
  return setRange(applyProgram("sub", { x: a, y: b }), subRange(a, b));
}

/**
 * naiveSub when a = exp(H) as a word (mul, div, and sqrt end in an exp):
 * sub(a, b) = eml(ln a, exp b), and exp(ln(exp H)) = exp H on every branch,
 * so eml(H, exp b) is the same value and eight tokens shorter.
 */
function subOfExp(a: Node, b: Node): Node {
  if (a.type === "eml" && a.a && a.b === ONE) {
    const inner = noteBuilder(E(b, ONE), "expOf");
    return noteBuilder(setRange(E(a.a, inner), subRange(a, b)), "subOfExp");
  }
  return naiveSub(a, b);
}

function rawAdd(a: Node, b: Node): Node {
  const range = combine(rangeOf(a), rangeOf(b), "add");
  const node = setRange(applyProgram("add", { x: a, y: b }), range);
  return range.int !== undefined ? attachInt(node, range.int) : node;
}

export function rawMul(a: Node, b: Node): Node {
  const range = combine(rangeOf(a), rangeOf(b), "mul");
  const node = setRange(applyProgram("mul", { x: a, y: b }), range);
  const tagged = range.int !== undefined ? attachInt(node, range.int) : node;
  const out = markMaybeInfinite(tagged, a, b);
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) unresolvedHuge.add(out);
  return out;
}

function poleSignOf(node: Node): -1 | 1 | null {
  const typed = realInfinitySign(node);
  if (typed !== null) return typed;
  return poleSign.get(node) ?? null;
}

/**
 * Nodes that may be infinite or indeterminate.
 * The mark is written when the node is built. A fold never inspects values or ranges.
 * a − a and a + (−a) fold to 0 only for a node that is not in this set.
 */
const maybeInfinite = new WeakSet<Node>();

/** Mark `out` when any of `from` may be infinite. Returns `out`. */
export function markMaybeInfinite(out: Node, ...from: Node[]): Node {
  if (from.some((node) => mayBeInfinite(node))) maybeInfinite.add(out);
  return out;
}

/** Mark a node that is itself an infinite or indeterminate source. */
export function markInfiniteSource(node: Node): Node {
  maybeInfinite.add(node);
  return node;
}

export function mayBeInfinite(node: Node): boolean {
  return maybeInfinite.has(node);
}

/**
 * v1.1 (reviewbot #11 review C): the sign of a marked node's infinity when it can only be a
 * REAL infinity of that sign (ln 0 = −∞, −ln 0 = +∞). Unset means unknown (complex, NaN, or
 * either sign). exp uses it: exp(−∞) = 0 is finite, so exp of a −∞-only node is not marked.
 */
const infiniteSign = new WeakMap<Node, -1 | 1>();

export function markInfiniteSign(node: Node, sign: -1 | 1 | null | undefined): Node {
  if (sign && mayBeInfinite(node)) infiniteSign.set(node, sign);
  return node;
}

export function infiniteSignOf(node: Node): -1 | 1 | undefined {
  return mayBeInfinite(node) ? infiniteSign.get(node) : undefined;
}

function realZeroValue(v: { re: number; im: number } | null): boolean {
  if (!v) return false;
  return (Object.is(v.re, 0) || Object.is(v.re, -0)) && (v.im === 0 || Object.is(v.im, -0));
}

export function rawDiv(a: Node, b: Node): Node {
  const num = knownValue(a);
  const den = knownValue(b);
  if (
    num &&
    den &&
    !wides.has(a) &&
    realZeroValue(num) &&
    (den.im === 0 || Object.is(den.im, -0)) &&
    den.re !== 0 &&
    Number.isFinite(den.re)
  ) {
    // +0/(−1) is −0. The div word logs +0 and would return +0, so the
    // reciprocal would be the wrong infinity. This leaf is the signed zero.
    const neg = Object.is(num.re, -0) !== den.re < 0;
    return neg ? negativeZero() : zeroNode();
  }
  const node = setRange(applyProgram("div", { x: a, y: b }), combine(rangeOf(a), rangeOf(b), "div"));
  if (rangeOf(b).int === BigInt(0) && rangeOf(a).int !== BigInt(0)) {
    const numerator = rangeOf(a).int;
    const neg = numerator !== undefined && numerator < BigInt(0);
    return markQuotient(noteNonfinite(node, neg ? -1 : 1), a, b);
  }
  if (b.type === "input" && Object.is(b.value.re, -0) && (b.value.im === 0 || Object.is(b.value.im, -0))) {
    // The div program logs +0, so the gates of 1/(−0) come out +∞.
    // The reciprocal of this leaf is the opposite infinity, which is what
    // those keys compute.
    const num = knownValue(a);
    const positive = a.type === "one" || (num !== null && num.re > 0 && (num.im === 0 || Object.is(num.im, -0)));
    const negative = num !== null && num.re < 0 && (num.im === 0 || Object.is(num.im, -0));
    if (positive) return noteNonfinite(input({ re: -Infinity, im: 0 }, "−∞"), -1);
    if (negative) return noteNonfinite(input({ re: Infinity, im: 0 }, "∞"), 1);
    return markQuotient(noteNonfinite(node, -1), a, b);
  }
  return markQuotient(node, a, b);
}

/** 0/0 and any quotient whose denominator is zero. The numerator's mark propagates either way. */
function markQuotient(node: Node, numerator: Node, denominator: Node): Node {
  if (denominatorMayBeZero(denominator)) markInfiniteSource(node);
  // v1.1 (#11 review C): 1/(0/0) is NaN. Over a real-signed infinity (1/ln 0 = 0) it stays finite.
  if (mayBeInfinite(denominator) && infiniteSignOf(denominator) === undefined) markInfiniteSource(node);
  return markMaybeInfinite(node, numerator);
}

function denominatorMayBeZero(den: Node): boolean {
  if (rangeOf(den).int === BigInt(0)) return true;
  const v = knownValue(den);
  return v !== null && realZeroValue(v);
}

/** A typed infinity. 0 · ∞ is indeterminate even when the infinity was not a division. */
export function noteNonfinite(node: Node, sign: -1 | 1 = 1): Node {
  nonfiniteNode.add(node);
  poleSign.set(node, sign);
  return node;
}

let negZero: Node | undefined;

/** Literal −0. The zero program is +0, and negating it must keep the sign. */
export function negativeZero(): Node {
  negZero ??= input({ re: -0, im: 0 }, "-0");
  return negZero;
}

export function isNonfiniteNode(node: Node): boolean {
  return nonfiniteNode.has(node);
}

let minusOne: Node | undefined;
let two: Node | undefined;
let zero: Node | undefined;
const ints = new Map<number, Node>();
const building = new Set<number>();
const nonfiniteNode = new WeakSet<Node>();
const poleSign = new WeakMap<Node, -1 | 1>();
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
  if (n === 1) return setRange(ONE, { re: { lo: 1, hi: 1 }, im: { lo: 0, hi: 0 }, int: BigInt(1) });
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
  const range = rangeOf(node);
  if (range.int !== undefined) return range.int !== BigInt(0);
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
  const range = rangeOf(node);
  if (range.int !== undefined) return true;
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
  if (rangeOf(other).int === undefined) unresolvedHuge.add(node);
}

function noteRealSum(node: Node, left: Node, right: Node): void {
  if (node === left || node === right) return;
  realSum.set(node, { left, right });
  noteUnresolvedHuge(node, left, right);
}

function rememberSub(node: Node, left: Node, right: Node): Node {
  if (node === left || node === right) return node;
  realSub.set(node, { left, right });
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
  const parts = realSum.get(subtrahend);
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
  const inner = realSub.get(subtrahend);
  if (inner && provenFinite(inner.left) && provenFinite(inner.right) && inner.left === minuend) return inner.right;
  const outer = realSub.get(minuend);
  if (!outer || !provenFinite(outer.left) || !provenFinite(outer.right)) return null;
  if (outer.left === subtrahend) return domainNeg(outer.right);
  return null;
}

/** An integer past the float range. Number(10^400) is already Infinity. */
function floatOverflowInt(node: Node): -1 | 1 | null {
  const n = rangeOf(node).int;
  if (n === undefined) return null;
  const limit = BigInt(2) ** BigInt(1024);
  if (n >= limit) return 1;
  if (n <= -limit) return -1;
  return null;
}

function finiteBeside(node: Node): boolean {
  if (floatOverflowInt(node)) return false;
  if (rangeOf(node).int !== undefined) return true;
  const v = knownValue(node);
  if (v !== null && Number.isFinite(v.re) && Number.isFinite(v.im)) return true;
  // 0.5 is a narrow interval, not a point. Dust such as 10^(−15) stays on the ordinary circuit.
  if (!provenFinite(node)) return false;
  const range = rangeOf(node);
  const re = range.re ? Math.max(Math.abs(range.re.lo), Math.abs(range.re.hi)) : 0;
  const im = range.im ? Math.max(Math.abs(range.im.lo), Math.abs(range.im.hi)) : 0;
  return Math.max(re, im) >= 1e-6;
}

/** An unknown range is not a proof, and a typed infinity is not finite. */
function provenFinite(node: Node): boolean {
  if (isNonfiniteNode(node) || realInfinitySign(node) !== null) return false;
  const range = rangeOf(node);
  if (range.int !== undefined) return true;
  if (!range.re || !range.im) return false;
  return [range.re.lo, range.re.hi, range.im.lo, range.im.hi].every((end) => Number.isFinite(end));
}

function cancelledSummand(sum: Node, part: Node): Node | null {
  const parts = realSum.get(sum);
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
  if (!turn) turn = tagValue(programNode("ipi"), { re: 0, im: Math.PI });
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

function finish(node: Node, range: Range): Node {
  if (range.int !== undefined) return attachInt(node, range.int);
  return setRange(node, range);
}

function moderate(a: Node, b: Node): boolean {
  const mag = maxMag(a, b);
  return mag !== null && mag < SHORT_MAG && !nearCut(rangeOf(b));
}

function buildSub(a: Node, b: Node, kFrom: Node = b): Node {
  const range = subRange(a, b);
  const rb = rangeOf(b);
  if (rb.int === BigInt(0)) return a;
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

const markedExactInt = new WeakSet<Node>();

/** Exact evaluation reads this integer. The float value stays the rounded one. */
export function isMarkedExactInt(node: Node): boolean {
  return markedExactInt.has(node);
}

export function markExactInt(node: Node, value: bigint): Node {
  markedExactInt.add(node);
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
  if (op === "add") noteRealSum(node, huge, other);
  else rememberSub(node, huge, other);
  // The factor's label is how exact mode sees that this mul is not the sum.
  // Evaluating the mul would certify the bare integer and drop the small term.
  return node;
}

function overflowIntDiff(a: Node, b: Node): Node | null {
  if (!floatOverflowInt(a) && !floatOverflowInt(b)) return null;
  const ia = rangeOf(a).int;
  const ib = rangeOf(b).int;
  if (ia === undefined || ib === undefined) return null;
  const diff = ia - ib;
  if (diff === BigInt(0)) return zeroNode();
  if (diff <= SAFE && diff >= -SAFE) return smallInt(Number(diff));
  return rememberSub(carryHugeInt(diff, a, b), a, b);
}

function overflowIntSum(a: Node, b: Node): Node | null {
  if (!floatOverflowInt(a) && !floatOverflowInt(b)) return null;
  const ia = rangeOf(a).int;
  const ib = rangeOf(b).int;
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
  const ia = provenInteger(a) ?? rangeOf(a).int;
  const ib = provenInteger(b) ?? rangeOf(b).int;
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
  if (complement) return domainNeg(complement);
  const rest = subComplement(a, b);
  if (rest) return rest;
  // Same-sign infinities are indeterminate. That check stays ahead of the identical-node fold.
  const pa = poleSignOf(a);
  const pb = poleSignOf(b);
  if (pa !== null && pb !== null && pa === pb) return rememberSub(naiveSub(a, b), a, b);
  // Identical nodes cancel before a huge term is rewritten. A marked node stays on the ordinary circuit.
  if (a === b && !mayBeInfinite(a)) {
    // The shared zero leaf must stay unmarked. A series shortcut that returned
    // its argument makes f(x) − x the same node twice; that zero is not certified.
    if (isSeriesShortcut(a)) return markSeriesShortcut(naiveSub(ONE, ONE));
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
  const ia = rangeOf(a).int;
  const ib = rangeOf(b).int;
  if (ia !== undefined && ib !== undefined) {
    const diff = ia - ib;
    if (diff === BigInt(0)) return zeroNode();
    const huge = ia > SAFE || ia < -SAFE || ib > SAFE || ib < -SAFE;
    if (huge && diff <= SAFE && diff >= -SAFE) return smallInt(Number(diff));
    const node = buildSub(a, b, kFrom);
    return rememberSub(huge ? node : attachInt(node, diff), a, b);
  }
  const proved = tinyRationalNode(a, b, "sub");
  if (proved) return proved;
  return rememberSub(buildSub(a, b, kFrom), a, b);
}

function safeNeg(b: Node): Node {
  const size = extent(b);
  if (size && size.im < Math.PI - CUT_MARGIN && size.re < REAL_CAP) {
    const node = applyProgram("minus", { x: b });
    const range = rangeOf(b);
    if (range.int !== undefined) return attachInt(node, -range.int);
    if (range.re && range.im) {
      const re = widen(-range.re.hi, -range.re.lo);
      const im = widen(-range.im.hi, -range.im.lo);
      if (re && im) return setRange(node, { re, im });
    }
    return node;
  }
  const node = rawMul(oneNeg(), b);
  const range = rangeOf(b);
  if (range.int !== undefined) return attachInt(node, -range.int);
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
 * the operands then sits inside the 120-digit circuit. 10^308 is not a finite float.
 */
function liftExponent(mag: number): number {
  if (!(mag > 0) || !Number.isFinite(mag)) return 1;
  return Math.min(TEN_POW_MAX, Math.max(1, Math.ceil(-Math.log10(mag))));
}

/**
 * (a·10^k + b·10^k) / 10^k. The unscaled add only has about 10^(−16) of absolute
 * accuracy, so two values near 10^(−10) need to be lifted before they are added.
 */
const twoScaled = new WeakSet<Node>();
const decades = new WeakMap<Node, number>();

/** Signed power-of-ten exponent of a known real, including values float64 cannot hold. */
export function noteDecade(node: Node, exp: number): Node {
  if (Number.isFinite(exp)) decades.set(node, Math.trunc(exp));
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

export function decadeOf(node: Node): number | undefined {
  return decades.get(node);
}

/**
 * v1.1 prototype (compscibot): a real known as m·10^e with 1 ≤ |m| < 10, kept
 * when float64 cannot hold it as a normal number (|x| < 2^(−1022)). The float
 * range of such a node may say 0; this tag says it is not.
 */
export type Wide = { m: number; e: number };
const wides = new WeakMap<Node, Wide>();
export const MIN_NORMAL = 2.2250738585072014e-308;

export function normWide(m: number, e: number): Wide | null {
  if (!Number.isFinite(m) || m === 0 || !Number.isFinite(e)) return null;
  let mm = m;
  let ee = Math.trunc(e);
  const shift = Math.floor(Math.log10(Math.abs(mm)));
  mm /= 10 ** shift;
  ee += shift;
  if (Math.abs(mm) >= 10) { mm /= 10; ee += 1; }
  if (Math.abs(mm) < 1) { mm *= 10; ee -= 1; }
  return { m: mm, e: ee };
}

export function noteWide(node: Node, w: Wide | null): Node {
  if (!w) return node;
  wides.set(node, w);
  // The decade is the exponent of the leading digit, and it is exact here.
  decades.set(node, w.e);
  // A real, signed, sub-normal interval: never a point, so never "the integer 0".
  if (w.e < -307) {
    const range = w.m > 0 ? { re: { lo: 0, hi: MIN_NORMAL }, im: { lo: 0, hi: 0 } } : { re: { lo: -MIN_NORMAL, hi: 0 }, im: { lo: 0, hi: 0 } };
    ranges.set(node, range);
  }
  return node;
}

/** The wide tag, or a normal nonzero known real written the same way. */
export function wideOf(node: Node): Wide | null {
  const hit = wides.get(node);
  if (hit) return hit;
  const v = knownValue(node);
  if (v && (v.im === 0 || Object.is(v.im, -0)) && Number.isFinite(v.re) && Math.abs(v.re) >= MIN_NORMAL) {
    const e = Math.floor(Math.log10(Math.abs(v.re)));
    return normWide(v.re / 10 ** e, e);
  }
  return null;
}

export function isWideTiny(node: Node): boolean {
  return wides.has(node);
}

/**
 * A real below the normal float range, known exactly as an integer ratio.
 * Decimal literals start there, and multiply, divide, and negate carry it.
 * The EML circuit only approximates a value this small. Its residue is not
 * a proof, so a sum or difference that is not this ratio is not certified.
 */
const MAX_RATIO_DIGITS = 8192;
const ZERO = BigInt(0);
const ONE_BI = BigInt(1);
const TEN_BI = BigInt(10);
const NORMAL_SHIFT = BigInt(1022);
export type ExactRatio = { n: bigint; d: bigint };
const exactRatios = new WeakMap<Node, ExactRatio>();

function digitsOf(n: bigint): number {
  if (n === ZERO) return 1;
  const body = n < ZERO ? -n : n;
  return body.toString().length;
}

function gcdBig(a: bigint, b: bigint): bigint {
  let x = a < ZERO ? -a : a;
  let y = b < ZERO ? -b : b;
  while (y !== ZERO) {
    const next = x % y;
    x = y;
    y = next;
  }
  return x;
}

function reduceRatio(n: bigint, d: bigint): ExactRatio | null {
  if (d === ZERO) return null;
  if (n === ZERO) return { n: ZERO, d: ONE_BI };
  if (d < ZERO) {
    n = -n;
    d = -d;
  }
  const g = gcdBig(n, d);
  n /= g;
  d /= g;
  if (digitsOf(n) > MAX_RATIO_DIGITS || digitsOf(d) > MAX_RATIO_DIGITS) return null;
  return { n, d };
}

/** |n/d| < 2^(−1022), so float64 cannot hold it as a normal number. */
function belowNormal(n: bigint, d: bigint): boolean {
  if (n === ZERO || d === ZERO) return false;
  const absN = n < ZERO ? -n : n;
  const absD = d < ZERO ? -d : d;
  return (absN << NORMAL_SHIFT) < absD;
}

function ratioDecade(n: bigint, d: bigint): number {
  const absN = n < ZERO ? -n : n;
  const absD = d < ZERO ? -d : d;
  const len = absN.toString().length - absD.toString().length;
  const below = len >= 0 ? absN < absD * TEN_BI ** BigInt(len) : absN * TEN_BI ** BigInt(-len) < absD;
  return below ? len - 1 : len;
}

function wideFromRatio(n: bigint, d: bigint): Wide | null {
  if (n === ZERO || d === ZERO) return null;
  const decade = ratioDecade(n, d);
  const neg = (n < ZERO) !== (d < ZERO);
  const absN = n < ZERO ? -n : n;
  const absD = d < ZERO ? -d : d;
  const pow10 = (k: number) => TEN_BI ** BigInt(k);
  const scaled = decade >= 0 ? (absN * pow10(15)) / (absD * pow10(decade)) : (absN * pow10(15 - decade)) / absD;
  let m = Number(scaled) / 1e15;
  if (!Number.isFinite(m) || m === 0) return null;
  if (neg) m = -m;
  return normWide(m, decade);
}

/** Store n/d when it sits below the normal float range, and keep the wide tag in step with it. */
export function noteExactRatio(node: Node, n: bigint, d: bigint): Node {
  const reduced = reduceRatio(n, d);
  if (!reduced || reduced.n === ZERO || !belowNormal(reduced.n, reduced.d)) return node;
  exactRatios.set(node, reduced);
  const wide = wideFromRatio(reduced.n, reduced.d);
  if (wide) noteWide(node, wide);
  return node;
}

export function exactRatioOf(node: Node): ExactRatio | null {
  return exactRatios.get(node) ?? null;
}

/** The stored ratio, or an integer node written as n/1. */
export function realRatioOf(node: Node): ExactRatio | null {
  const hit = exactRatios.get(node);
  if (hit) return hit;
  const big = rangeOf(node).int;
  if (big === undefined) return null;
  return { n: big, d: ONE_BI };
}

/** Attach n/d when a product or quotient of exact reals falls below the normal float range. */
export function attachTinyProduct(node: Node, a: Node, b: Node, op: "mul" | "div"): Node {
  const left = realRatioOf(a);
  const right = realRatioOf(b);
  if (!left || !right || (op === "div" && right.n === ZERO)) return node;
  const n = op === "mul" ? left.n * right.n : left.n * right.d;
  const d = op === "mul" ? left.d * right.d : left.d * right.n;
  return noteExactRatio(node, n, d);
}

/** Set while a proved tiny sum is being given its circuit, so that build does not re-enter. */
let inTinyRational = false;

/**
 * Exact sum or difference of two reals below the normal float range.
 * Equal ratios subtract to 0 and add to twice the value. A pair this small with no exact ratio is not certified:
 * the lifted circuit's residue is rounding, not a value.
 */
function tinyRationalNode(a: Node, b: Node, op: "add" | "sub"): Node | null {
  if (inTinyRational) return null;
  const left = realRatioOf(a);
  const right = realRatioOf(b);
  if (!left || !right || !belowNormal(left.n, left.d) || !belowNormal(right.n, right.d)) return null;
  // Equal ratios cancel under subtraction only. Their sum is twice the value.
  if (op === "sub" && left.n * right.d === right.n * left.d) return zeroNode();
  const n = op === "add" ? left.n * right.d + right.n * left.d : left.n * right.d - right.n * left.d;
  const reduced = reduceRatio(n, left.d * right.d);
  if (!reduced) return unverifiedResult();
  if (reduced.n === ZERO) return zeroNode();
  inTinyRational = true;
  try {
    const node = op === "sub" ? buildSub(a, b) : buildSub(a, domainNeg(b));
    return noteExactRatio(node, reduced.n, reduced.d);
  } finally {
    inTinyRational = false;
  }
}

/** A sum or difference lifted by a power of ten. Its small component is the value, not dust. */
export function markTwoScaled(node: Node): Node {
  twoScaled.add(node);
  return node;
}

export function isTwoScaled(node: Node): boolean {
  return twoScaled.has(node);
}

/**
 * Gates built only to lift a tiny pair by a power of ten and bring it back.
 * Their terms reach that scale, which says nothing about the size the circuit
 * works at, so the exact engine leaves them out when it sizes rounding dust.
 * The lifted operands are not in the set.
 */
const scaledShell = new WeakSet<Node>();

export function inScaledShell(node: Node): boolean {
  return scaledShell.has(node);
}

export function noteScaledShell(node: Node): void {
  scaledShell.add(node);
}

/** Hide a lift's internal cancellation so it is not mistaken for the value's work. */
/**
 * v1.1: an odd power series x + c₁x³ + c₂x⁵ + … built by library.ts oddSeries. Its circuit is
 * that polynomial, so exact mode evaluates the polynomial from x directly instead of the lifted
 * circuit (same value; the truncation is already past the 480-digit cap). Coefficients are
 * [numerator, denominator, sign].
 */
export type SeriesCoeff = [string, string, -1 | 1];
const oddSeriesPolys = new WeakMap<Node, { arg: Node; coeffs: SeriesCoeff[] }>();

export function noteOddSeries(node: Node, arg: Node, coeffs: SeriesCoeff[]): Node {
  oddSeriesPolys.set(node, { arg, coeffs });
  return node;
}

export function oddSeriesOf(node: Node): { arg: Node; coeffs: SeriesCoeff[] } | undefined {
  return oddSeriesPolys.get(node);
}

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
    scaledShell.add(node);
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
  const scale = 10 ** k;
  if (!ia || !ib || !Number.isFinite(scale)) return false;
  // The raw add wraps when either scaled imaginary part leaves (−π, π], and when their sum does.
  if (!inAddStrip(ia.lo * scale, ia.hi * scale) || !inAddStrip(ib.lo * scale, ib.hi * scale)) return false;
  return inAddStrip((ia.lo + ib.lo) * scale, (ia.hi + ib.hi) * scale);
}

function scaledTiny(a: Node, b: Node, k: number): Node {
  const scale = tenPow(k);
  return noteBuilder(markTwoScaled(markShell(rawDiv(rawAdd(rawMul(a, scale), rawMul(b, scale)), scale), [a, b])), "scaledTiny");
}

/** (a·10^k − b·10^k) / 10^k. The short subtraction loses a difference near 10^(−20). */
function scaledTinySub(a: Node, b: Node): Node | null {
  if (nearCut(rangeOf(a)) || nearCut(rangeOf(b))) return null;
  const mag = maxMag(a, b);
  if (mag === null || !(mag > 0 && mag < TINY_MAG)) return null;
  const k = liftExponent(mag);
  const ib = imagSpan(b);
  const scaleFactor = 10 ** k;
  // The short sub word is exact for Im y in [−π, π). The lift can push a tiny imaginary past that.
  if (!ib || !Number.isFinite(scaleFactor) || !(ib.lo * scaleFactor >= -Math.PI && ib.hi * scaleFactor < Math.PI)) return null;
  const scale = tenPow(k);
  return noteBuilder(markTwoScaled(markShell(rawDiv(naiveSub(rawMul(a, scale), rawMul(b, scale)), scale), [a, b])), "scaledTinySub");
}

export function domainAdd(a: Node, b: Node): Node {
  return markMaybeInfinite(domainAddBuild(a, b), a, b);
}

function domainAddBuild(a: Node, b: Node): Node {
  const cancelled = sumOfNegation(a, b);
  if (cancelled) return cancelled;
  const carried = overflowIntSum(a, b);
  if (carried) return carried;
  const proved = tinyRationalNode(a, b, "add");
  if (proved) return proved;
  // Adding a non-integer to an integer past the float range must stay +∞.
  // Building the sum rotates through ln 0 and comes out negative.
  // A finite non-integer beside an integer past the float range is not dropped.
  // Building the sum rotates through ln 0 and comes out negative, so the node only remembers both operands.
  if (floatOverflowInt(a) && finiteBeside(b)) return rememberHugeReal(a, b, "add");
  if (floatOverflowInt(b) && finiteBeside(a)) return rememberHugeReal(b, a, "add");
  if (unresolvedHuge.has(a) || unresolvedHuge.has(b)) return unverifiedResult();
  const range = combine(rangeOf(a), rangeOf(b), "add");
  const mag = maxMag(a, b);
  let node: Node;
  let unknown = false;
  const bothReal = pureReal(a) && pureReal(b);
  const cut = nearCut(rangeOf(a)) || nearCut(rangeOf(b));
  if (mag !== null && mag > 0 && mag < TINY_MAG && !cut) {
    const k = liftExponent(mag);
    // A scaled imaginary sum outside (−π, π] is not the raw add word. rotSub is.
    node = scaledSumInAddStrip(a, b, k) ? scaledTiny(a, b, k) : domainSub(a, safeNeg(b));
  } else if (mag !== null && mag < SHORT_MAG && !cut && (bothReal || axisAligned(a, b))) {
    node = rawAdd(a, b);
  } else if (mag !== null && mag < SHORT_MAG) node = domainSub(a, safeNeg(b));
  else if (mag !== null) node = scaled(a, b, scaleFor(mag), "add");
  else {
    // k(−b) = 1 + √(b²) = k(b). Build the scale from b, not from the negation.
    node = domainSub(a, safeNeg(b), b);
    unknown = true;
  }
  const tagged = range.int !== undefined ? attachInt(node, range.int) : setRange(node, range);
  noteRealSum(tagged, a, b);
  if (unknown) notePrecision(tagged, { kind: "add", left: a, right: b });
  return tagged;
}

const negOf = new WeakMap<Node, Node>();

/** a + (−a) is 0 when a is unmarked. A marked a falls through to the ordinary sum. */
/** v1.1: b was built as −a (or a as −b). Read only; no fold. */
export function isNegationPair(a: Node, b: Node): boolean {
  return negOf.get(b) === a || negOf.get(a) === b;
}

export function sumOfNegation(a: Node, b: Node): Node | null {
  const base = negOf.get(b) === a ? a : negOf.get(a) === b ? b : null;
  if (base === null) return null;
  if (isSeriesShortcut(a) || isSeriesShortcut(b)) return null;
  if (mayBeInfinite(base)) return null;
  return zeroNode();
}

export function domainNeg(b: Node): Node {
  const out = markMaybeInfinite(domainNegBuild(b), b);
  if (out !== b && !negOf.has(out)) negOf.set(out, b);
  if (unresolvedHuge.has(b)) unresolvedHuge.add(out);
  return out;
}

function domainNegBuild(b: Node): Node {
  const wb = wides.get(b);
  const ratio = exactRatioOf(b);
  if (wb) {
    const node = noteWide(rawMul(oneNeg(), b), { m: -wb.m, e: wb.e });
    if (ratio) noteExactRatio(node, -ratio.n, ratio.d);
    return node;
  }
  if (ratio) return noteExactRatio(rawMul(oneNeg(), b), -ratio.n, ratio.d);
  const n = rangeOf(b).int;
  if (n === BigInt(0)) return negativeZero();
  const v = knownValue(b);
  if (v && (v.im === 0 || Object.is(v.im, -0)) && Object.is(v.re, 0)) return negativeZero();
  if (v && (v.im === 0 || Object.is(v.im, -0)) && Object.is(v.re, -0)) return zeroNode();
  // The minus program collapses a tiny value to 0. −x = (−1)·x keeps it.
  const size = extent(b);
  if (size && Math.max(size.re, size.im) > 0 && Math.max(size.re, size.im) < TINY_MAG) return rawMul(oneNeg(), b);
  return safeNeg(b);
}
