import type { C } from "./complex";
import {
  beginInteger,
  domainAdd,
  domainNeg,
  domainSub,
  endInteger,
  decadeOf,
  isNonfiniteNode,
  knownValue,
  noteDecade,
  noteTinyReal,
  naiveSub,
  negativeZero,
  shieldLift,
  noteExp,
  noteLn,
  noteNonfinite,
  rangeOf,
  tagInteger,
  rawDiv,
  rawMul,
  tagReal,
  tagValue,
  installIntegerBuilder,
} from "./lowering";
import { E, EmlError, ONE, isolateCircuit, markSeriesShortcut, onCircuitIsolate, type Node, V, input, notePrecision } from "./node";
import { applyProgram, programNode } from "./programs";

/**
 * Every primitive of a scientific calculator, built only from 1 and eml.
 * The shapes follow the constructive reductions in arXiv:2603.21852:
 * exp, ln (equation 5), then subtraction, and the usual exp-log identities.
 *
 * Builders only assemble trees. They never evaluate, and they never replace
 * a subexpression with a stored float. Overflow is handled by the evaluator
 * (float64, or the wide-exponent exact mode), not by editing the program.
 * The only input nodes are numbers the user typed.
 */

export const X: Node = V("x");
export const Y: Node = V("y");

const memoResets: Array<() => void> = [];

function memo(build: () => Node): () => Node {
  let cached: Node | undefined;
  memoResets.push(() => {
    cached = undefined;
  });
  return () => (cached ??= build());
}

onCircuitIsolate(() => {
  for (const reset of memoResets) reset();
  intCache.clear();
  unaryCache.clear();
  binaryCache.clear();
});

function imagZero(v: { re: number; im: number }): boolean {
  return v.im === 0 || Object.is(v.im, -0);
}

/**
 * A known point, or the center of an interval only a few ulps wide.
 * Negation widens ±i, and a sum widens 2+10^(−18)i, so neither is a point.
 */
function tightValue(t: Node): { re: number; im: number } | null {
  const known = knownValue(t);
  if (known) return known;
  const range = rangeOf(t);
  if (!range.re || !range.im) return null;
  const re = (range.re.lo + range.re.hi) / 2;
  const im = (range.im.lo + range.im.hi) / 2;
  if (!Number.isFinite(re) || !Number.isFinite(im)) return null;
  const scale = Math.max(1, Math.abs(re), Math.abs(im));
  if (range.re.hi - range.re.lo > 1e-12 * scale) return null;
  if (range.im.hi - range.im.lo > 1e-12 * scale) return null;
  return { re, im };
}

export function tExp(t: Node): Node {
  const node = noteExp(E(t, ONE), t);
  expArg.set(node, t);
  // exp(+∞) is a pole, so exp(+∞) − exp(+∞) is the indeterminate subtraction.
  // exp(−∞) stays a zero: exp(−∞) − exp(−∞) is 0.
  // A finite real past about 709 overflows float to +∞. The range stays
  // unknown, so the node has to be marked or exp(exp(800)) − itself folds to 0.
  if (t.type === "input" && t.value.re === Infinity && imagZero(t.value)) return noteNonfinite(node, 1);
  const known = knownValue(t);
  if (known && known.re === Infinity && imagZero(known)) return noteNonfinite(node, 1);
  if (known && known.re < 0 && !Number.isFinite(known.re)) return node;
  if (known && Number.isFinite(known.re) && known.re > 709 && Math.abs(known.im) < 1e-6) return noteNonfinite(node, 1);
  if (isNonfiniteNode(t) && !(known && known.re < 0)) return noteNonfinite(node, 1);
  return node;
}

export function tLn(t: Node): Node {
  const inner = onePlus.get(t);
  // ln(1+x) = x − x²/2 + … . The next term is below the 480-digit cap only for |x| ≤ 10^(−480).
  if (inner && tinyScale(inner, SERIES_REL) !== null) return markSeries(inner, "series shortcut: the leading term, for |x| ≤ 10^(−480)");
  return noteLn(E(ONE, E(E(ONE, t), ONE)), t);
}

export const tE = memo(() => tagReal(programNode("e"), Math.E));

export const tZero = memo(() => tagReal(programNode("0"), 0));

const cosArg = new WeakMap<Node, Node>();
const expArg = new WeakMap<Node, Node>();
const sqrtArg = new WeakMap<Node, Node>();
const onePlus = new WeakMap<Node, Node>();

/**
 * Odd functions and cos(x)−1 drop a relative x². That term is past 480 digits
 * only once |x| ≤ 10^(−241). exp(x)−1, ln(1+x), and sqrt(1+x)−1 drop a relative
 * x, which needs |x| ≤ 10^(−480). A larger argument keeps the real circuit.
 */
const SERIES_ODD = -241;
/**
 * Sin keeps at most four odd powers. |x| ≤ 10^(−61) is the widest argument
 * whose next term is past 480 digits with those three corrections.
 */
const SERIES_POLY = -61;
/**
 * tan, tanh, arctan, and cos(x)−1 carry enough terms for about |x| ≤ 10^(−20).
 * A wider argument stays on the circuit rather than a truncated polynomial.
 */
const SERIES_WIDE = -20;
const SERIES_REL = -480;
const LEAD_NOTE = "series shortcut: the leading term, for |x| ≤ 10^(−241)";
const POLY_NOTE = "series shortcut: odd powers kept until the remainder is past the 480-digit cap";
const seriesNotes = new WeakMap<Node, string>();

function markSeries(node: Node, note: string): Node {
  seriesNotes.set(node, note);
  return markSeriesShortcut(node);
}

/** The note for a result whose circuit used a series shortcut. Null when it did not. */
export function seriesShortcutNote(root: Node): string | null {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    const note = seriesNotes.get(node);
    if (note) return note;
    if (node.type === "eml") {
      if (node.a) stack.push(node.a);
      if (node.b) stack.push(node.b);
    }
  }
  return null;
}

/** Decade of a real known to sit in one power of ten, or null when it might not. */
function tinyScale(node: Node, limit: number): number | null {
  const decade = decadeOf(node);
  if (decade !== undefined && decade <= limit) return decade;
  const known = knownValue(node);
  if (known && known.im === 0 && Number.isFinite(known.re) && known.re !== 0) {
    const decadeKnown = Math.floor(Math.log10(Math.abs(known.re)));
    if (decadeKnown > limit) return null;
    return decadeKnown;
  }
  // 3·10^(−45) is a product, so its range is a few ulps wide and not a point.
  const range = rangeOf(node);
  if (!range.re || !range.im || range.im.lo !== 0 || range.im.hi !== 0) return null;
  const lo = range.re.lo;
  const hi = range.re.hi;
  if (!Number.isFinite(lo) || !Number.isFinite(hi) || lo === 0 || hi === 0 || Math.sign(lo) !== Math.sign(hi)) return null;
  const dLo = Math.floor(Math.log10(Math.abs(lo)));
  const dHi = Math.floor(Math.log10(Math.abs(hi)));
  if (dLo !== dHi || dLo > limit) return null;
  return dLo;
}

function realIsNegative(node: Node): boolean {
  const known = knownValue(node);
  if (known && known.im === 0 && known.re !== 0) return known.re < 0;
  const range = rangeOf(node);
  return !!range.re && range.re.hi < 0;
}

function isOneNode(node: Node): boolean {
  if (rangeOf(node).int === BigInt(1)) return true;
  const v = knownValue(node);
  return !!v && v.im === 0 && v.re === 1;
}

/**
 * cos(x) − 1 = −x²/2 + x⁴/24 − … . One term is past the 480-digit cap only for
 * |x| ≤ 10^(−241). Up to |x| ≤ 10^(−20) the even powers continue until the next
 * one is past that cap. A larger argument stays on the exp circuit.
 */
/** (2k)! for k = 1..13. 26! is 27 digits, inside the 40-digit integer builder. */
const COS_FACTORIAL = [
  "2",
  "24",
  "720",
  "40320",
  "3628800",
  "479001600",
  "87178291200",
  "20922789888000",
  "6402373705728000",
  "2432902008176640000",
  "1124000727777607680000",
  "620448401733239439360000",
  "403291461126605635584000000",
];

function cosMinusOne(a: Node, b: Node): Node | null {
  let arg: Node | undefined;
  let sign = 1;
  if (cosArg.has(a) && isOneNode(b)) {
    arg = cosArg.get(a);
    sign = 1;
  } else if (cosArg.has(b) && isOneNode(a)) {
    arg = cosArg.get(b);
    sign = -1;
  }
  const scale = arg ? tinyScale(arg, SERIES_WIDE) : null;
  if (!arg || scale === null) return null;
  const count = termCount(scale, COS_FACTORIAL.length);
  if (count === null) return null;
  // Negation of a float-sized 0 would become the −0 leaf. 10^(−400) is 0 in
  // float64 and a real decimal, so scale the square by −1 with the raw product.
  if (count === 1) {
    const halfSquare = tHalfOf(tMul(arg, arg));
    const series = sign > 0 ? rawMul(tNeg(ONE), halfSquare) : halfSquare;
    return markSeries(noteDecade(series, scale * 2), "series shortcut: −x²/2, for |x| ≤ 10^(−241)");
  }
  let power = rawMul(arg, arg);
  let acc: Node | null = null;
  for (let k = 1; k <= count; k += 1) {
    const den = COS_FACTORIAL[k - 1];
    if (!den) return null;
    // Dividing the power by the factorial collapses once the power underflows
    // in the float range. Multiply by the reciprocal instead.
    const mag = rawMul(power, tInv(digitsToInteger(1, den)));
    // cos(x)−1 has sign (−1)^k. 1−cos flips that.
    const negative = sign > 0 ? k % 2 === 1 : k % 2 === 0;
    if (acc === null) acc = negative ? rawMul(tNeg(ONE), mag) : mag;
    else acc = retainSum(acc, mag, scale * 2, negative);
    if (k < count) power = rawMul(power, rawMul(arg, arg));
  }
  if (!acc) return null;
  // The powers and the lift are not the expression's cancellation.
  // cos(x)−1 leads with −x²/2. 1−cos leads with the opposite sign.
  return markSeries(
    noteTinyReal(shieldLift(acc, [arg]), scale * 2, sign > 0),
    "series shortcut: even powers kept until the remainder is past the 480-digit cap",
  );
}

/** The circuit is chosen from the structural range of a and b. */
function expMinusOne(a: Node, b: Node): Node | null {
  if (expArg.has(a) && isOneNode(b)) {
    const arg = expArg.get(a);
    if (arg && tinyScale(arg, SERIES_REL) !== null) return markSeries(arg, "series shortcut: the leading term, for |x| ≤ 10^(−480)");
  }
  if (expArg.has(b) && isOneNode(a)) {
    const arg = expArg.get(b);
    if (arg && tinyScale(arg, SERIES_REL) !== null) return markSeries(rawMul(tNeg(ONE), arg), "series shortcut: the leading term, for |x| ≤ 10^(−480)");
  }
  return null;
}

function sqrtMinusOne(a: Node, b: Node): Node | null {
  if (!sqrtArg.has(a) || !isOneNode(b)) return null;
  const inner = sqrtArg.get(a);
  const scale = inner ? tinyScale(inner, SERIES_REL) : null;
  if (!inner || scale === null) return null;
  const half = tHalfOf(inner);
  return markSeries(noteDecade(half, scale - 1), "series shortcut: x/2, for |x| ≤ 10^(−480)");
}

export function tSub(a: Node, b: Node): Node {
  return cosMinusOne(a, b) ?? expMinusOne(a, b) ?? sqrtMinusOne(a, b) ?? domainSub(a, b);
}

export function tNeg(b: Node): Node {
  return domainNeg(b);
}

function largeRealSum(a: Node, b: Node): Node | null {
  const da = decadeOf(a);
  const db = decadeOf(b);
  if (da === undefined || db === undefined || Math.abs(da - db) > 24) return null;
  const k = Math.max(da, db);
  if (k < 300) return null;
  const scale = pow10(k);
  const node = rawMul(scale, domainAdd(rawDiv(a, scale), rawDiv(b, scale)));
  return noteDecade(node, k);
}

export function tAdd(a: Node, b: Node): Node {
  const large = largeRealSum(a, b);
  if (large) return large;
  const node = domainAdd(a, b);
  if (isOneNode(a)) onePlus.set(node, b);
  else if (isOneNode(b)) onePlus.set(node, a);
  return node;
}

export function tInv(b: Node): Node {
  return rawDiv(ONE, b);
}

function exactZero(node: Node): boolean {
  return rangeOf(node).int === BigInt(0);
}

function negativeFactor(node: Node): boolean {
  const v = knownValue(node);
  if (!v || !(v.im === 0 || Object.is(v.im, -0))) return false;
  return v.re < 0 || Object.is(v.re, -0);
}

export function tMul(a: Node, b: Node): Node {
  // 0 · ∞ is indeterminate. Typed infinity and division by the integer 0 are both non-finite.
  if ((exactZero(a) && isNonfiniteNode(b)) || (exactZero(b) && isNonfiniteNode(a))) {
    const pole = isNonfiniteNode(a) ? a : b;
    return naiveIndeterminate(pole);
  }
  // 0 · (−1) is the −0 leaf. The product program collapses that sign.
  if (exactZero(a) && negativeFactor(b)) return negativeZero();
  if (exactZero(b) && negativeFactor(a)) return negativeZero();
  return rawMul(a, b);
}

function naiveIndeterminate(pole: Node): Node {
  return naiveSub(pole, pole);
}

function expArgument(node: Node): Node | null {
  if (node.type === "eml" && node.b.type === "one") return node.a;
  return null;
}

function moderateExponent(node: Node): boolean {
  const re = rangeOf(node).re;
  if (rangeOf(node).int !== undefined) return true;
  if (!re) return false;
  return Math.abs(re.lo) < 40 && Math.abs(re.hi) < 40;
}

export function tDiv(a: Node, b: Node): Node {
  // exp(u)/exp(v) = exp(u − v) when the exponents are integers or small,
  // so exp(800)/exp(799) is e and not ∞/∞. A large complex exponent keeps
  // the quotient: rewriting it overflows.
  const u = expArgument(a);
  const v = expArgument(b);
  if (u && v && moderateExponent(u) && moderateExponent(v)) return tExp(tSub(u, v));
  return rawDiv(a, b);
}

export function tPow(a: Node, b: Node): Node {
  const node = applyProgram("pow", { x: a, y: b });
  const ia = rangeOf(a).int;
  const ib = rangeOf(b).int;
  if (ia !== undefined && ib !== undefined && ib >= BigInt(0) && ib <= BigInt(10000)) {
    return tagInteger(node, ia ** ib);
  }
  const va = knownValue(a);
  const vb = knownValue(b);
  if (va && vb && va.im === 0 && vb.im === 0 && va.re > 0 && Number.isFinite(vb.re)) {
    const re = va.re ** vb.re;
    if (Number.isFinite(re)) tagReal(node, re);
  }
  return node;
}

export function tSqr(t: Node): Node {
  const node = applyProgram("sqr", { x: t });
  const v = knownValue(t);
  if (!v) return node;
  return tagValue(node, { re: v.re * v.re - v.im * v.im, im: 2 * v.re * v.im });
}

export const tMinusOne = memo(() => tagReal(programNode("-1"), -1));

export const tTwo = memo(() => tagReal(programNode("2"), 2));

export const tHalf = memo(() => tagReal(programNode("1/2"), 0.5));

export const tThree = memo(() => tagReal(programNode("3"), 3));

export const tTwoThirds = memo(() => tDiv(tTwo(), tThree()));

export function tSqrt(t: Node): Node {
  const v = knownValue(t);
  // sqrt(−0) is −0. The short word returns +0, and 1 over that is the wrong infinity.
  if (v && Object.is(v.re, -0) && imagZero(v)) return negativeZero();
  const node = applyProgram("sqrt", { x: t });
  const inner = onePlus.get(t);
  if (inner && tinyScale(inner, SERIES_REL) !== null) sqrtArg.set(node, inner);
  if (!v) return node;
  if (v.im === 0 && v.re >= 0) return tagReal(node, Math.sqrt(v.re));
  const ax = Math.abs(v.re);
  const ay = Math.abs(v.im);
  const s = Math.sqrt((ax + Math.hypot(v.re, v.im)) / 2);
  const d = s === 0 ? 0 : ay / (2 * s);
  return tagValue(node, v.re >= 0 ? { re: s, im: Math.sign(v.im) * d } : { re: d, im: Math.sign(v.im || 1) * s });
}

export const tSqrt2 = memo(() => tagReal(programNode("sqrt2"), Math.SQRT2));

export const tI = memo(() => tagValue(programNode("i"), { re: 0, im: 1 }));

export const tPi = memo(() => tagReal(programNode("pi"), Math.PI));

export function tHalfOf(t: Node): Node {
  return rawMul(t, tHalf());
}

export function tSigmoid(t: Node): Node {
  return tInv(tAdd(ONE, tExp(tNeg(t))));
}

export function tSinh(t: Node): Node {
  const known = tightValue(t);
  // sinh z = z + z³/6. Below about 10^(−6) the cubic is dust, and the exp formula is not.
  if (known && Math.hypot(known.re, known.im) < 1e-6) return t;
  // exp(t)/2 · (1 − exp(−2t)). Subtracting the real 1 keeps exp(t) out of the exponent.
  const em2 = tExp(tNeg(tAdd(t, t)));
  return tHalfOf(tMul(tExp(t), tSub(ONE, em2)));
}

export function tCosh(t: Node): Node {
  const em2 = tExp(tNeg(tAdd(t, t)));
  return tHalfOf(tMul(tExp(t), tSub(ONE, tNeg(em2))));
}

export function tTanh(t: Node): Node {
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, TANH_ODD, SERIES_WIDE);
  if (series) return series;
  // (e^{2t} − 1) / (e^{2t} + 1). The +1 is a subtraction of −1, so the huge term is not exponentiated again.
  const e2 = tExp(tAdd(t, t));
  return tDiv(tSub(e2, ONE), tSub(e2, tMinusOne()));
}

/**
 * Remember the argument. The pole and large-angle flags are decided from its
 * value at evaluation, so tan(3π/2) is a pole even when the product has no range.
 */
function flagAngle(node: Node, arg: Node, tan: boolean): Node {
  notePrecision(node, { kind: tan ? "pole" : "trig", arg });
  return node;
}

/**
 * sin, tan, tanh, and arctan of a real x equal x once x³ is past the 480-digit
 * cap, which is |x| ≤ 10^(−241). A larger argument keeps the circuit. The mark
 * stops a later x − f(x) from certifying the shortcut's zero.
 */
function tinyRealArgument(t: Node): Node | null {
  if (tinyScale(t, SERIES_ODD) === null) return null;
  return markSeries(t, LEAD_NOTE);
}

type SignedRatio = { num: string; den: string; sign: -1 | 1 };

/**
 * How many powers to keep so the next one is past the 480-digit cap.
 * Each extra power of x² sits 2|log10 x| digits below the previous one.
 * Null when the coefficient list runs out while that next term is still visible.
 */
function termCount(decade: number, maxTerms: number): number | null {
  const depth = -decade;
  let terms = 1;
  while (depth * 2 * terms <= 480 && terms < maxTerms) terms += 1;
  if (depth * 2 * terms <= 480) return null;
  return terms;
}

function rationalNode(num: string, den: string): Node {
  const top = num === "1" ? ONE : digitsToInteger(1, num);
  return tDiv(top, digitsToInteger(1, den));
}

/**
 * Add or subtract a correction that may sit far below `acc`.
 * Lift both by a power of ten so the exact circuit can see the small term,
 * then scale back. The lift's own cancellation is not the result's work.
 */
function retainSum(acc: Node, term: Node, leadDecade: number, subtract: boolean): Node {
  const k = Math.max(0, -leadDecade);
  if (k === 0) return subtract ? naiveSub(acc, term) : naiveSub(acc, rawMul(tMinusOne(), term));
  const scale = pow10(Math.min(k, 900));
  const liftedA = rawMul(acc, scale);
  const liftedB = rawMul(term, scale);
  const mixed = subtract ? naiveSub(liftedA, liftedB) : naiveSub(liftedA, rawMul(tMinusOne(), liftedB));
  return shieldLift(rawDiv(mixed, scale), [acc, term]);
}

/**
 * x plus the next odd powers. The leading term alone is only past the cap for
 * |x| ≤ 10^(−241). This is an accelerator: a zero that comes out of it is not certified.
 */
function oddSeries(t: Node, corrections: SignedRatio[], limit: number): Node | null {
  const scale = tinyScale(t, limit);
  if (scale === null || scale <= SERIES_ODD) return null;
  const count = termCount(scale, corrections.length + 1);
  if (count === null || count < 2) return null;
  let acc = t;
  let power = t;
  for (let i = 0; i < count - 1; i += 1) {
    const coeff = corrections[i];
    if (!coeff) return null;
    power = rawMul(power, rawMul(t, t));
    const term = rawMul(rationalNode(coeff.num, coeff.den), power);
    acc = retainSum(acc, term, scale, coeff.sign < 0);
  }
  // Coefficients and the lift are not the expression's cancellation. The argument is.
  return markSeries(noteTinyReal(shieldLift(acc, [t]), scale, realIsNegative(t)), POLY_NOTE);
}

/** sin x = x − x³/6 + x⁵/120 − x⁷/5040 + … */
const SIN_ODD: SignedRatio[] = [
  { num: "1", den: "6", sign: -1 },
  { num: "1", den: "120", sign: 1 },
  { num: "1", den: "5040", sign: -1 },
];

/**
 * tan x = x + (1/3)x³ + (2/15)x⁵ + … through x²⁵.
 * The fractions are the Taylor coefficients; every sign is positive.
 */
const TAN_ODD: SignedRatio[] = [
  { num: "1", den: "3", sign: 1 },
  { num: "2", den: "15", sign: 1 },
  { num: "17", den: "315", sign: 1 },
  { num: "62", den: "2835", sign: 1 },
  { num: "1382", den: "155925", sign: 1 },
  { num: "21844", den: "6081075", sign: 1 },
  { num: "929569", den: "638512875", sign: 1 },
  { num: "6404582", den: "10854718875", sign: 1 },
  { num: "443861162", den: "1856156927625", sign: 1 },
  { num: "18888466084", den: "194896477400625", sign: 1 },
  { num: "113927491862", den: "2900518163668125", sign: 1 },
  { num: "58870668456604", den: "3698160658676859375", sign: 1 },
];

/** tanh has the same absolute coefficients, with the x³ term negative. */
const TANH_ODD: SignedRatio[] = TAN_ODD.map((coeff, i) => ({ ...coeff, sign: i % 2 === 0 ? -1 : 1 }));

/** arctan x = x − x³/3 + x⁵/5 − x⁷/7 + … through x²⁵. */
const ARCTAN_ODD: SignedRatio[] = Array.from({ length: 12 }, (_, i) => ({
  num: "1",
  den: String(2 * (i + 1) + 1),
  sign: (i % 2 === 0 ? -1 : 1) as -1 | 1,
}));

export function tSin(t: Node): Node {
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, SIN_ODD, SERIES_POLY);
  if (series) return series;
  const it = tMul(tI(), t);
  const num = tSub(tExp(it), tExp(tNeg(it)));
  return flagAngle(tDiv(num, tMul(tTwo(), tI())), t, false);
}

export function tCos(t: Node): Node {
  const it = tMul(tI(), t);
  const node = flagAngle(tHalfOf(tAdd(tExp(it), tExp(tNeg(it)))), t, false);
  cosArg.set(node, t);
  return node;
}

export function tTan(t: Node): Node {
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, TAN_ODD, SERIES_WIDE);
  if (series) return series;
  // tan(z) = −i tanh(i z), and tanh(w) = 1 − 2/(exp(2w)+1).
  // A large positive exponent overflows to +∞ and the quotient vanishes,
  // so the same circuit covers both signs of Im(z). sin/cos does not.
  const w = tMul(tI(), t);
  const grown = tExp(tMul(tTwo(), w));
  const tanh = tSub(ONE, tDiv(tTwo(), tAdd(grown, ONE)));
  return flagAngle(tMul(tNeg(tI()), tanh), t, true);
}

/** The sign of Im(t) when the range proves it. 0 is a proven real. null is unknown. */
function provenImagSign(t: Node): 1 | -1 | 0 | null {
  const range = rangeOf(t);
  if (range.int !== undefined) return 0;
  if (!range.im) return null;
  if (range.im.lo === 0 && range.im.hi === 0) return 0;
  if (range.im.lo > 0) return 1;
  if (range.im.hi < 0) return -1;
  return null;
}

function realBounds(t: Node): { lo: number; hi: number } | null {
  const range = rangeOf(t);
  if (range.int !== undefined) {
    const n = Number(range.int);
    return Number.isFinite(n) ? { lo: n, hi: n } : null;
  }
  return range.re;
}

/** The raw sub program keeps a tiny imaginary part. It needs a moderate real subtrahend. */
function rawSubtrahendOk(t: Node): boolean {
  const range = rangeOf(t);
  if (range.int !== undefined) return range.int > BigInt(-700) && range.int < BigInt(700);
  if (!range.re || !range.im) return false;
  const edge = Math.PI - 1e-3;
  return range.re.lo > -700 && range.re.hi < 700 && range.im.lo > -edge && range.im.hi < edge;
}

function minMagnitude(t: Node): number {
  const re = realBounds(t);
  const im = rangeOf(t).int !== undefined ? { lo: 0, hi: 0 } : rangeOf(t).im;
  if (!re || !im) return 0;
  const gap = (iv: { lo: number; hi: number }) => (iv.lo > 0 ? iv.lo : iv.hi < 0 ? -iv.hi : 0);
  return Math.hypot(gap(re), gap(im));
}

/**
 * √(1 − t), principal. On the real cut t > 1 the value is +i√(t − 1), the bank
 * reached from below (counter-clockwise, the same as mpmath). A proven sign of
 * Im t uses ∓i·√(t − 1). Otherwise −(t − 1).
 */
function sqrtOneMinus(t: Node): Node {
  const re = realBounds(t);
  const side = provenImagSign(t);
  if (re && re.lo > 1 && side !== null) {
    const turn = side > 0 ? tNeg(tI()) : tI();
    return tMul(turn, tSqrt(naiveSub(t, ONE)));
  }
  if (re && re.hi < 1 && rawSubtrahendOk(t)) return tSqrt(naiveSub(ONE, t));
  return tSqrt(rawMul(tMinusOne(), naiveSub(t, ONE)));
}

/** √(1 + t), principal. On the real cut t < −1 the value is +i√(−1 − t). */
function sqrtOnePlus(t: Node): Node {
  const re = realBounds(t);
  const side = provenImagSign(t);
  if (re && re.hi < -1 && side !== null) {
    const turn = side < 0 ? tNeg(tI()) : tI();
    const m = rawSubtrahendOk(t) ? naiveSub(tMinusOne(), t) : rawMul(tMinusOne(), naiveSub(t, tMinusOne()));
    return tMul(turn, tSqrt(m));
  }
  return tSqrt(naiveSub(t, tMinusOne()));
}

/** z + z³/6 + 3z⁵/40. */
function arcsinSeries(t: Node): Node {
  const z2 = tSqr(t);
  const z3 = tMul(z2, t);
  const z5 = tMul(z3, z2);
  return tAdd(t, tAdd(tDiv(z3, integerNode(6)), tDiv(tMul(tThree(), z5), integerNode(40))));
}

/**
 * Principal arcsin, the same circuit in both modes.
 * For a real x > 1, arcsin(x) = π/2 − i·arcosh(x). For x < −1 it is the odd
 * extension, −π/2 + i·arcosh(−x). A point just above the cut has positive
 * imaginary part. S = √(1 − t)·√(1 + t), not the square root of the product,
 * so each cut keeps its own side. A variable has no proven half-plane, so the
 * sign is csgn(ln(it + S) + 10i). A float disagreement next to the cut is
 * flagged against the exact value. It is not given another formula.
 */
export function tArcsin(t: Node): Node {
  const known = knownValue(t);
  if (known && (known.im === 0 || Object.is(known.im, -0)) && (known.re === 1 || known.re === -1)) {
    const half = tHalfOf(tPi());
    return known.re < 0 ? tNeg(half) : half;
  }
  if (rangeOf(t).int === BigInt(0)) return tZero();
  const box = asinhBox(t);
  if (box !== null && box < 1e-4) return arcsinSeries(t);
  const re = realBounds(t);
  const side = provenImagSign(t);
  const lower = side === 1 || (side === 0 && !!re && re.hi < 0);
  if (side !== null && minMagnitude(t) > 1e10) {
    if (lower) return tMul(tI(), tAdd(tLn(tTwo()), tLn(tMul(tNeg(tI()), t))));
    return tMul(tNeg(tI()), tAdd(tLn(tTwo()), tLn(tMul(tI(), t))));
  }
  const rad = tMul(sqrtOneMinus(t), sqrtOnePlus(t));
  const it = tMul(tI(), t);
  const upper = side === -1 || (side === 0 && !!re && re.lo >= 0);
  if (lower) return tMul(tI(), tLn(tSub(rad, it)));
  if (upper) return tMul(tNeg(tI()), tLn(tAdd(it, rad)));
  const lnP = tLn(tAdd(it, rad));
  const z = tAdd(lnP, tMul(integerNode(10), tI()));
  const sigma = tDiv(tSqrt(tSqr(z)), z);
  return tMul(tMul(tNeg(tI()), sigma), tLn(tAdd(tMul(sigma, it), rad)));
}

export function tArccos(t: Node): Node {
  const known = tightValue(t);
  if (known && imagZero(known) && known.re === 1) return tZero();
  if (known && imagZero(known) && known.re === -1) return tPi();
  // acos = π/2 − asin, so a real x > 1 has positive imaginary part.
  return tSub(tHalfOf(tPi()), tArcsin(t));
}

export function tArctan(t: Node): Node {
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, ARCTAN_ODD, SERIES_WIDE);
  if (series) return series;
  // A pure imaginary iy with |y| > 1 is i·artanh(y) on this cut.
  // artanh(−2) = −artanh(2), so arctan(−2i) = −π/2 − (artanh 2) i.
  const range = rangeOf(t);
  if (range.re && range.im && Math.abs(range.re.lo) < 1e-6 && Math.abs(range.re.hi) < 1e-6 && (range.im.lo > 1 || range.im.hi < -1)) {
    return tMul(tI(), tArtanh(tMul(tNeg(tI()), t)));
  }
  const it = tMul(tI(), t);
  return tDiv(tLn(tDiv(tAdd(ONE, it), tSub(ONE, it))), tMul(tTwo(), tI()));
}

function asinhBox(t: Node): number | null {
  const range = rangeOf(t);
  if (!range.re || !range.im) return null;
  const ends = [range.re.lo, range.re.hi, range.im.lo, range.im.hi];
  if (!ends.every((end) => Number.isFinite(end))) return null;
  const re = Math.max(Math.abs(range.re.lo), Math.abs(range.re.hi));
  const im = Math.max(Math.abs(range.im.lo), Math.abs(range.im.hi));
  return Math.hypot(re, im);
}

/** True when every value in the range has magnitude at least `limit`. */
function asinhOutside(t: Node, limit: number): boolean {
  const range = rangeOf(t);
  if (!range.re || !range.im) return false;
  return range.re.lo >= limit || range.re.hi <= -limit || range.im.lo >= limit || range.im.hi <= -limit;
}

/**
 * arsinh(t) = −i·arcsin(i·t). With arcsin's counter-clockwise cut, this is
 * arcosh(y) + iπ/2 for iy with y > 1, and the odd value for −iy.
 * ±i are matched only as the i program itself: a float near ±i is not that node.
 */
export function tArsinh(t: Node): Node {
  const known = knownValue(t);
  if ((known && known.re === 0 && (known.im === 0 || Object.is(known.im, -0))) || rangeOf(t).int === BigInt(0)) return tZero();
  if (t === tI() || t === tNeg(tI())) {
    const quarter = tMul(tI(), tHalfOf(tPi()));
    return t === tI() ? quarter : tNeg(quarter);
  }
  const node = tMul(tNeg(tI()), tArcsin(tMul(tI(), t)));
  if (!asinhOutside(t, 1e-4)) notePrecision(node, { kind: "asinh", arg: t });
  return node;
}

/** Principal arcosh: ln(z + sqrt(z−1)·sqrt(z+1)). sqrt(z²−1) flips the real part for Re(z) < −1. */
export function tArcosh(t: Node): Node {
  const rad = tMul(tSqrt(tSub(t, ONE)), tSqrt(tAdd(t, ONE)));
  return tLn(tAdd(t, rad));
}

/**
 * ½ ln|(1+x)/(1−x)| − iπ/2 for a real x > 1.
 * (1+x)/(1−x) is negative, and this cut's log of a negative real has argument −π,
 * so the half-turn is the lower bank. This matches mpmath's atanh.
 * C99 catanh of a real above 1, with a +0 imaginary part, returns +iπ/2.
 */
function artanhAboveOne(t: Node): Node {
  const ratio = tDiv(tAdd(t, ONE), tSub(t, ONE));
  return tSub(tHalfOf(tLn(tAbs(ratio))), tMul(tI(), tHalfOf(tPi())));
}

export function tArtanh(t: Node): Node {
  const known = tightValue(t);
  if (known && Math.hypot(known.re, known.im) < 1e-6) return t;
  if (known && imagZero(known) && known.re > 1) return artanhAboveOne(t);
  if (known && imagZero(known) && known.re < -1) return tNeg(artanhAboveOne(tNeg(t)));
  return tHalfOf(tLn(tDiv(tAdd(ONE, t), tSub(ONE, t))));
}

export function tLogBase(base: Node, value: Node): Node {
  return applyProgram("log", { x: base, y: value });
}

export function tAvg(a: Node, b: Node): Node {
  return tHalfOf(tAdd(a, b));
}

function tAbs(t: Node): Node {
  const known = knownValue(t);
  if (known && known.im === 0) return known.re < 0 ? tNeg(t) : t;
  return tSqrt(tSqr(t));
}

export function tHypot(a: Node, b: Node): Node {
  const va = knownValue(a);
  const vb = knownValue(b);
  if (va && vb && va.im === 0 && vb.im === 0) {
    if (va.re === 0 && vb.re === 0) return tZero();
    const ma = Math.abs(va.re);
    const mb = Math.abs(vb.re);
    if (ma === 0) return tAbs(b);
    if (mb === 0) return tAbs(a);
    const moderate = ma < 1e150 && mb < 1e150 && ma > 1e-150 && mb > 1e-150;
    if (moderate) return tSqrt(tAdd(tSqr(a), tSqr(b)));
    const big = ma >= mb ? a : b;
    const small = ma >= mb ? b : a;
    return tMul(tAbs(big), tSqrt(tAdd(ONE, tSqr(tDiv(small, big)))));
  }
  return tSqrt(tAdd(tSqr(a), tSqr(b)));
}

const intCache = new Map<number, Node>();

/** Non-negative and negative integers, built from the constant 1. */
export function integerNode(n: number): Node {
  if (!Number.isInteger(n) || !Number.isSafeInteger(n)) {
    throw new Error(`Cannot build ${n} from 1.`);
  }
  const hit = intCache.get(n);
  if (hit) return hit;
  return isolateCircuit(() => integerNodeBuild(n));
}

function integerNodeBuild(n: number): Node {
  beginInteger(n);
  let node: Node;
  try {
    if (n === 0) node = tZero();
    else if (n === 1) node = ONE;
    else if (n === 2) node = tTwo();
    else if (n === -1) node = tMinusOne();
    else if (n === 3) node = tThree();
    else if (n < 0) node = tNeg(integerNode(-n));
    else if (n % 2 === 0) node = tMul(integerNode(n / 2), tTwo());
    else node = tAdd(integerNode(n - 1), ONE);
  } finally {
    endInteger(n);
  }
  tagReal(node, n);
  intCache.set(n, node);
  return node;
}

installIntegerBuilder(integerNode);

/**
 * A decimal literal. Integers and short decimals become pure EML circuits.
 * Anything too large to build from 1 is an input terminal.
 */
function digitsToInteger(sign: number, digits: string): Node {
  const body = digits.replace(/^0+(?=\d)/, "") || "0";
  if (body.length > 40) throw new EmlError("That integer is too long to build from 1.");
  if (body.length <= 15) {
    const n = Number(body);
    if (Number.isSafeInteger(n)) return integerNode(sign * n);
  }
  let node = tZero();
  const ten = integerNode(10);
  for (const ch of body) node = tAdd(tMul(node, ten), integerNode(Number(ch)));
  return sign < 0 ? tNeg(node) : node;
}

function pow10(exp: number): Node {
  if (exp === 0) return ONE;
  let result: Node = ONE;
  let base = integerNode(10);
  let n = exp;
  while (n > 0) {
    if (n % 2 === 1) result = tMul(result, base);
    n = Math.floor(n / 2);
    if (n > 0) base = tMul(base, base);
  }
  return result;
}

export function literalNode(text: string): Node {
  return isolateCircuit(() => literalNodeBuild(text));
}

function literalNodeBuild(text: string): Node {
  const trimmed = text.trim();
  if (!trimmed) throw new EmlError(`Cannot read the number ${text}.`);
  if (/^[+-]?0[xob]/i.test(trimmed)) throw new EmlError(`Cannot read the number ${text}.`);
  if (/^-0(?:\.0+)?(?:[eE][+-]?\d+)?$/.test(trimmed)) return negativeZero();
  if (!Number.isFinite(Number(trimmed)) && /^[+-]?(?:inf|infinity)$/i.test(trimmed)) {
    const negative = trimmed.startsWith("-");
    return noteNonfinite(input({ re: negative ? -Infinity : Infinity, im: 0 }, trimmed), negative ? -1 : 1);
  }
  const sci = /^([+-]?)(\d+)(?:\.(\d+))?[eE]([+-]?\d+)$/.exec(trimmed);
  if (sci) {
    const sign = sci[1] === "-" ? -1 : 1;
    const exp = Number(sci[4]);
    const frac = sci[3] ?? "";
    const digits = `${sci[2]}${frac}`.replace(/^0+(?=\d)/, "") || "0";
    const expAdj = exp - frac.length;
    if (digits.length > 40) throw new EmlError("That integer is too long to build from 1.");
    if (!Number.isInteger(exp) || Math.abs(expAdj) > 1_000_000) {
      throw new EmlError("That exponent is too large to build.");
    }
    const magnitude =
      expAdj >= 0 ? tMul(digitsToInteger(1, digits), pow10(expAdj)) : tDiv(digitsToInteger(1, digits), pow10(-expAdj));
    const signed = sign < 0 ? tNeg(magnitude) : magnitude;
    noteDecade(signed, expAdj);
    const numeric = Number(trimmed);
    return Number.isFinite(numeric) && numeric !== 0 ? tagReal(signed, numeric) : signed;
  }
  if (/^[+-]?\d+$/.test(trimmed)) {
    return digitsToInteger(trimmed.startsWith("-") ? -1 : 1, trimmed.replace(/^[+-]/, ""));
  }
  const match = /^([+-]?)(\d*)(?:\.(\d*))?$/.exec(trimmed);
  if (match && (match[2] || match[3])) {
    const sign = match[1] === "-" ? -1 : 1;
    const whole = match[2] || "0";
    const frac = match[3] ?? "";
    const digits = `${whole}${frac}`.replace(/^0+(?=\d)/, "") || "0";
    if (!frac) {
      const wholeNode = digitsToInteger(sign, digits);
      return wholeNode;
    }
    if (digits.length <= 40 && frac.length <= 40) {
      const magnitude = tDiv(digitsToInteger(1, digits), pow10(frac.length));
      return sign < 0 ? tNeg(magnitude) : magnitude;
    }
  }
  throw new EmlError(`Cannot read the number ${text}.`);
}

export const unaryBuilders: Record<string, (t: Node) => Node> = {
  exp: tExp,
  ln: tLn,
  inv: tInv,
  half: tHalfOf,
  minus: tNeg,
  sqr: tSqr,
  sqrt: tSqrt,
  sigma: tSigmoid,
  sin: tSin,
  cos: tCos,
  tan: tTan,
  arcsin: tArcsin,
  arccos: tArccos,
  arctan: tArctan,
  sinh: tSinh,
  cosh: tCosh,
  tanh: tTanh,
  arsinh: tArsinh,
  arcosh: tArcosh,
  artanh: tArtanh,
};

export const binaryBuilders: Record<string, (a: Node, b: Node) => Node> = {
  add: tAdd,
  sub: tSub,
  mul: tMul,
  div: tDiv,
  pow: tPow,
  log: tLogBase,
  avg: tAvg,
  hypot: tHypot,
};

const constantBuilders: Record<string, () => Node> = {
  "1": () => ONE,
  e: tE,
  "0": tZero,
  "-1": tMinusOne,
  "2": tTwo,
  "1/2": tHalf,
  "2/3": tTwoThirds,
  "sqrt(2)": tSqrt2,
  i: tI,
  pi: tPi,
};

const unaryCache = new Map<string, Node>();
const binaryCache = new Map<string, Node>();

export function constantNode(name: string): Node {
  const build = constantBuilders[name];
  if (!build) throw new Error(`Unknown constant ${name}.`);
  return isolateCircuit(build);
}

export function unaryNode(name: string): Node {
  const hit = unaryCache.get(name);
  if (hit) return hit;
  return isolateCircuit(() => {
    const build = unaryBuilders[name];
    if (!build) throw new Error(`Unknown function ${name}.`);
    const node = build(X);
    unaryCache.set(name, node);
    return node;
  });
}

export function binaryNode(name: string): Node {
  const hit = binaryCache.get(name);
  if (hit) return hit;
  return isolateCircuit(() => {
    const build = binaryBuilders[name];
    if (!build) throw new Error(`Unknown operation ${name}.`);
    const node = build(X, Y);
    binaryCache.set(name, node);
    return node;
  });
}

/** Build a unary program on a concrete argument. */
export function applyUnaryNode(name: string, arg: Node): Node {
  const build = unaryBuilders[name];
  if (!build) throw new Error(`Unknown function ${name}.`);
  return isolateCircuit(() => build(arg));
}

/** Build a binary program on concrete arguments. */
export function applyBinaryNode(name: string, a: Node, b: Node): Node {
  const build = binaryBuilders[name];
  if (!build) throw new Error(`Unknown operation ${name}.`);
  return isolateCircuit(() => build(a, b));
}

export const CONSTANT_KEYS: { id: string; label: string }[] = [
  { id: "e", label: "e" },
  { id: "pi", label: "π" },
  { id: "i", label: "i" },
  { id: "0", label: "0" },
  { id: "-1", label: "−1" },
  { id: "2", label: "2" },
  { id: "1/2", label: "½" },
  { id: "sqrt(2)", label: "√2" },
];

export const UNARY_KEYS: { id: string; label: string }[] = [
  { id: "exp", label: "exp" },
  { id: "ln", label: "ln" },
  { id: "sqrt", label: "√" },
  { id: "sqr", label: "x²" },
  { id: "inv", label: "1/x" },
  { id: "minus", label: "±" },
  { id: "sin", label: "sin" },
  { id: "cos", label: "cos" },
  { id: "tan", label: "tan" },
  { id: "arcsin", label: "asin" },
  { id: "arccos", label: "acos" },
  { id: "arctan", label: "atan" },
  { id: "sinh", label: "sinh" },
  { id: "cosh", label: "cosh" },
  { id: "tanh", label: "tanh" },
  { id: "arsinh", label: "asinh" },
  { id: "sigma", label: "σ" },
];

export const BINARY_KEYS: { id: string; label: string; hint: string }[] = [
  { id: "add", label: "+", hint: "x + y" },
  { id: "sub", label: "−", hint: "x − y" },
  { id: "mul", label: "×", hint: "x × y" },
  { id: "div", label: "÷", hint: "x ÷ y" },
  { id: "pow", label: "xʸ", hint: "x^y" },
  { id: "log", label: "logₓy", hint: "log base x of y" },
  { id: "avg", label: "avg", hint: "(x + y) / 2" },
  { id: "hypot", label: "hypot", hint: "√(x² + y²)" },
];

/**
 * A named variable. The number stays in the caller's environment, so a chained
 * stack of programs is still a 1-and-EML circuit and not a stored float.
 */
export function bindInput(_value: C, label: string): Node {
  return V(label);
}

/** A number, or the name pi, e, or i, as a stack terminal. */
export function scalarNode(text: string): Node {
  const key = text.trim().toLowerCase().replace(/π/g, "pi");
  if (key === "pi" || key === "e" || key === "i") return constantNode(key);
  if (key === "inf" || key === "infinity" || key === "+inf" || key === "+infinity") return literalNode("inf");
  if (key === "-inf" || key === "-infinity") return literalNode("-inf");
  if (!text.trim()) throw new EmlError("Enter a number, pi, e, i, or inf.");
  try {
    return literalNode(text.trim());
  } catch {
    throw new EmlError(`“${text.trim()}” is not a number.`);
  }
}
