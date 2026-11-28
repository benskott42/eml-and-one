import type { C } from "./complex";
import {
  beginInteger,
  buildingInteger,
  carryTinyScale,
  domainAdd,
  domainNeg,
  domainSub,
  endInteger,
  decadeOf,
  hiddenUnderflow,
  integerQuotient,
  isLostTiny,
  isNegationPair,
  isNonfiniteNode,
  knownValue,
  mayBeInfinite,
  markInfiniteSource,
  markMaybeInfinite,
  noteDecade,
  noteLostTiny,
  provenFinite,
  noteTinyReal,
  naiveSub,
  negativeZero,
  shieldLift,
  noteExp,
  noteLn,
  noteNonfinite,
  noteOverflow,
  rangeOf,
  sumOfNegation,
  tagInteger,
  rawDiv,
  rawMul,
  tagReal,
  tagValue,
  installIntegerBuilder,
  markExactInt,
} from "./lowering";
import { E, EmlError, ONE, circuitStats, evaluateReport, freshInput, freshOne, isolateCircuit, onCircuitIsolate, type Node, V, input, notePrecision } from "./node";
import { SHORT_PROGRAMS, applyProgram, programNode } from "./programs";
import { DECIMAL_SCALE_MAX, type Rational, derive, isRecognized, derivePow, exactDecimalOf, exactNthRoot, exactRationalOf, factsOf, isExactUnsure, isUnverified, learn, markExactUnsure, markRecognized, markSeriesError, markSeriesShortcut, markUnverified, maxSeriesErrorExp, noteBuiltFrom, noteExactDecimal, provenInteger, recognizedNoteFrom, recordedDirection, seriesShortcutNoteFrom } from "./facts";

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
  hugeAngleBuilt = false;
  for (const reset of memoResets) reset();
  intCache.clear();
  unaryCache.clear();
  binaryCache.clear();
});

function imagZero(v: { re: number; im: number }): boolean {
  return v.im === 0 || Object.is(v.im, -0);
}

/** The recorded multiple of π on the real axis (q·π), or null. See facts.ts. */
function piOf(node: Node): Rational | null {
  const angle = factsOf(node).angle;
  return angle && angle.unit === "real" ? angle.q : null;
}

/** π/2 + kπ, written as an odd multiple of π/2. A nearby float is not this. */
function isSymbolicTanPole(arg: Node): boolean {
  const coeff = piOf(arg);
  if (!coeff) return false;
  const twice = BigInt(2) * coeff.n;
  if (twice % coeff.d !== BigInt(0)) return false;
  return (twice / coeff.d) % BigInt(2) !== BigInt(0);
}

/** The coefficient of π in twelfths, mod 24 (one full turn), when it is a whole number of them. */
function piTwelfths(arg: Node): number | null {
  const coeff = piOf(arg);
  if (!coeff) return null;
  const scaled = BigInt(12) * coeff.n;
  if (scaled % coeff.d !== BigInt(0)) return null;
  const k = (scaled / coeff.d) % BigInt(24);
  return Number(k < BigInt(0) ? k + BigInt(24) : k);
}

/**
 * sin at a multiple of π/6 where the value is 0, ±1/2 or ±1. The gates leave a
 * residue near 10^(−16) there, which exact mode refuses: sin(π), cos(π/2) and
 * sin(π/6) − 1/2 said "couldn't verify". The angle is the recorded multiple of π,
 * not a float near it. ±√3/2 keeps its circuit.
 */
/** Mark an exact-recognition result without mutating the shared `ONE` singleton or interned input leaves. */
function recognized(node: Node): Node {
  if (node === ONE) return markRecognized(freshOne());
  if (node.type === "input") return markRecognized(freshInput(node.value, node.label));
  return markRecognized(node);
}

function sinAtPiMultiple(twelfths: number | null): Node | null {
  if (twelfths === null || twelfths % 2 !== 0) return null;
  const sixths = (twelfths / 2) % 12;
  if (sixths === 0 || sixths === 6) return recognized(tZero());
  if (sixths === 3) return recognized(ONE);
  if (sixths === 9) return recognized(tMinusOne());
  if (sixths === 1 || sixths === 5) return recognized(tHalf());
  if (sixths === 7 || sixths === 11) return recognized(tNeg(tHalf()));
  return null;
}

/** The recorded multiple of π on the imaginary axis (q·π·i), or null: exp(iπ) is −1 from this. */
function imagPiOf(node: Node): Rational | null {
  const angle = factsOf(node).angle;
  return angle && angle.unit === "imag" ? angle.q : null;
}

/** i^n for an integer n. */
function unitPower(quarter: number): Node {
  const q = ((quarter % 4) + 4) % 4;
  if (q === 0) return recognized(ONE);
  if (q === 1) return recognized(tI());
  if (q === 2) return recognized(tMinusOne());
  return recognized(tNeg(tI()));
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
  // exp(i·kπ/2) is i^k.
  const turn = imagPiOf(t);
  if (turn && (BigInt(2) * turn.n) % turn.d === BigInt(0)) return unitPower(Number(((BigInt(2) * turn.n) / turn.d) % BigInt(4)));
  return expGates(t);
}

/** exp as its gate, with no value recognized. The tan pole is built from these gates. */
function expGates(t: Node): Node {
  const node = noteExp(E(t, ONE), t);
  // A crude series-shortcut error of magnitude >= 10^(-14) in the exponent
  // multiplies exp(t) by exp(±10^err), contaminating its 12 displayed digits.
  const argErr = maxSeriesErrorExp(t);
  if (argErr !== undefined && argErr >= -14) return markUnverified(node);
  noteBuiltFrom(node, { expArg: t });
  const lnArg = factsOf(t).builtFrom?.lnArg;
  if (lnArg && !isUnverified(t) && !isExactUnsure(t)) {
    const q = exactRationalOf(lnArg);
    if (q && q.n > BigInt(0)) learn(node, { rational: q });
  }
  // exp(+∞) is a pole, so exp(+∞) − exp(+∞) is the indeterminate subtraction.
  // exp(−∞) stays a zero: exp(−∞) − exp(−∞) is 0.
  // A finite real past about 709 overflows float to +∞. Mark it as overflow,
  // not a pole, so exp(800) − exp(800) folds to 0. exp of that overflow is a
  // pole, or exp(exp(800)) − itself would also fold to 0.
  if (t.type === "input" && t.value.re === Infinity && imagZero(t.value)) return noteNonfinite(node, 1);
  const known = knownValue(t);
  if (known && known.re === Infinity && imagZero(known)) return noteNonfinite(node, 1);
  if (known && known.re < 0 && !Number.isFinite(known.re)) return node;
  if (known && Number.isFinite(known.re) && known.re > 709 && Math.abs(known.im) < 1e-6) return noteOverflow(node);
  if (isNonfiniteNode(t) && !(known && known.re < 0)) return noteNonfinite(node, 1);
  return node;
}

export function tLn(t: Node): Node {
  const plus = factsOf(t).builtFrom?.onePlus;
  const minus = factsOf(t).builtFrom?.oneMinus;
  // ln(1+x) = x − x²/2 + … . Keep the leading term once the next term is past 478 digits (decade ≤ −479).
  const plusScale = plus ? tinyScale(plus, SERIES_REL) : null;
  if (plus && plusScale !== null) {
    return markSeriesError(markSeries(noteDecade(rawMul(ONE, plus), plusScale), "series shortcut: the leading term, for |x| < 10^(−478)"), 2 * plusScale + 2);
  }
  const minusScale = minus ? tinyScale(minus, SERIES_REL) : null;
  if (minus && minusScale !== null) {
    return markSeriesError(markSeries(rawMul(tNeg(ONE), minus), "series shortcut: the leading term, for |x| < 10^(−478)"), 2 * minusScale + 2);
  }
  const node = noteLn(E(ONE, E(E(ONE, t), ONE)), t);
  const argErr = maxSeriesErrorExp(t);
  if (argErr !== undefined) {
    const expT = magnitudeExp(t);
    if (expT === null || expT <= argErr + 12) return markUnverified(node);
  }
  noteBuiltFrom(node, { lnArg: t });
  if (!isUnverified(t) && !isExactUnsure(t)) {
    const expArg = factsOf(t).builtFrom?.expArg;
    const eq = expArg ? exactRationalOf(expArg) : null;
    if (eq) learn(node, { rational: eq });
  }
  if (provenInteger(t) === BigInt(0)) markInfiniteSource(node);
  // ln of an imaginary infinity is not the real infinity the log word prints.
  if (oddDirection(t)) return markUnverified(markMaybeInfinite(node, t));
  const inner = plus ?? minus;
  if (inner) {
    const decade = decadeOf(inner);
    // ln(1±x) shares x's decade when that decade still fits. Past the cap, or an
    // underflow with no decade, the circuit prints 0 and that 0 is not certified.
    if (decade !== undefined && decade <= -8 && -decade + 48 <= 480) noteDecade(node, decade);
    else if (decade === undefined && (isLostTiny(inner) || hiddenUnderflow(inner))) noteLostTiny(node);
  }
  return markMaybeInfinite(node, t);
}

export const tE = memo(() => tagReal(programNode("e"), Math.E));

export const tZero = memo(() => tagReal(programNode("0"), 0));

/**
 * Odd functions and cos(x)−1 drop a relative x². That term is past 480 digits
 * only once |x| ≤ 10^(−241). exp(x)−1, ln(1+x), and sqrt(1+x)−1 drop a relative
 * x; at decade ≤ −479 (|x| < 10^(−478)) the dropped x²/2 term is marked via
 * markSeriesError so any cancellation exposing it stays refused. A larger argument
 * keeps the real circuit.
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
const SERIES_REL = -479;
const LEAD_NOTE = "series shortcut: the leading term, for |x| ≤ 10^(−241)";
const POLY_NOTE = "series shortcut: odd powers kept until the remainder is past the 480-digit cap";
const SMALL_NOTE = "series shortcut: the leading term z, for a small |z|";
function markSeries(node: Node, note: string): Node {
  return markSeriesShortcut(node, note);
}

/** The note for a result whose circuit used a series shortcut. Null when it did not. */
export function seriesShortcutNote(root: Node): string | null {
  return seriesShortcutNoteFrom(root);
}

/** "recognized exactly" when the circuit used an exact recognition shortcut (see docs/shortcuts.md). */
export function recognizedNote(root: Node): string | null {
  return recognizedNoteFrom(root);
}

/** Decade of a real known to sit in one power of ten, or null when it might not. */
function tinyScale(node: Node, limit: number): number | null {
  const decade = decadeOf(node);
  if (decade !== undefined && decade <= limit) return decade;
  const dec = exactDecimalOf(node);
  if (dec && dec.n !== BigInt(0)) {
    const absN = dec.n < BigInt(0) ? -dec.n : dec.n;
    const decExp = absN.toString().length - 1 - dec.s;
    if (decExp <= limit) return decExp;
  }
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
  if (provenInteger(node) === BigInt(1)) return true;
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
  const cosA = factsOf(a).builtFrom?.cosArg;
  const cosB = factsOf(b).builtFrom?.cosArg;
  if (cosA && isOneNode(b)) {
    arg = cosA;
    sign = 1;
  } else if (cosB && isOneNode(a)) {
    arg = cosB;
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
  const expA = factsOf(a).builtFrom?.expArg;
  if (expA && isOneNode(b)) {
    const scale = tinyScale(expA, SERIES_REL);
    if (scale !== null) {
      return markSeriesError(markSeries(noteDecade(rawMul(ONE, expA), scale), "series shortcut: the leading term, for |x| < 10^(−478)"), 2 * scale + 2);
    }
  }
  const expB = factsOf(b).builtFrom?.expArg;
  if (expB && isOneNode(a)) {
    const scale = tinyScale(expB, SERIES_REL);
    if (scale !== null) {
      return markSeriesError(markSeries(rawMul(tNeg(ONE), expB), "series shortcut: the leading term, for |x| < 10^(−478)"), 2 * scale + 2);
    }
  }
  return null;
}

function sqrtMinusOne(a: Node, b: Node): Node | null {
  const inner = factsOf(a).builtFrom?.sqrtArg;
  if (!inner || !isOneNode(b)) return null;
  const scale = tinyScale(inner, SERIES_REL);
  if (scale === null) return null;
  const half = tHalfOf(inner);
  return markSeriesError(markSeries(noteDecade(half, scale - 1), "series shortcut: x/2, for |x| < 10^(−478)"), 2 * scale + 2);
}

/**
 * Constant substitution. A closed constant with a shortest known word
 * (best-known.json) uses it when the word is shorter than the ordinary circuit
 * and does not add a dependence on ln 0 = −∞: 1/2 is the K 35 circuit without
 * ln 0, so it may take the K 31 strict word but not the K 29 word that logs 0.
 */
const ln0Memo = new WeakMap<Node, boolean>();

function touchesLn0(node: Node): boolean {
  const known = ln0Memo.get(node);
  if (known !== undefined) return known;
  let touched = true;
  try {
    touched = evaluateReport(node).touchedLn0;
  } catch {
    touched = true;
  }
  ln0Memo.set(node, touched);
  return touched;
}

function preferShorter(generic: Node, candidate: Node | null): Node {
  if (!candidate || candidate === generic) return generic;
  if (circuitStats(candidate).rpnLength >= circuitStats(generic).rpnLength) return generic;
  if (touchesLn0(candidate) && !touchesLn0(generic)) return generic;
  return candidate;
}

/** The shortest of these words that preferShorter accepts over `generic`, or null. */
function shortestWord(generic: Node, ids: readonly string[]): Node | null {
  const length = (id: string) => SHORT_PROGRAMS[id]?.length ?? Number.POSITIVE_INFINITY;
  const sorted = ids.filter((id) => Object.hasOwn(SHORT_PROGRAMS, id)).sort((x, y) => length(x) - length(y));
  for (const id of sorted) {
    const word = programNode(id);
    if (preferShorter(generic, word) === word) return word;
  }
  return null;
}

/** A closed operand: no input leaf, no variable, no series shortcut. Only those fold. */
function closedConstant(node: Node): boolean {
  return node.type !== "input" && node.type !== "var" && maxSeriesErrorExp(node) === undefined && provenFinite(node);
}

/**
 * Small exact integers combined by + − × are that integer: 5 − 7 was the K 147
 * subtraction circuit and −2 is a K 25 word. A zero is left to the ordinary
 * builders, which keep its sign, and so is any integer the library is building.
 */
function foldSmallInts(op: "add" | "sub" | "mul", a: Node, b: Node, generic: Node): Node {
  if (buildingInteger() || !closedConstant(a) || !closedConstant(b)) return generic;
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia === undefined || ib === undefined) return generic;
  // A product of two nonzero integers with either past ±64 is past ±64: do not multiply huge ones to see that.
  const big = (v: bigint) => v > BigInt(64) || v < BigInt(-64);
  if (op === "mul" && ia !== BigInt(0) && ib !== BigInt(0) && (big(ia) || big(ib))) return generic;
  const value = op === "add" ? ia + ib : op === "sub" ? ia - ib : ia * ib;
  if (value === BigInt(0) || value < BigInt(-64) || value > BigInt(64)) return generic;
  return preferShorter(generic, integerNode(Number(value)));
}

/** Quotients of small integers with a stored word, and the stricter word that avoids ln 0. */
const QUOTIENT_WORDS: Readonly<Record<string, readonly string[]>> = {
  "1/2": ["1/2", "1/2-strict", "1/2-alt"],
  "-1/2": ["-1/2", "-1/2-strict"],
  "1/3": ["1/3", "1/3-strict"],
  "-1/3": ["-1/3"],
  "2/3": ["2/3"],
  "3/2": ["3/2", "3/2-strict"],
  "-3/2": ["-3/2", "-3/2-strict"],
  "5/2": ["5/2"],
  "-5/2": ["-5/2"],
  "-2/3": ["-2/3", "-2/3-strict"],
  "-5/3": ["-5/3"],
};

function gcd(x: bigint, y: bigint): bigint {
  let p = x < BigInt(0) ? -x : x;
  let q = y < BigInt(0) ? -y : y;
  while (q !== BigInt(0)) [p, q] = [q, p % q];
  return p;
}

function quotientWord(a: Node, b: Node, generic: Node): Node {
  if (!closedConstant(a) || !closedConstant(b)) return generic;
  if (provenInteger(a) === BigInt(1) && b === tE()) {
    const word = shortestWord(generic, ["1/e", "1/e-strict"]);
    return word ? tagReal(word, 1 / Math.E) : generic;
  }
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia === undefined || ib === undefined || ib === BigInt(0)) return generic;
  const g = gcd(ia, ib);
  let n = ia / g;
  let d = ib / g;
  if (d < BigInt(0)) {
    n = -n;
    d = -d;
  }
  const ids = QUOTIENT_WORDS[`${n}/${d}`];
  if (!ids) return generic;
  const word = shortestWord(generic, ids);
  // The word takes the facts the ordinary quotient derives from a and b.
  return word ? derive("div", tagReal(word, Number(n) / Number(d)), a, b) : generic;
}

/** ±iπ and ±2πi words, by the recorded multiple of πi. */
const ANGLE_WORDS: Readonly<Record<string, readonly string[]>> = {
  "1": ["ipi", "ipi-strict"],
  "-1": ["-ipi", "-ipi-strict"],
  "2": ["2ipi"],
  "-2": ["-2ipi"],
};

/**
 * A value the compiler has recorded exactly, as a multiple of πi (angle fact) or as a
 * rational (rational or decimal fact), takes its stored word under the preferShorter
 * policy, however it was spelled: 2*pi*i was K 199, pi*i K 165, 1/3−1 K 47.
 * The word carries the same exact fact, so later rules still see the value.
 * The parser applies it to each subexpression the user wrote (parse.ts foldAst), never
 * inside a library builder: tan(π/2) builds exp(2i·π/2), and swapping that iπ for its
 * word turned "near a pole" into an indeterminate form.
 */
export function constantWord(generic: Node): Node {
  if (isUnverified(generic) || isExactUnsure(generic) || maxSeriesErrorExp(generic) !== undefined) return generic;
  // A recognized result (cos((2/3)·π) is −1/2) keeps its own node: the word is shared,
  // and the "recognized exactly" note belongs to this circuit.
  if (isRecognized(generic)) return generic;
  const angle = factsOf(generic).angle;
  if (angle && angle.unit === "imag" && angle.q.d === BigInt(1)) {
    const ids = ANGLE_WORDS[angle.q.n.toString()];
    const word = ids ? shortestWord(generic, ids) : null;
    if (!word) return generic;
    tagValue(word, { re: 0, im: Number(angle.q.n) * Math.PI });
    return learn(word, { angle });
  }
  const rational = exactRationalOf(generic);
  if (rational && rational.d !== BigInt(1)) {
    const ids = QUOTIENT_WORDS[`${rational.n}/${rational.d}`];
    const word = ids ? shortestWord(generic, ids) : null;
    if (!word) return generic;
    tagReal(word, Number(rational.n) / Number(rational.d));
    return learn(word, { rational });
  }
  return generic;
}

export function tSub(a: Node, b: Node): Node {
  return foldSmallInts("sub", a, b, tSubBuild(a, b));
}

function tSubBuild(a: Node, b: Node): Node {
  const series = cosMinusOne(a, b) ?? expMinusOne(a, b) ?? sqrtMinusOne(a, b);
  if (series) return derive("sub", markMaybeInfinite(series, a, b), a, b);
  const node = domainSub(a, b);
  if (isOneNode(a)) noteBuiltFrom(node, { oneMinus: b });
  return derive("sub", markMaybeInfinite(node, a, b), a, b);
}

export function tNeg(b: Node): Node {
  const dir = directionOf(b);
  if (dir) return rememberDirection(dir.magnitude, dir.quarter + 2);
  const generic = derive("neg", domainNeg(b), b);
  if (b === tE()) {
    const word = shortestWord(generic, ["-e", "-e-strict"]);
    return word ? tagReal(word, -Math.E) : generic;
  }
  // −ln 2 is a K 27 word; negating the ln 2 word is K 39.
  if (b === programNode("ln2")) {
    const word = shortestWord(generic, ["-ln2"]);
    return word ? tagReal(word, -Math.LN2) : generic;
  }
  // −2 and −3 are words (K 25, K 35); negating 2 or 3 is K 33 and K 43.
  if (!buildingInteger() && closedConstant(b)) {
    const int = provenInteger(b);
    if (int !== undefined && int !== BigInt(0) && int >= BigInt(-64) && int <= BigInt(64)) return preferShorter(generic, integerNode(-Number(int)));
  }
  return generic;
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
  return foldSmallInts("add", a, b, tAddBuild(a, b));
}

function tAddBuild(a: Node, b: Node): Node {
  const cancelled = sumOfNegation(a, b);
  if (cancelled) return cancelled;
  const large = largeRealSum(a, b);
  if (large) return derive("add", markMaybeInfinite(large, a, b), a, b);
  const node = domainAdd(a, b);
  if (isOneNode(a)) noteBuiltFrom(node, { onePlus: b });
  else if (isOneNode(b)) noteBuiltFrom(node, { onePlus: a });
  return derive("add", node, a, b);
}

/**
 * The user's a + b. The add word rotates through ln, so ±∞ beside a finite term
 * can print a pure imaginary infinity. When that number is not the real infinity
 * the sum must be, exact mode says it could not verify. A float NaN stays undefined.
 */
export function userAdd(a: Node, b: Node): Node {
  return userSum(a, b, false);
}

/** The user's a − b. Same refusal as userAdd. */
export function userSub(a: Node, b: Node): Node {
  return userSum(a, b, true);
}

/** The user's −b keeps b's exact decimal via derive("neg", ...). */
export function userNeg(b: Node): Node {
  return tNeg(b);
}

/**
 * Classify, then build. The add circuit is the same node as ln of a zero argument,
 * and building it overwrites that range. Reading ln(0) afterwards would miss −∞.
 */
function userSum(a: Node, b: Node, sub: boolean): Node {
  const errA = maxSeriesErrorExp(a);
  const errB = maxSeriesErrorExp(b);
  const inheritedErr = errA !== undefined && errB !== undefined ? Math.max(errA, errB) : (errA ?? errB);
  const node = userSumBuild(a, b, sub);
  // Preserve crude series-shortcut error bounds even if algebraic cancellation (e.g. a − (a + c) → −c)
  // dropped the shortcut node from the resulting DAG.
  if (inheritedErr !== undefined) markSeriesError(node, inheritedErr);
  if (!isUnverified(node) && !isExactUnsure(node)) {
    const exact = exactRationalOf(node);
    const f = factsOf(node);
    if (exact && exact.n === BigInt(0) && f.decimal !== null && f.rational !== null && provenInteger(node) === undefined) {
      markExactInt(node, BigInt(0));
    }
  }
  return node;
}

function userSumBuild(a: Node, b: Node, sub: boolean): Node {
  const same = a === b;
  const negation = !sub && isNegationPair(a, b);
  // Classify before any sum or negation is built. Adding 0 reuses the ln(0)
  // node and would clear its range, so the sign must be read first.
  // Identical addends such as ln(0)+ln(0) still need a class: skipping that
  // would leave the indeterminate label on a same-direction sum.
  const left = negation ? null : infinityClass(a);
  const right = negation ? null : infinityClass(b);
  // Exact 0 is an identity. Passing the other operand through keeps a
  // directed infinity such as ∞i + 0, which the refusal path would drop.
  // An operand refused as unverified can carry a float-known 0 (its overflowed terms read as 0).
  // It is not an identity: dropping it would certify the other operand as the whole sum.
  const refused = isUnverified(a) || isUnverified(b) || isExactUnsure(a) || isExactUnsure(b);
  if (!same && !negation && !refused) {
    if (exactZero(b)) return a;
    if (!sub && exactZero(a)) return b;
    if (sub && exactZero(a)) return tNeg(b);
  }
  const node = sub ? tSub(a, b) : tAdd(a, b);
  // Identical subtraction stays on the circuit so ∞ − ∞ is undefined, not 0.
  if (same && sub) return node;
  if (negation || !left || !right || (!left.inf && !right.inf)) {
    // 1+(2+∞) must not drop the inner refusal and certify a NaN as ∞−∞.
    if (isUnverified(a) || isUnverified(b)) return markUnverified(node);
    if (isExactUnsure(a) || isExactUnsure(b)) return markExactUnsure(node);
    return node;
  }
  return refuseInfiniteSum(node, left, right, sub);
}

export function tInv(b: Node): Node {
  return rawDiv(ONE, b);
}

function exactZero(node: Node): boolean {
  if (isUnverified(node) || isExactUnsure(node)) return false;
  if (provenInteger(node) === BigInt(0)) return true;
  const known = knownValue(node);
  return !!known && known.im === 0 && known.re === 0 && !Object.is(known.re, -0);
}

/** A known −0 or 0. exactZero leaves −0 out, since −0 is not an identity of a sum. */
function signedZero(node: Node): boolean {
  if (isUnverified(node) || isExactUnsure(node)) return false;
  const known = knownValue(node);
  return !!known && known.re === 0 && known.im === 0;
}

function negativeFactor(node: Node): boolean {
  const v = knownValue(node);
  if (!v || !(v.im === 0 || Object.is(v.im, -0))) return false;
  // −0 is the negative leaf. A proven negative integer is too: 0·(−1) and 0·(−2)
  // are −0, because the product program would collapse that sign.
  // A negative non-integer is not. Tagging −2/3 or −ln 2 as an exact point must
  // not turn 0 times that point into −0; the product stays +0.
  if (Object.is(v.re, -0)) return true;
  const n = provenInteger(node);
  return n !== undefined && n < BigInt(0);
}

/** A known infinity, or a node marked non-finite. ln(0) is −∞ and is not marked. */
function nonFiniteFactor(node: Node): boolean {
  if (isNonfiniteNode(node)) return true;
  const v = knownValue(node);
  return v !== null && (!Number.isFinite(v.re) || !Number.isFinite(v.im));
}

/** Sign of a known real, or of a real interval that stays off zero. −0 counts as 0. */
function realDirection(node: Node): -1 | 0 | 1 | null {
  const v = node.type === "input" ? node.value : knownValue(node);
  if (v && imagZero(v) && !Number.isNaN(v.re)) {
    if (v.re === 0) return 0;
    return v.re < 0 ? -1 : 1;
  }
  const range = rangeOf(node);
  if (!range.re || !range.im || range.im.lo !== 0 || range.im.hi !== 0) return null;
  if (!Number.isFinite(range.re.lo) || !Number.isFinite(range.re.hi)) return null;
  if (range.re.hi < 0) return -1;
  if (range.re.lo > 0) return 1;
  if (range.re.lo === 0 && range.re.hi === 0) return 0;
  return null;
}

/** −∞ on the real axis, including ln(0). A typed +∞ is not this. */
function negativeRealInfinity(node: Node): boolean {
  return realSignedInfinity(node) === -1;
}

/** A known real ±∞, including a typed infinity and ln(0). */
function realSignedInfinity(node: Node): -1 | 1 | null {
  const v = node.type === "input" ? node.value : knownValue(node);
  if (!v || !imagZero(v)) return null;
  if (v.re === Infinity) return 1;
  if (v.re === -Infinity) return -1;
  return null;
}

/** Sign of a known finite pure imaginary, or of an interval that stays on one side of 0. */
function pureImagDirection(node: Node): -1 | 1 | null {
  const v = node.type === "input" ? node.value : knownValue(node);
  if (v && (v.re === 0 || Object.is(v.re, -0)) && Number.isFinite(v.im) && v.im !== 0) return v.im < 0 ? -1 : 1;
  const range = rangeOf(node);
  if (!range.re || !range.im || range.re.lo !== 0 || range.re.hi !== 0) return null;
  if (!Number.isFinite(range.im.lo) || !Number.isFinite(range.im.hi)) return null;
  if (range.im.hi < 0) return -1;
  if (range.im.lo > 0) return 1;
  return null;
}

function positiveRealInfinity(node: Node): Node {
  return realSignedInfinity(node) === -1 ? domainNeg(node) : node;
}

function axisTurn(quarter: number): Node {
  const q = ((quarter % 4) + 4) % 4;
  if (q === 0) return ONE;
  if (q === 1) return tNeg(tI());
  if (q === 2) return tMinusOne();
  return tI();
}

function rememberDirection(magnitude: Node, quarter: number): Node {
  const positive = positiveRealInfinity(magnitude);
  const node = E(E(positive, axisTurn(quarter)), ONE);
  return learn(node, { infinity: { maybe: true, kind: "directed", magnitude: positive, quarter } });
}

function directionOf(node: Node): { magnitude: Node; quarter: number } | null {
  const hit = recordedDirection(node);
  if (hit) return hit;
  const sign = realSignedInfinity(node);
  if (sign === 1) return { magnitude: node, quarter: 0 };
  if (sign === -1) return { magnitude: domainNeg(node), quarter: 2 };
  return null;
}

/** Quarter 1 is +∞i and quarter 3 is −∞i. */
function oddDirection(node: Node): boolean {
  const dir = directionOf(node);
  if (!dir) return false;
  const quarter = ((dir.quarter % 4) + 4) % 4;
  return quarter === 1 || quarter === 3;
}

/** A real ±∞, or a directed infinity. A float overflow such as exp(800) is not this. */
function infinityClass(node: Node): { inf: boolean; sign: -1 | 1 | undefined } {
  const real = realSignedInfinity(node);
  if (real !== null) return { inf: true, sign: real };
  const dir = directionOf(node);
  if (dir) {
    const quarter = ((dir.quarter % 4) + 4) % 4;
    if (quarter === 0) return { inf: true, sign: 1 };
    if (quarter === 2) return { inf: true, sign: -1 };
    return { inf: true, sign: undefined };
  }
  if (mayBeInfinite(node)) return { inf: true, sign: undefined };
  return { inf: false, sign: undefined };
}

function floatOf(node: Node): { re: number; im: number } | null {
  try {
    const report = evaluateReport(node, {}, { maxNodes: 50_000 });
    if (report.unverified) return null;
    return report.value;
  } catch {
    return null;
  }
}

/**
 * An infinite component beside a nonzero finite one, or two infinite components.
 * A float overflow such as exp(800) is ∞ + 0i and is not this: its exact value is finite.
 */
function offAxisInfinity(value: { re: number; im: number } | null): boolean {
  if (!value || Number.isNaN(value.re) || Number.isNaN(value.im)) return false;
  const reInf = !Number.isFinite(value.re);
  const imInf = !Number.isFinite(value.im);
  if (reInf && imInf) return true;
  if (reInf) return value.im !== 0;
  if (imInf) return value.re !== 0;
  return false;
}

function floatIsNaN(value: { re: number; im: number } | null): boolean {
  return value !== null && Number.isNaN(value.re) && Number.isNaN(value.im);
}

function floatIsRealInfinity(value: { re: number; im: number } | null, sign: -1 | 1): boolean {
  if (!value) return false;
  return value.re === sign * Infinity && (value.im === 0 || Object.is(value.im, -0));
}

function oppositeSign(sign: -1 | 1): -1 | 1 {
  return sign === 1 ? -1 : 1;
}

/**
 * ±∞ beside a finite term, when the add or sub word does not already show that
 * real infinity. A NaN float stays indeterminate only when both sides are
 * infinite and not proven to point the same way, so 1 + ∞ is refused and
 * ∞ − ∞ stays undefined. Two infinities that do point the same way keep the
 * circuit when it already shows that real infinity, so ∞ − (−∞) stays ∞.
 * The operands were classified before the sum was built.
 */
function refuseInfiniteSum(
  node: Node,
  left: { inf: boolean; sign: -1 | 1 | undefined },
  right: { inf: boolean; sign: -1 | 1 | undefined },
  sub: boolean,
): Node {
  const value = floatOf(node);
  const leftEff = left.sign;
  const rightEff = right.sign === undefined ? undefined : sub ? oppositeSign(right.sign) : right.sign;
  const bothInf = left.inf && right.inf;
  const knownPair = bothInf && leftEff !== undefined && rightEff !== undefined;
  if (knownPair && leftEff !== rightEff) return floatIsNaN(value) ? node : markUnverified(node);
  if (knownPair && leftEff === rightEff) {
    if (floatIsRealInfinity(value, leftEff)) return node;
    return markUnverified(node);
  }
  if (left.inf !== right.inf) {
    const known = left.inf ? left.sign : right.sign;
    const sign = known === undefined ? undefined : !left.inf && sub ? oppositeSign(known) : known;
    if (sign !== undefined) {
      if (floatIsRealInfinity(value, sign)) return node;
      return markUnverified(node);
    }
  }
  // Both infinite, but the directions are not proven. A NaN float is the
  // indeterminate cancellation; anything else is refused.
  if (bothInf && floatIsNaN(value)) return node;
  return markUnverified(node);
}

/** Quarter turns to add for a finite factor on one axis. */
function factorQuarter(node: Node): number | null {
  const real = realDirection(node);
  if (real === 1) return 0;
  if (real === -1) return 2;
  const imag = pureImagDirection(node);
  if (imag === 1) return 1;
  if (imag === -1) return 3;
  return null;
}

/**
 * A finite factor whose angle is not a quarter turn. 1+i is one.
 * An unknown range is not this: the product word still has to run.
 */
function offAxis(node: Node): boolean {
  if (factorQuarter(node) !== null) return false;
  const v = node.type === "input" ? node.value : knownValue(node);
  if (v && Number.isFinite(v.re) && Number.isFinite(v.im)) return v.re !== 0 && v.im !== 0;
  const range = rangeOf(node);
  if (!range.re || !range.im) return false;
  const ends = [range.re.lo, range.re.hi, range.im.lo, range.im.hi];
  if (!ends.every((end) => Number.isFinite(end))) return false;
  const reOff = range.re.hi < 0 || range.re.lo > 0;
  const imOff = range.im.hi < 0 || range.im.lo > 0;
  return reOff && imOff;
}

export function tMul(a: Node, b: Node): Node {
  return foldSmallInts("mul", a, b, tMulBuild(a, b));
}

function tMulBuild(a: Node, b: Node): Node {
  // 0 · ∞ is indeterminate. A known −∞ is not a finite negative factor, so it must not become −0.
  if ((exactZero(a) && nonFiniteFactor(b)) || (exactZero(b) && nonFiniteFactor(a))) {
    const pole = nonFiniteFactor(a) ? a : b;
    return markMaybeInfinite(naiveIndeterminate(pole), a, b);
  }
  // 0 · (−1) is the −0 leaf. The product program collapses that sign.
  if (exactZero(a) && negativeFactor(b)) return negativeZero();
  if (exactZero(b) && negativeFactor(a)) return negativeZero();
  // 0 times a finite value is exactly 0. The other factor's cap mark stops here,
  // so 0·10^(−500) stays a certified 0.
  if (exactZero(a) && provenFinite(b)) return tZero();
  if (exactZero(b) && provenFinite(a)) return tZero();
  // Carry the angle. Two infinities add their quarter turns. A factor off an
  // axis has no quarter turn, and the product word would still certify a real ∞.
  const dirA = directionOf(a);
  const dirB = directionOf(b);
  if (dirA && dirB) return rememberDirection(dirA.magnitude, dirA.quarter + dirB.quarter);
  if (dirA && offAxis(b)) return markUnverified(markInfiniteSource(rawMul(a, b)));
  if (dirB && offAxis(a)) return markUnverified(markInfiniteSource(rawMul(a, b)));
  const quarterA = dirA ? null : factorQuarter(a);
  const quarterB = dirB ? null : factorQuarter(b);
  if (dirA && quarterB !== null) return rememberDirection(dirA.magnitude, dirA.quarter + quarterB);
  if (dirB && quarterA !== null) return rememberDirection(dirB.magnitude, dirB.quarter + quarterA);
  // An infinity off the axes, such as ln(ln(0)) = ∞ + iπ, turned by i is −π + ∞i.
  // The product word prints a real ∞, and a result read off it was certified:
  // 1 + exp(−(ln(ln(0))·i)) was 1, though that exp has no limit.
  const turned = (inf: Node, quarter: number | null) =>
    (quarter === 1 || quarter === 3) && !directionOf(inf) && (nonFiniteFactor(inf) || mayBeInfinite(inf)) && offAxisInfinity(floatOf(inf));
  if (turned(a, quarterB) || turned(b, quarterA)) {
    return markUnverified(markInfiniteSource(rawMul(a, b)));
  }
  const product = propagateMulSeriesError(derive("mul", carryTinyScale(rawMul(a, b), a, b, "mul"), a, b), a, b);
  // The product word keeps only the cosine of the right-hand factor when the
  // left one is −∞, so ln(0)*2 comes out +∞. Negating makes the sign the
  // product of the two signs. An infinity on the right already has that sign.
  const direction = realDirection(b);
  if (negativeRealInfinity(a) && direction !== null && direction !== 0) return tNeg(product);
  return product;
}

function naiveIndeterminate(pole: Node): Node {
  return naiveSub(pole, pole);
}

function magnitudeExp(node: Node): number | null {
  const dec = decadeOf(node);
  if (dec !== undefined) return dec + 1;
  const v = knownValue(node) ?? floatOf(node);
  if (!v) return null;
  const m = Math.hypot(v.re, v.im);
  if (!Number.isFinite(m) || m === 0) return null;
  return Math.ceil(Math.log10(m));
}

function propagateMulSeriesError(out: Node, a: Node, b: Node): Node {
  const errA = maxSeriesErrorExp(a);
  const errB = maxSeriesErrorExp(b);
  if (errA !== undefined) {
    const expB = magnitudeExp(b);
    if (expB === null) {
      if (!exactZero(b)) markUnverified(out);
    } else if (expB > 0) {
      markSeriesError(out, errA + expB);
    }
  }
  if (errB !== undefined) {
    const expA = magnitudeExp(a);
    if (expA === null) {
      if (!exactZero(a)) markUnverified(out);
    } else if (expA > 0) {
      markSeriesError(out, errB + expA);
    }
  }
  return out;
}

function propagateDivSeriesError(out: Node, a: Node, b: Node): Node {
  const errA = maxSeriesErrorExp(a);
  if (errA !== undefined) {
    const expB = magnitudeExp(b);
    if (expB === null) markUnverified(out);
    else if (expB < 0) markSeriesError(out, errA - expB);
  }
  return out;
}

function expArgument(node: Node): Node | null {
  if (node.type === "eml" && node.b.type === "one") return node.a;
  return null;
}

function moderateExponent(node: Node): boolean {
  const re = rangeOf(node).re;
  if (provenInteger(node) !== undefined) return true;
  if (!re) return false;
  return Math.abs(re.lo) < 40 && Math.abs(re.hi) < 40;
}

export function tDiv(a: Node, b: Node): Node {
  return quotientWord(a, b, tDivBuild(a, b));
}

function tDivBuild(a: Node, b: Node): Node {
  // A finite numerator over a directed infinity is 0. The quotient word can
  // leave a signed zero in the opposite direction.
  if (directionOf(b) && !directionOf(a) && provenFinite(a)) return tZero();
  // (∞i)/2 is not the real infinity the quotient word prints.
  if (oddDirection(a) && !directionOf(b) && provenFinite(b)) return markUnverified(rawDiv(a, b));
  // exp(u)/exp(v) = exp(u − v) when the exponents are integers or small,
  // so exp(800)/exp(799) is e and not ∞/∞. A large complex exponent keeps
  // the quotient: rewriting it overflows.
  const u = expArgument(a);
  const v = expArgument(b);
  if (u && v && moderateExponent(u) && moderateExponent(v)) return tExp(tSub(u, v));
  const quotient = integerQuotient(a, b);
  if (quotient) return propagateDivSeriesError(quotient, a, b);
  return propagateDivSeriesError(derive("div", carryTinyScale(rawDiv(a, b), a, b, "div"), a, b), a, b);
}

/** A proven integer exponent, including negatives. A float that is not integral is not one. */
function integerExponent(node: Node): bigint | null {
  const tagged = provenInteger(node);
  if (tagged !== undefined) return tagged;
  const v = node.type === "input" ? node.value : knownValue(node);
  if (!v || v.im !== 0 || !Number.isInteger(v.re)) return null;
  return BigInt(v.re);
}

export function tPow(a: Node, b: Node): Node {
  // x^0 = 1 for every finite x, 0^0 included: the IEEE pow convention, and v1.1's.
  // The power word evaluates ln(0) for a zero base and printed 0^0 as undefined.
  // An infinite base (ln(0)^0) keeps the word and stays undefined.
  // −0 is that zero too: IEEE pow(0, −0) is 1, and 0^−0 printed undefined.
  if ((exactZero(b) || signedZero(b)) && provenFinite(a)) return recognized(ONE);
  // (−0)^b for a positive real b: −0 for odd positive integers, +0 otherwise (matching IEEE pow).
  // Without this, applyProgram("pow", −0, 2) evaluates exp(2·ln(−0)) = exp(−∞ + 2πi) and loses its angle.
  if (signedZero(a) && !isUnverified(b) && !isExactUnsure(b)) {
    const exp = integerExponent(b);
    if (exp !== null && exp > BigInt(0)) {
      return recognized(exp % BigInt(2) === BigInt(1) ? negativeZero() : tZero());
    }
    const rb = exactRationalOf(b);
    if (rb && rb.n > BigInt(0)) return recognized(tZero());
    const vb = knownValue(b);
    if (vb && vb.im === 0 && vb.re > 0 && Number.isFinite(vb.re)) {
      return recognized(tZero());
    }
  }
  // An integer power multiplies the quarter turn. ^2 was the only case, so
  // (∞i)^3 stayed the power word and came out a real infinity.
  // A negative integer power is 0, the same zero as 1 over that infinity.
  // Any other exponent is not a quarter turn and must not be certified.
  const dir = directionOf(a);
  if (dir) {
    const exp = integerExponent(b);
    if (exp !== null && exp > BigInt(0)) return rememberDirection(dir.magnitude, dir.quarter * Number(exp % BigInt(4)));
    if (exp !== null && exp < BigInt(0)) return tZero();
    return markUnverified(markInfiniteSource(applyProgram("pow", { x: a, y: b })));
  }
  // (±i)^n is 1, i, −1 or −i. The power word leaves a residue: i^2 + 1 said "couldn't verify".
  const unit = factsOf(a).imaginaryUnit;
  if (unit) {
    const exp = integerExponent(b);
    if (exp !== null) return unitPower(Number((exp * BigInt(unit)) % BigInt(4)));
  }
  if (closedConstant(a) && closedConstant(b)) {
    // e^2 is a K 21 word without ln 0; the power word on e is K 45.
    if (a === tE() && provenInteger(b) === BigInt(2)) {
      const word = shortestWord(applyProgram("pow", { x: a, y: b }), ["e^2"]);
      if (word) return tagReal(word, Math.E ** 2);
    }
    // A small integer power is that integer when the integer is shorter: 2^2 is the K 39 word for 4.
    const ia = provenInteger(a);
    const ib = provenInteger(b);
    if (!buildingInteger() && ia !== undefined && ib !== undefined && ib >= BigInt(0) && ib <= BigInt(64)) {
      const value = ia ** ib;
      if (value !== BigInt(0) && value >= BigInt(-64) && value <= BigInt(64)) {
        const int = integerNode(Number(value));
        if (preferShorter(applyProgram("pow", { x: a, y: b }), int) === int) return int;
      }
    }
  }
  const node = applyProgram("pow", { x: a, y: b });
  const errB = maxSeriesErrorExp(b);
  if (errB !== undefined && errB >= -14) return markUnverified(node);
  const errA = maxSeriesErrorExp(a);
  if (errA !== undefined) {
    const expA = magnitudeExp(a);
    const expB = magnitudeExp(b);
    if (expA === null || expB === null || errA + expB - expA >= -14) return markUnverified(node);
  }
  const ia = provenInteger(a);
  const ib = provenInteger(b);
  if (ia !== undefined && ib !== undefined && ib >= BigInt(0) && ib <= BigInt(10000)) {
    return tagInteger(node, ia ** ib);
  }
  derivePow(node, a, b);
  const va = knownValue(a);
  const vb = knownValue(b);
  if (va && vb && va.im === 0 && vb.im === 0 && va.re > 0 && Number.isFinite(vb.re)) {
    const re = va.re ** vb.re;
    // A float underflow is 0, and tagReal would store that as the integer 0.
    // The power is not that integer. The decade lets a later cancellation see it.
    // A float power is not the integer it may round to: 8^(3.3333333333333333e−1) is not 2.
    if (Number.isFinite(re) && re !== 0) tagValue(node, { re, im: 0 });
    else if (re === 0) {
      const log10 = Math.log10(va.re) * vb.re;
      const decade = Math.floor(log10 + 1e-10);
      // Past 480 digits a power spelling stays unresolved. Inside the cap, the
      // decade is what lets 1 ± 10^(−k) keep the small term.
      if (Number.isFinite(decade) && -decade + 48 <= 480) noteDecade(node, decade);
      // No decade past the cap: a series shortcut must not resolve tan(10^(−5000)).
      // The mark only refuses a later result that collapsed to a confident 0.
      else if (Number.isFinite(decade)) noteLostTiny(node);
    }
  }
  return node;
}

export function tSqr(t: Node): Node {
  const dir = directionOf(t);
  if (dir) return rememberDirection(dir.magnitude, dir.quarter * 2);
  const node = derive("mul", applyProgram("sqr", { x: t }), t, t);
  const v = knownValue(t);
  if (!v) return node;
  // A square that underflowed to 0 is not the integer 0.
  const tiny = (x: number, y: number) => x !== 0 && y !== 0 && x * y === 0;
  if (tiny(v.re, v.re) || tiny(v.im, v.im) || tiny(v.re, v.im)) return node;
  return tagValue(node, { re: v.re * v.re - v.im * v.im, im: 2 * v.re * v.im });
}

export const tMinusOne = memo(() => tagReal(programNode("-1"), -1));

export const tTwo = memo(() => tagReal(programNode("2"), 2));

export const tHalf = memo(() => noteExactDecimal(tagReal(programNode("1/2"), 0.5), { n: BigInt(5), s: 1 }));

export const tThree = memo(() => tagReal(programNode("3"), 3));

export const tTwoThirds = memo(() => tDiv(tTwo(), tThree()));

export function tSqrt(t: Node): Node {
  const v = t.type === "input" ? t.value : knownValue(t);
  // sqrt(−∞) is +∞i. The principal value has a non-negative real part, as sqrt(−1) = +i.
  // sqrt(+∞) stays +∞. The square-root word drops the angle, so the direction is recorded.
  if (v && imagZero(v) && v.re === Number.POSITIVE_INFINITY) return rememberDirection(t, 0);
  if (v && imagZero(v) && v.re === Number.NEGATIVE_INFINITY) return rememberDirection(t, 1);
  // sqrt(−0) is −0. The short word returns +0, and 1 over that is the wrong infinity.
  if (v && Object.is(v.re, -0) && imagZero(v)) return negativeZero();
  // sqrt of an imaginary infinity is off the axis. The square-root word prints a real infinity.
  if (oddDirection(t)) return markUnverified(applyProgram("sqrt", { x: t }));
  const node = applyProgram("sqrt", { x: t });
  // Exact rational square root: sqrt(p^2 / q^2) = p / q, and sqrt(-1) = +i.
  const rq = exactRationalOf(t);
  if (rq && rq.n >= BigInt(0)) {
    const rn = exactNthRoot(rq.n, 2);
    const rd = exactNthRoot(rq.d, 2);
    if (rn !== null && rd !== null) learn(node, { rational: { n: rn, d: rd } });
  } else if ((rq && rq.n === BigInt(-1) && rq.d === BigInt(1)) || provenInteger(t) === BigInt(-1)) {
    learn(node, { imaginaryUnit: 1 });
  }
  const inner = factsOf(t).builtFrom?.onePlus;
  if (inner && tinyScale(inner, SERIES_REL) !== null) noteBuiltFrom(node, { sqrtArg: inner });
  if (!v) return node;
  if (v.im === 0 && v.re >= 0) {
    // Only the root of a proven integer square is that integer: sqrt(4.0000000000000001e0) is not 2.
    const root = Math.sqrt(v.re);
    return provenInteger(t) !== undefined && root * root === v.re ? tagReal(node, root) : tagValue(node, { re: root, im: 0 });
  }
  const ax = Math.abs(v.re);
  const ay = Math.abs(v.im);
  const s = Math.sqrt((ax + Math.hypot(v.re, v.im)) / 2);
  const d = s === 0 ? 0 : ay / (2 * s);
  return tagValue(node, v.re >= 0 ? { re: s, im: Math.sign(v.im) * d } : { re: d, im: Math.sign(v.im || 1) * s });
}

export const tSqrt2 = memo(() => tagReal(programNode("sqrt2"), Math.SQRT2));

export const tI = memo(() => learn(tagValue(programNode("i"), { re: 0, im: 1 }), { imaginaryUnit: 1 }));

export const tPi = memo(() => {
  const node = tagReal(programNode("pi"), Math.PI);
  learn(node, { angle: { q: { n: BigInt(1), d: BigInt(1) }, unit: "real" } });
  return node;
});

export function tHalfOf(t: Node): Node {
  return rawMul(t, tHalf());
}

export function tSigmoid(t: Node): Node {
  return tInv(tAdd(ONE, tExp(tNeg(t))));
}

export function tSinh(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  // sinh(i·kπ) = 0 and sinh(i·(k + 1/2)π) = ±i.
  const ang = factsOf(t).angle;
  if (ang && ang.unit === "imag") {
    if (ang.q.d === BigInt(1)) return recognized(tZero());
    if (ang.q.d === BigInt(2)) {
      const m = Number(((ang.q.n % BigInt(4)) + BigInt(4)) % BigInt(4));
      return recognized(m === 1 ? tI() : tNeg(tI()));
    }
  }
  const known = tightValue(t);
  // sinh z = z + z³/6. Below about 10^(−6) the cubic is dust, and the exp formula is not.
  // The dropped cubic is not exact, so z is marked as a series shortcut with its cubic error
  // scale: any cancellation exposing the dropped z³/6 term is refused rather than certified.
  const mag = known ? Math.hypot(known.re, known.im) : Number.NaN;
  if (mag < 1e-6) {
    const out = markSeries(t, SMALL_NOTE);
    if (mag > 0) markSeriesError(out, Math.ceil(3 * Math.log10(mag)));
    return out;
  }
  // exp(t)/2 · (1 − exp(−2t)). Subtracting the real 1 keeps exp(t) out of the exponent.
  const em2 = tExp(tNeg(tAdd(t, t)));
  return tHalfOf(tMul(tExp(t), tSub(ONE, em2)));
}

export function tCosh(t: Node): Node {
  const em2 = tExp(tNeg(tAdd(t, t)));
  return tHalfOf(tMul(tExp(t), tSub(ONE, tNeg(em2))));
}

export function tTanh(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  // tanh(i·kπ) = 0, tanh(i·(k + 1/4)π) = ±i, and tanh(i·(k + 1/2)π) = pole.
  const ang = factsOf(t).angle;
  if (ang && ang.unit === "imag") {
    if (ang.q.d === BigInt(1)) return recognized(tZero());
    if (ang.q.d === BigInt(2)) return tTan(tMul(tNeg(tI()), t));
    if (ang.q.d === BigInt(4)) {
      const m = Number(((ang.q.n % BigInt(4)) + BigInt(4)) % BigInt(4));
      return recognized(m === 1 ? tI() : tNeg(tI()));
    }
  }
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, TANH_ODD, SERIES_WIDE);
  if (series) return series;
  // (e^{2t} − 1) / (e^{2t} + 1). The +1 is a subtraction of −1, so the huge term is not exponentiated again.
  const e2 = tExp(tAdd(t, t));
  const out = tDiv(tSub(e2, ONE), tSub(e2, tMinusOne()));
  // Past |Re t| ≈ 100 the distance from ±1, 2e^(−2|t|), is below the working precision
  // and the quotient rounds to an exact ±1. Not certified.
  // A literal 10^20 has no tagged float, and exp(800) overflows one, so the float
  // value decides. Without it, e^(2t) overflowed and tanh(10^20) printed undefined (∞/∞).
  const known = knownValue(t) ?? floatOrNull(t);
  return known && !Number.isNaN(known.re) && Math.abs(known.re) > 100 ? markExactUnsure(out) : out;
}

/** The float value of a subtree, or null when it cannot be evaluated. */
function floatOrNull(t: Node): { re: number; im: number } | null {
  try {
    return evaluateReport(t).value;
  } catch {
    return null;
  }
}

/**
 * Remember the argument. The pole and large-angle flags are decided from its
 * value at evaluation, so tan(3π/2) is a pole even when the product has no range.
 */
function flagAngle(node: Node, arg: Node, tan: boolean): Node {
  notePrecision(node, { kind: tan ? "pole" : "trig", arg });
  let known = knownValue(arg);
  if (!known) {
    try {
      known = evaluateReport(arg).value;
    } catch {
      known = null;
    }
  }
  if (known && Number.isFinite(known.re) && Math.abs(known.im) <= 1 && Math.abs(known.re) > HUGE_ANGLE) hugeAngleBuilt = true;
  return node;
}

/** Past this a 120-digit π no longer reduces the angle reliably. */
const HUGE_ANGLE = 1e15;
let hugeAngleBuilt = false;

/**
 * Whether the expression being compiled took sin, cos, or tan of an angle past
 * 10^15. A later sum can rebuild the trig node away, so its note is not enough.
 */
export function builtHugeAngle(): boolean {
  return hugeAngleBuilt;
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

/**
 * An odd function at an exact zero is that zero, and at −0 it is −0, as in IEEE.
 * Their circuits cancel to a 0 that exact mode cannot certify, or that a series
 * shortcut produced: tan(0), sinh(0), tanh(−0), arctan(0) and artanh(0) said
 * "couldn't verify", and arcsin(−0) was undefined in float.
 */
function oddAtZero(t: Node): Node | null {
  if (provenInteger(t) === BigInt(0)) return recognized(tZero());
  if (t.type === "input" && Object.is(t.value.re, -0) && t.value.im === 0) return recognized(t);
  return null;
}

export function tSin(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  const special = sinAtPiMultiple(piTwelfths(t));
  if (special) return special;
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, SIN_ODD, SERIES_POLY);
  if (series) return series;
  const it = tMul(tI(), t);
  const num = tSub(tExp(it), tExp(tNeg(it)));
  return flagAngle(tDiv(num, tMul(tTwo(), tI())), t, false);
}

export function tCos(t: Node): Node {
  // cos x = sin(x + π/2).
  const twelfths = piTwelfths(t);
  const special = sinAtPiMultiple(twelfths === null ? null : (twelfths + 6) % 24);
  if (special) return special;
  const it = tMul(tI(), t);
  const node = flagAngle(tHalfOf(tAdd(tExp(it), tExp(tNeg(it)))), t, false);
  noteBuiltFrom(node, { cosArg: t });
  return node;
}

export function tTan(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  // tan(kπ) is 0 and tan(π/4 + kπ/2) is ±1. The pole at π/2 + kπ is handled below.
  const twelfths = piTwelfths(t);
  if (twelfths !== null && twelfths % 12 === 0) return recognized(tZero());
  if (twelfths !== null && twelfths % 12 === 3) return recognized(ONE);
  if (twelfths !== null && twelfths % 12 === 9) return recognized(tMinusOne());
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, TAN_ODD, SERIES_WIDE);
  if (series) return series;
  // tan(z) = −i tanh(i z), and tanh(w) = 1 − 2/(exp(2w)+1).
  // A large positive exponent overflows to +∞ and the quotient vanishes,
  // so the same circuit covers both signs of Im(z). sin/cos does not.
  const w = tMul(tI(), t);
  // At the pole exp(2w) is exp(iπ). Recognized as −1 it would make this 2/0 − a real
  // infinity; the gates keep the large finite value the pole is built from below.
  const grown = isSymbolicTanPole(t) ? expGates(tMul(tTwo(), w)) : tExp(tMul(tTwo(), w));
  const tanh = tSub(ONE, tDiv(tTwo(), tAdd(grown, ONE)));
  const built = flagAngle(tMul(tNeg(tI()), tanh), t, true);
  if (!isSymbolicTanPole(t)) return built;
  // Those gates are a large finite, so tan(π/2) − tan(π/2) would be 0.
  // Dividing by 0 makes this pole a real infinity. The difference is then ∞ − ∞.
  return markInfiniteSource(flagAngle(rawDiv(built, tZero()), t, true));
}

/** The sign of Im(t) when the range proves it. 0 is a proven real. null is unknown. */
function provenImagSign(t: Node): 1 | -1 | 0 | null {
  if (provenInteger(t) !== undefined) return 0;
  const range = rangeOf(t);
  if (!range.im) return null;
  if (range.im.lo === 0 && range.im.hi === 0) return 0;
  if (range.im.lo > 0) return 1;
  if (range.im.hi < 0) return -1;
  return null;
}

function realBounds(t: Node): { lo: number; hi: number } | null {
  const int = provenInteger(t);
  if (int !== undefined) {
    const n = Number(int);
    return Number.isFinite(n) ? { lo: n, hi: n } : null;
  }
  return rangeOf(t).re;
}

/** The raw sub program keeps a tiny imaginary part. It needs a moderate real subtrahend. */
function rawSubtrahendOk(t: Node): boolean {
  const int = provenInteger(t);
  if (int !== undefined) return int > BigInt(-700) && int < BigInt(700);
  const range = rangeOf(t);
  if (!range.re || !range.im) return false;
  const edge = Math.PI - 1e-3;
  return range.re.lo > -700 && range.re.hi < 700 && range.im.lo > -edge && range.im.hi < edge;
}

function minMagnitude(t: Node): number {
  const re = realBounds(t);
  const im = provenInteger(t) !== undefined ? { lo: 0, hi: 0 } : rangeOf(t).im;
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

/**
 * Factored Horner series for arcsin(z) = z * (1 + z²*(1/6)*(1 + z²*(9/20)*(...))).
 * Picks enough terms for the omitted tail to lie past 124 digits at |z| <= box,
 * keeping float64 accuracy for |z| < 1e-4 without losing exact-mode digits.
 */
function arcsinSeries(t: Node, box: number): Node {
  const z2 = tSqr(t);
  const logBox = box > 0 ? -Math.log10(box) : 60;
  const terms = Math.max(2, Math.min(16, Math.ceil(62 / Math.max(4, logBox))));
  let acc: Node = ONE;
  for (let k = terms; k >= 1; k -= 1) {
    const num = (2 * k - 1) * (2 * k - 1);
    const den = 2 * k * (2 * k + 1);
    const factor = tDiv(integerNode(num), integerNode(den));
    acc = tAdd(ONE, tMul(z2, tMul(factor, acc)));
  }
  return tMul(t, acc);
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
  const zero = oddAtZero(t);
  if (zero) return zero;
  const known = knownValue(t);
  // Below about 10^(−60) the x³/6 term is not kept beside x: not certified.
  const tiny = known ? Math.hypot(known.re, known.im) : Number.NaN;
  if (tiny > 0 && tiny < 1e-60) {
    const out = markSeries(t, SMALL_NOTE);
    markSeriesError(out, Math.ceil(3 * Math.log10(tiny)));
    return out;
  }
  if (known && (known.im === 0 || Object.is(known.im, -0)) && (known.re === 1 || known.re === -1)) {
    const half = tHalfOf(tPi());
    return recognized(known.re < 0 ? tNeg(half) : half);
  }
  if (provenInteger(t) === BigInt(0)) return recognized(tZero());
  const box = asinhBox(t);
  // Below 10^(−4), the adaptive factored Horner series avoids float64 cancellation
  // while keeping the truncation tail past 124 digits. Below 10^(−60) the x³/6
  // term is not kept beside x: not certified.
  if (box !== null && box < 1e-4) {
    const series = arcsinSeries(t, box);
    // A float range of 0 collapses the product onto the shared integer 0.
    // Stamping that node unverified poisons π/2, which was built first.
    // π/2 − 0 folds back to that half, so in-process acos stays certified.
    // The wire rebuilds the half after the mark, and the refusal climbs.
    // The collapsed value is the same exact 0 a proven integer takes above.
    if (provenInteger(series) === BigInt(0)) return recognized(series);
    return box < 1e-60 ? markUnverified(series) : markSeries(series, SMALL_NOTE);
  }
  const re = realBounds(t);
  const side = provenImagSign(t);
  const lower = side === 1 || (side === 0 && !!re && re.hi < 0);
  // Asymptotic ±i(ln 2 + ln(∓iz)) drops O(1/z²); only switch once 1/z² is past 120 digits (|z| > 10^65).
  if (side !== null && minMagnitude(t) > 1e65) {
    const asym = lower
      ? tMul(tI(), tAdd(tLn(tTwo()), tLn(tMul(tNeg(tI()), t))))
      : tMul(tNeg(tI()), tAdd(tLn(tTwo()), tLn(tMul(tI(), t))));
    return markSeries(asym, "series shortcut: large-argument asymptotic");
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

/** −i·Log(z + i·√(1 − z)·√(1 + z)), for z next to 1, where it does not cancel. */
function arccosNearOne(t: Node): Node {
  const rad = tMul(sqrtOneMinus(t), sqrtOnePlus(t));
  return tMul(tNeg(tI()), tLn(tAdd(t, tMul(tI(), rad))));
}

export function tArccos(t: Node): Node {
  const exact = knownValue(t);
  if (exact && imagZero(exact) && exact.re === 1) return recognized(tZero());
  if (exact && imagZero(exact) && exact.re === -1) return recognized(tPi());
  // Near ±1 the range midpoint cannot tell 1 from 1 + 10^(−16): returning 0 printed
  // 0 for arccos(1 + 10^(−16)), which is 1.414×10^(−8) i. π/2 − arcsin cancels to a
  // zero exact mode cannot certify at 2/2, so near +1 the value is −i·Log(z + i·S),
  // which is Log 1 = 0 there. Near −1, arccos z = π − arccos(−z).
  const known = tightValue(t);
  if (known && imagZero(known) && known.re === 1) return arccosNearOne(t);
  if (known && imagZero(known) && known.re === -1) return tSub(tPi(), arccosNearOne(tNeg(t)));
  // acos = π/2 − asin, so a real x > 1 has positive imaginary part.
  return tSub(tHalfOf(tPi()), tArcsin(t));
}

export function tArctan(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  const small = tinyRealArgument(t);
  if (small) return small;
  const series = oddSeries(t, ARCTAN_ODD, SERIES_WIDE);
  if (series) return series;
  // arctan has its poles at ±i, where it is ±∞i: arctan(iy) = i·artanh(y) and y → 1.
  // −i·artanh(i·i) did not see i·i as −1, so the infinity lost its quarter turn and
  // came out a real ∞: exp(−arctan(i)) was 0, and 1 + exp(−arctan(i)) a certified 1.
  // As a directed infinity, exp of it is undefined, as exp(ln(0)·i) already is.
  const tf = factsOf(t);
  const imUnit =
    t === tI()
      ? 1
      : t === tNeg(tI())
        ? -1
        : tf.imaginaryUnit ??
          (tf.imagRational && tf.imagRational.d === BigInt(1) && (tf.imagRational.n === BigInt(1) || tf.imagRational.n === BigInt(-1))
            ? Number(tf.imagRational.n)
            : 0);
  if (imUnit === 1) return tMul(tI(), tNeg(tLn(tZero())));
  if (imUnit === -1) return tMul(tI(), tLn(tZero()));
  // A pure imaginary iy with |y| > 1 is i·artanh(y) on this cut.
  // artanh(−2) = −artanh(2), so arctan(−2i) = −π/2 − (artanh 2) i.
  const range = rangeOf(t);
  if (range.re && range.im && Math.abs(range.re.lo) < 1e-6 && Math.abs(range.re.hi) < 1e-6 && (range.im.lo > 1 || range.im.hi < -1)) {
    return tMul(tI(), tArtanh(tMul(tNeg(tI()), t)));
  }
  // arctan z = −i·artanh(iz), which holds on both cuts because tArtanhClosed is
  // mpmath's atanh. Bypass tArtanh's < 1e-6 linear shortcut here: tArctan already
  // handled tiny arguments via tinyRealArgument / oddSeries above, so 1e-20 < |z| < 1e-6
  // stays on the exact closed form instead of dropping z³/3.
  return tMul(tNeg(tI()), tArtanhClosed(tMul(tI(), t)));
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
  const zero = oddAtZero(t);
  if (zero) return zero;
  const known = knownValue(t);
  if (!isUnverified(t) && !isExactUnsure(t) && ((known && known.re === 0 && (known.im === 0 || Object.is(known.im, -0))) || provenInteger(t) === BigInt(0))) return recognized(tZero());
  const unit = factsOf(t).imaginaryUnit;
  if (unit) {
    const quarter = tMul(tI(), tHalfOf(tPi()));
    return recognized(unit === 1 ? quarter : tNeg(quarter));
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

function tArtanhClosed(t: Node): Node {
  const known = tightValue(t);
  // artanh(±1) is ±∞, kept as ln 0 so it has a direction. The quotient of square
  // roots divides by a 0 and gives an infinity with none, which i·artanh(1) turned
  // into a real ∞.
  const unit = provenInteger(t);
  if (unit === BigInt(1)) return tNeg(tLn(tZero()));
  if (unit === BigInt(-1)) return tLn(tZero());
  if (known && imagZero(known) && known.re > 1) return artanhAboveOne(t);
  if (known && imagZero(known) && known.re < -1) return tNeg(artanhAboveOne(tNeg(t)));
  // Log(√(1+z) / √(1−z)) with the principal √ and Log. It equals ½(ln(1+z) − ln(1−z))
  // (DLMF 4.37.24, mpmath's atanh) exactly: half a difference of two Args in (−π, π]
  // stays inside (−π, π), so no 2πi is lost. ½·Log((1+z)/(1−z)) put a real above 1 on
  // the other bank (+iπ/2) whenever the range table had no point for it, so
  // atanh(1.694^3) was +iπ/2 while atanh(4.861) was −iπ/2, both certified.
  return tLn(tDiv(tSqrt(tAdd(ONE, t)), tSqrt(tSub(ONE, t))));
}

export function tArtanh(t: Node): Node {
  const zero = oddAtZero(t);
  if (zero) return zero;
  const known = tightValue(t);
  // artanh z = z + z³/3: the dropped cubic is not exact, as in tSinh.
  const mag = known ? Math.hypot(known.re, known.im) : Number.NaN;
  if (mag < 1e-6) {
    const out = markSeries(t, SMALL_NOTE);
    if (mag > 0) markSeriesError(out, Math.ceil(3 * Math.log10(mag)));
    return out;
  }
  return tArtanhClosed(t);
}

/** Exact rational log_base(value) = p/q when base^p = value^q for small integers |p| <= 64, 1 <= q <= 8. */
function exactRationalLog(base: Rational, value: Rational): Rational | null {
  if (base.n <= BigInt(0) || value.n <= BigInt(0) || base.n === base.d) return null;
  if (value.n === value.d) return { n: BigInt(0), d: BigInt(1) };
  // Normalize base > 1 by inverting if base < 1 (flips sign of log).
  let bn = base.n;
  let bd = base.d;
  let flipBase = false;
  if (bn < bd) {
    [bn, bd] = [bd, bn];
    flipBase = true;
  }
  let vn = value.n;
  let vd = value.d;
  let flipVal = false;
  if (vn < vd) {
    [vn, vd] = [vd, vn];
    flipVal = true;
  }
  const sign = flipBase === flipVal ? BigInt(1) : BigInt(-1);
  // Check value^q === base^p for 1 <= q <= 8 and 1 <= p <= 64 (strictly increasing powers).
  let vnq = BigInt(1);
  let vdq = BigInt(1);
  for (let q = 1; q <= 8; q += 1) {
    vnq *= vn;
    vdq *= vd;
    if (vnq.toString().length > 200 || vdq.toString().length > 200) break;
    let bnp = BigInt(1);
    let bdp = BigInt(1);
    for (let p = 1; p <= 64; p += 1) {
      bnp *= bn;
      bdp *= bd;
      if (bnp === vnq && bdp === vdq) return { n: sign * BigInt(p), d: BigInt(q) };
      if (bnp > vnq && bdp >= vdq) break;
      if (bnp.toString().length > 200 || bdp.toString().length > 200) break;
    }
  }
  return null;
}

export function tLogBase(base: Node, value: Node): Node {
  const node = applyProgram("log", { x: base, y: value });
  if (!isUnverified(base) && !isUnverified(value) && !isExactUnsure(base) && !isExactUnsure(value)) {
    const rb = exactRationalOf(base);
    const rv = exactRationalOf(value);
    if (rb && rv) {
      const q = exactRationalLog(rb, rv);
      if (q) learn(node, { rational: q });
    }
  }
  return node;
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
  const ra = exactRationalOf(a);
  const rb = exactRationalOf(b);
  if (ra && rb) {
    if (ra.n === BigInt(0) && rb.n === BigInt(0)) return tZero();
    if (ra.n === BigInt(0)) return rb.n < BigInt(0) ? tNeg(b) : b;
    if (rb.n === BigInt(0)) return ra.n < BigInt(0) ? tNeg(a) : a;
  }
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
    // A stored word for this integer (−2, −3, 4), when it is shorter and adds no ln 0.
    const id = String(n);
    if (n < -1 || n > 3) {
      if (Object.hasOwn(SHORT_PROGRAMS, id)) node = preferShorter(node, programNode(id));
    }
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
  // The expression box reads .5e3 and 1.e5 as numbers, as it reads .5 and 5.
  const sci = /^([+-]?)(\d*)(?:\.(\d*))?[eE]([+-]?\d+)$/.exec(trimmed);
  if (sci && (sci[2] || sci[3])) {
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
    if (digits !== "0") noteDecade(signed, expAdj + digits.length - 1);
    if (Math.abs(expAdj) <= DECIMAL_SCALE_MAX) {
      const n = BigInt(sign) * BigInt(digits) * (expAdj > 0 ? BigInt(10) ** BigInt(expAdj) : BigInt(1));
      noteExactDecimal(signed, { n, s: expAdj < 0 ? -expAdj : 0 });
    }
    const numeric = Number(trimmed);
    if (!Number.isFinite(numeric) || numeric === 0) return signed;
    // The float is the decimal only when it is an integer the float holds exactly:
    // 1.0000000000000001e0 rounds to 1, and tagging it the integer 1 made 1.0000000000000001e0 − 1 a certified 0.
    const whole = digits.replace(/0+$/, "") || "0";
    const shift = expAdj + (digits.length - whole.length);
    const integral = shift >= 0 && Number.isSafeInteger(numeric) && BigInt(whole) * BigInt(10) ** BigInt(shift) === BigInt(Math.abs(numeric));
    return integral ? tagReal(signed, numeric) : tagValue(signed, { re: numeric, im: 0 });
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
      const signed = sign < 0 ? tNeg(magnitude) : magnitude;
      return noteExactDecimal(signed, { n: BigInt(sign) * BigInt(digits), s: frac.length });
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
  add: userAdd,
  sub: userSub,
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
