import { countWord, countWordLength } from "./countWord";
import { EXACT_MAX_NODES, EXACT_TOO_LARGE } from "./exactBudget";
import { tagValue } from "./lowering";
import { tAdd, tNeg, tSub } from "./library";
import { circuitStats, E, nodeFromRpn, ONE, rpnTokens, type Node } from "./node";
import { SHORT_PROGRAMS } from "./programs";
import rows from "./integer-table.json";

/**
 * Compile a typed expression into a press sequence on the keys 1 and EML.
 *
 * eml(x, y) = exp(x) − ln(y), written in RPN: 1 pushes the constant, E pops y
 * then x (x was pushed first) and pushes eml(x, y). The idea of typing an
 * ordinary sum and playing it back as those two keys is John Haas's
 * eml-calculator (https://github.com/j0hnhaas/eml-calculator, MIT;
 * https://j0hnhaas.github.io/eml-calculator/). This file does not copy his
 * source. The recipes are our words in best-known.json, checked against our
 * exact engine on the lower bank (Arg in [−π, π)).
 *
 * Short recipes, and where the exact engine says they are valid. Lengths are
 * the paper's direct-search lengths when both operands are single keys
 * (arXiv:2603.21852). "Extra" is the keys the recipe adds around the operands,
 * the same templates as the gadget words (sub +9, minus +14, mul +15, add +17,
 * pow +23).
 *
 * - add, 19 keys, extra 17. Both operands integers from −REAL_LIMIT to
 *   REAL_LIMIT, and the sum is not 0. Every such pair was checked on the
 *   words this compiler emits: the value matches and the engine certifies it.
 *   A sum of exactly 0 is not that word. A printed 0 is not certified for
 *   every spelling, on the short word or on tAdd (add(6, −6), add(8, −8),
 *   add(−8, 8), and composed spellings such as (2^3−1)+(0−7)). After both
 *   operands have compiled, any add whose rational value is 0 is the
 *   certified 0 word (7 presses). An operand that itself cannot be compiled
 *   still errors, because that check happens before the 0 word replaces the
 *   operands. Wrong once Im(x + y) leaves (−π, π]: add(5, 4i) wraps to
 *   5 − (2π − 4)i.
 * - sub, 11 keys, extra 9. Both operands integers in that same range, and
 *   the difference is not 0. Every such pair is certified on the short word.
 *   A difference of exactly 0 is the certified 0 word, for the same reason
 *   (sub(−4, −4) and (−4*1)−(−4) are unverified on the short spelling).
 *   Wrong once Im(y) leaves [−π, π]: sub(5, 4i) is 5 + (2π − 4)i, not 5 − 4i.
 * - mul, 17 keys, extra 15. Both operands integers in that range. Also an
 *   integer from −IMUL_LIMIT to IMUL_LIMIT times k·i for an integer k in that
 *   same range, either order, including 4·i and −4·i.
 * - div, 17 keys, extra 15. Both operands integers in the real range, divisor
 *   not 0. 1/3 and 8/7 match at 40 digits.
 * - pow, 25 keys, extra 23. Integer base in the real range and an integer
 *   exponent from POW_MIN through POW_MAX, including negative bases. 0^0 is
 *   indeterminate. A negative power of 0 is a pole.
 * - minus, 15 keys, extra 14. One integer operand in the real range. Wrong
 *   for a pure imaginary whose absolute value exceeds π: minus(4i) wraps.
 *
 * Outside those domains the compiler does not emit the short word. Addition
 * and subtraction of an in-range integer and k·i (k a nonzero integer with
 * |k| ≤ IMUL_LIMIT), and negation of such a k·i, use the library builders
 * (domainAdd, domainSub, rotSub, and negation by a verified −1). Every pair
 * in that rectangle was checked on the exact engine and is certified,
 * including 5 − 4i and −(4i). Multiplication,
 * division, and powers have no longer builder than the short word, so an
 * operand outside the checked domain is reported instead of emitted. Integer
 * literals are the mathbot table (integer-table.json, −2..25) when that word
 * is no longer than the counting construction, and countWord otherwise.
 */

type TableRow = { n: number; word: string; presses: number };

const TABLE = new Map<number, TableRow>();
for (const row of rows as TableRow[]) TABLE.set(row.n, row);

export const REAL_LIMIT = 8;
export const IMUL_LIMIT = 6;
export const POW_MIN = -3;
export const POW_MAX = 6;
export const LITERAL_LIMIT = 60;

export class PressCompileError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "PressCompileError";
  }
}

type Fr = { n: number; d: number };
type G = { re: Fr; im: Fr };

type Ast =
  | { k: "int"; n: number }
  | { k: "i" }
  | { k: "neg"; a: Ast }
  | { k: "bin"; op: "+" | "-" | "*" | "/" | "^"; a: Ast; b: Ast };

type Built = { node: Node; word: string; value: G; via: string[] };

export type PressSequence = {
  node: Node;
  word: string;
  presses: number;
  via: readonly string[];
};

const ZERO_FR: Fr = { n: 0, d: 1 };
const ONE_FR: Fr = { n: 1, d: 1 };
const GI: G = { re: ZERO_FR, im: ONE_FR };

function gcd(a: number, b: number): number {
  let x = Math.abs(a);
  let y = Math.abs(b);
  while (y !== 0) {
    const next = x % y;
    x = y;
    y = next;
  }
  return x || 1;
}

function fr(n: number, d = 1): Fr {
  if (!Number.isSafeInteger(n) || !Number.isSafeInteger(d)) {
    throw new PressCompileError("That value is outside the verified recipes.");
  }
  if (d < 0) {
    n = -n;
    d = -d;
  }
  if (d === 0) throw new PressCompileError("Division by zero has no press sequence.");
  const g = gcd(n, d);
  return { n: n / g, d: d / g };
}

function realG(n: number): G {
  return { re: fr(n), im: ZERO_FR };
}

function isZeroG(g: G): boolean {
  return g.re.n === 0 && g.im.n === 0;
}

function isRealG(g: G): boolean {
  return g.im.n === 0;
}

function mulInt(a: number, b: number): number {
  const product = a * b;
  if (!Number.isSafeInteger(product)) throw new PressCompileError("That value is outside the verified recipes.");
  return product;
}

function frAdd(a: Fr, b: Fr): Fr {
  return fr(mulInt(a.n, b.d) + mulInt(b.n, a.d), mulInt(a.d, b.d));
}

function frSub(a: Fr, b: Fr): Fr {
  return fr(mulInt(a.n, b.d) - mulInt(b.n, a.d), mulInt(a.d, b.d));
}

function frMul(a: Fr, b: Fr): Fr {
  return fr(mulInt(a.n, b.n), mulInt(a.d, b.d));
}

function frDiv(a: Fr, b: Fr): Fr {
  if (b.n === 0) throw new PressCompileError("Division by zero has no press sequence.");
  return fr(mulInt(a.n, b.d), mulInt(a.d, b.n));
}

function gAdd(a: G, b: G): G {
  return { re: frAdd(a.re, b.re), im: frAdd(a.im, b.im) };
}

function gSub(a: G, b: G): G {
  return { re: frSub(a.re, b.re), im: frSub(a.im, b.im) };
}

function gNeg(g: G): G {
  return { re: fr(-g.re.n, g.re.d), im: fr(-g.im.n, g.im.d) };
}

function gMul(a: G, b: G): G {
  return {
    re: frSub(frMul(a.re, b.re), frMul(a.im, b.im)),
    im: frAdd(frMul(a.re, b.im), frMul(a.im, b.re)),
  };
}

function gDiv(a: G, b: G): G {
  const den = frAdd(frMul(b.re, b.re), frMul(b.im, b.im));
  if (den.n === 0) throw new PressCompileError("Division by zero has no press sequence.");
  return {
    re: frDiv(frAdd(frMul(a.re, b.re), frMul(a.im, b.im)), den),
    im: frDiv(frSub(frMul(a.im, b.re), frMul(a.re, b.im)), den),
  };
}

function gPowInt(base: G, exp: number): G {
  if (exp < 0) {
    if (isZeroG(base)) throw new PressCompileError("A negative power of 0 has no press sequence.");
    return gPowInt(gDiv(realG(1), base), -exp);
  }
  let result = realG(1);
  let cursor = base;
  let left = exp;
  while (left > 0) {
    if (left % 2 === 1) result = gMul(result, cursor);
    left = Math.floor(left / 2);
    if (left > 0) cursor = gMul(cursor, cursor);
  }
  return result;
}

/** An integer whose absolute value sits inside the checked real box. */
export function realInBox(g: G): boolean {
  return isRealG(g) && g.re.d === 1 && Math.abs(g.re.n) <= REAL_LIMIT;
}

/** Integer k with g = k·i and |k| ≤ IMUL_LIMIT, or null. */
function imagScale(g: G): number | null {
  if (g.re.n !== 0 || g.im.d !== 1) return null;
  if (Math.abs(g.im.n) > IMUL_LIMIT) return null;
  return g.im.n;
}

function realScale(g: G): number | null {
  if (!isRealG(g) || g.re.d !== 1) return null;
  if (Math.abs(g.re.n) > IMUL_LIMIT) return null;
  return g.re.n;
}

function integerExponent(g: G): number | null {
  if (!isRealG(g) || g.re.d !== 1) return null;
  return g.re.n;
}

function recipe(id: string): string {
  const word = SHORT_PROGRAMS[id];
  if (!word) throw new PressCompileError(`The recipe ${id} is not in the program table.`);
  return word;
}

/** Keys the recipe adds around its x and y holes. The total, with single-key operands, is the paper length. */
export function recipeExtra(id: string): number {
  const word = recipe(id);
  let holes = 0;
  for (const ch of word) if (ch === "x" || ch === "y") holes += 1;
  return word.length - holes;
}

function buttonsOnly(word: string): boolean {
  if (word.length === 0) return false;
  for (const ch of word) if (ch !== "1" && ch !== "E") return false;
  return true;
}

function integerWord(n: number): { word: string; how: string } {
  if (!Number.isSafeInteger(n) || n > LITERAL_LIMIT || n < -LITERAL_LIMIT) {
    throw new PressCompileError(`The integer ${n} is outside −${LITERAL_LIMIT}…${LITERAL_LIMIT}.`);
  }
  const counted = countWord(n);
  if (!buttonsOnly(counted) || counted.length !== countWordLength(n)) {
    throw new PressCompileError("The counting word does not match its length.");
  }
  const row = TABLE.get(n);
  if (row && buttonsOnly(row.word) && row.word.length === row.presses && row.word.length <= counted.length) {
    return { word: row.word, how: `lit:${n}:table` };
  }
  return { word: counted, how: `lit:${n}:count` };
}

function spell(node: Node, value: G, via: string[]): Built {
  const length = circuitStats(node).rpnLength;
  if (length > BigInt(EXACT_MAX_NODES)) {
    throw new PressCompileError(EXACT_TOO_LARGE);
  }
  const tokens = rpnTokens(node, Number(length));
  if (!tokens || tokens.some((token) => token !== "1" && token !== "E")) {
    throw new PressCompileError("The general construction is not a program of the 1 and EML keys.");
  }
  const word = tokens.join("");
  if (BigInt(word.length) !== length) {
    throw new PressCompileError("The press count does not match the circuit.");
  }
  return { node, word, value, via };
}

function fromWord(word: string, value: G, via: string[]): Built {
  if (!buttonsOnly(word)) throw new PressCompileError("A recipe produced a symbol other than 1 or E.");
  return spell(nodeFromRpn(word.split("")), value, via);
}

function splice(template: string, holes: Record<string, string>): string {
  let out = "";
  for (const ch of template) out += holes[ch] ?? ch;
  return out;
}

function shortCall(id: string, holes: Record<string, string>, value: G, via: string[]): Built {
  return fromWord(splice(recipe(id), holes), value, via);
}

function pointOf(g: G): { re: number; im: number } | null {
  if (g.re.d !== 1 || g.im.d !== 1) return null;
  if (!Number.isSafeInteger(g.re.n) || !Number.isSafeInteger(g.im.n)) return null;
  return { re: g.re.n, im: g.im.n };
}

/**
 * The 7-press 0 word. Used for every add or sub whose rational value is 0,
 * after the operands have compiled. The short spelling of a printed 0 is not
 * certified for every way of writing those operands.
 */
function certifiedZero(parts: Built[], id: "add" | "sub"): Built {
  return fromWord(recipe("0"), realG(0), [...parts.flatMap((part) => part.via), `${id}:zero`]);
}

function fallbackLinear(op: "add" | "sub" | "minus", parts: Built[], value: G): Built {
  const tagged: Node[] = [];
  for (const part of parts) {
    const point = pointOf(part.value);
    if (!point) throw new PressCompileError("That value has no general 1-and-EML construction in this compiler.");
    tagged.push(tagValue(part.node, point));
  }
  const left = tagged[0];
  const right = tagged[1];
  if (!left) throw new PressCompileError("The general construction is missing an operand.");
  const node = op === "minus" ? tNeg(left) : op === "add" ? (right ? tAdd(left, right) : null) : right ? tSub(left, right) : null;
  if (!node) throw new PressCompileError("The general construction is missing an operand.");
  return spell(node, value, [...parts.flatMap((part) => part.via), `${op}:fallback`]);
}

function nonzeroImag(g: G): number | null {
  const k = imagScale(g);
  if (k === null || k === 0) return null;
  return k;
}

/** An in-range integer beside a nonzero k·i. That is the checked rotSub rectangle. */
function stripPair(a: G, b: G): boolean {
  const leftReal = realInBox(a) ? a.re.n : null;
  const rightReal = realInBox(b) ? b.re.n : null;
  return (leftReal !== null && nonzeroImag(b) !== null) || (rightReal !== null && nonzeroImag(a) !== null);
}

function outside(kind: string): never {
  throw new PressCompileError(
    `That ${kind} is outside the verified domain. Integers from −${REAL_LIMIT} to ${REAL_LIMIT} use the short recipe. An integer in that range combined with k·i, |k| from 1 to ${IMUL_LIMIT}, uses the general construction.`,
  );
}

function mulInDomain(a: G, b: G): boolean {
  if (realInBox(a) && realInBox(b)) return true;
  const leftReal = realScale(a);
  const rightReal = realScale(b);
  const leftImag = imagScale(a);
  const rightImag = imagScale(b);
  if (leftReal !== null && rightImag !== null) return true;
  if (rightReal !== null && leftImag !== null) return true;
  return false;
}

function powInDomain(base: G, exp: number): boolean {
  if (!realInBox(base)) return false;
  if (!Number.isInteger(exp) || exp < POW_MIN || exp > POW_MAX) return false;
  if (isZeroG(base) && exp <= 0) return false;
  return true;
}

function lower(ast: Ast): Built {
  const folded = signedInteger(ast);
  if (folded !== null) {
    const lit = integerWord(folded);
    return fromWord(lit.word, realG(folded), [lit.how]);
  }
  if (ast.k === "i") return fromWord(recipe("i"), GI, ["lit:i"]);
  if (ast.k === "neg") {
    const arg = lower(ast.a);
    const value = gNeg(arg.value);
    if (realInBox(arg.value)) return shortCall("minus", { x: arg.word }, value, [...arg.via, "minus:short"]);
    if (nonzeroImag(arg.value) !== null) return fallbackLinear("minus", [arg], value);
    return outside("negation");
  }
  if (ast.k !== "bin") throw new PressCompileError("That expression is not supported.");
  const left = lower(ast.a);
  const right = lower(ast.b);
  if (ast.op === "^") return lowerPow(left, right);
  if (ast.op === "/" && isZeroG(right.value)) throw new PressCompileError("Division by zero has no press sequence.");
  const value = ast.op === "+" ? gAdd(left.value, right.value) : ast.op === "-" ? gSub(left.value, right.value) : ast.op === "*" ? gMul(left.value, right.value) : gDiv(left.value, right.value);
  const id = ast.op === "+" ? "add" : ast.op === "-" ? "sub" : ast.op === "*" ? "mul" : "div";
  if ((id === "add" || id === "sub") && isZeroG(value)) return certifiedZero([left, right], id);
  const inDomain = id === "mul" ? mulInDomain(left.value, right.value) : realInBox(left.value) && realInBox(right.value);
  if (inDomain) return shortCall(id, { x: left.word, y: right.word }, value, [...left.via, ...right.via, `${id}:short`]);
  if ((id === "add" || id === "sub") && stripPair(left.value, right.value)) return fallbackLinear(id, [left, right], value);
  outside(id === "add" ? "sum" : id === "sub" ? "difference" : id === "mul" ? "product" : "quotient");
}

function lowerPow(base: Built, exp: Built): Built {
  const n = integerExponent(exp.value);
  if (n === null) {
    throw new PressCompileError("Powers are compiled for integer exponents only. 2^3 is supported.");
  }
  if (isZeroG(base.value) && n === 0) throw new PressCompileError("0^0 is indeterminate, so it has no press sequence.");
  if (isZeroG(base.value) && n < 0) throw new PressCompileError("A negative power of 0 has no press sequence.");
  if (n < POW_MIN || n > POW_MAX) {
    throw new PressCompileError(`That exponent is outside the verified power recipe (${POW_MIN} through ${POW_MAX}).`);
  }
  const value = gPowInt(base.value, n);
  if (!powInDomain(base.value, n)) {
    throw new PressCompileError("That power is outside the verified domain of the short recipe (a real base, and an integer exponent).");
  }
  return shortCall("pow", { x: base.word, y: exp.word }, value, [...base.via, ...exp.via, "pow:short"]);
}

/** A chain of unary minuses on an integer, folded so −3 uses the integer word. */
function signedInteger(ast: Ast): number | null {
  let sign = 1;
  let cur = ast;
  while (cur.k === "neg") {
    sign = -sign;
    cur = cur.a;
  }
  if (cur.k !== "int") return null;
  const n = sign * cur.n;
  if (!Number.isSafeInteger(n)) return null;
  return n;
}

function normalize(source: string): string {
  return source.replaceAll("−", "-").replaceAll("×", "*").replaceAll("÷", "/");
}

// TODO(debt): this is a second parser, and the Fr/G fraction arithmetic above
// is a second rational engine, beside compileExpression in parse.ts (the fold
// at parse.ts:389). They stay split so a press sequence does not go through
// the scientific compiler. Fold them when the two grammars can share one AST.
function parse(source: string): Ast {
  const s = source;
  let i = 0;

  function skip(): void {
    while (i < s.length && (s[i] === " " || s[i] === "\t" || s[i] === "\n" || s[i] === "\r")) i += 1;
  }

  function parseAdd(): Ast {
    let left = parseMul();
    for (;;) {
      skip();
      const op = s[i];
      if (op !== "+" && op !== "-") break;
      i += 1;
      const right = parseMul();
      left = { k: "bin", op, a: left, b: right };
    }
    return left;
  }

  function parseMul(): Ast {
    let left = parseUnary();
    for (;;) {
      skip();
      const op = s[i];
      if (op !== "*" && op !== "/") break;
      i += 1;
      const right = parseUnary();
      left = { k: "bin", op, a: left, b: right };
    }
    return left;
  }

  function parseUnary(): Ast {
    skip();
    if (s[i] === "+") {
      i += 1;
      return parseUnary();
    }
    if (s[i] === "-") {
      i += 1;
      return { k: "neg", a: parseUnary() };
    }
    return parsePow();
  }

  function parsePow(): Ast {
    const base = parseAtom();
    skip();
    if (s[i] === "^") {
      i += 1;
      return { k: "bin", op: "^", a: base, b: parseUnary() };
    }
    if (s[i] === "*" && s[i + 1] === "*") {
      i += 2;
      return { k: "bin", op: "^", a: base, b: parseUnary() };
    }
    return base;
  }

  function parseAtom(): Ast {
    skip();
    const ch = s[i];
    if (ch === undefined) throw new PressCompileError("The expression ended early.");
    if (ch === "(") {
      i += 1;
      const inner = parseAdd();
      skip();
      if (s[i] !== ")") throw new PressCompileError("A parenthesis is missing its close.");
      i += 1;
      return inner;
    }
    if (ch === ".") throw new PressCompileError("Decimals are not compiled. Write a fraction such as 1/2.");
    if (ch >= "0" && ch <= "9") return { k: "int", n: readNumber() };
    if ((ch >= "A" && ch <= "Z") || (ch >= "a" && ch <= "z")) {
      const name = readName();
      if (name === "i" || name === "I") return { k: "i" };
      throw new PressCompileError(
        `${name} is not supported. This compiler builds presses from integers, i, parentheses, and + − * / ^.`,
      );
    }
    throw new PressCompileError(`Cannot read “${ch}” in the expression.`);
  }

  function readNumber(): number {
    const start = i;
    while (i < s.length && s[i] >= "0" && s[i] <= "9") i += 1;
    if (s[i] === ".") throw new PressCompileError("Decimals are not compiled. Write a fraction such as 1/2.");
    const text = s.slice(start, i);
    const n = Number(text);
    if (!Number.isSafeInteger(n)) throw new PressCompileError(`The integer ${text} is too large to build from 1.`);
    return n;
  }

  function readName(): string {
    const start = i;
    while (i < s.length && /[A-Za-z0-9]/.test(s[i] ?? "")) i += 1;
    return s.slice(start, i);
  }

  const ast = parseAdd();
  skip();
  if (i < s.length) throw new PressCompileError("The expression has an extra symbol.");
  return ast;
}

/** Compile `source` into the 1/E press word. The returned length is that word's length. */
export function compilePresses(source: string): PressSequence {
  const text = normalize(source).trim();
  if (!text) throw new PressCompileError("Enter an expression.");
  const built = lower(parse(text));
  return { node: built.node, word: built.word, presses: built.word.length, via: built.via };
}

/** The press-budget check on a circuit that is already a node. Not exported: the calculator uses compilePresses. */
function compilePressNode(node: Node): PressSequence {
  const built = spell(node, realG(0), []);
  return { node: built.node, word: built.word, presses: built.word.length, via: built.via };
}

/**
 * A full binary circuit past the shared cap must fail with the worker's sentence.
 * The expression parser never builds that node, so compilePresses cannot reach it.
 */
export function oversizedPressNodeIsRejected(): boolean {
  let wide = ONE;
  for (let i = 0; i < 16; i += 1) wide = E(wide, wide);
  try {
    compilePressNode(wide);
    return false;
  } catch (err) {
    return err instanceof PressCompileError && err.message === EXACT_TOO_LARGE;
  }
}
