/**
 * Program numbers for constant EML circuits (alphabet {1, E}).
 *
 * Order: by K (RPN length = 2n+1), then lexicographically on the RPN string with 1 < E.
 * Program #0 is "1", #1 is "11E" (e), #2 "111EE", #3 "11E1E", #4 "1111EEE", #5 "111E1EE" (0), ...
 * Global index = sum of Catalan(m) for m < n, plus the rank within size n.
 * A shared DAG is ranked as its expanded tree. rankProgram checks the gate count
 * before expanding, and refuses above MAX_RANK_GATES.
 */
import { E, ONE, type Node, circuitStats, rpnTokens } from "./node";

export const MAX_RANK_GATES = 1000;

const ZERO = BigInt(0);
const ONE_BI = BigInt(1);

const fact: bigint[] = [ONE_BI];
function factorial(k: number): bigint {
  for (let i = fact.length; i <= k; i += 1) {
    const prev = fact[i - 1] ?? ONE_BI;
    fact.push(prev * BigInt(i));
  }
  return fact[k] ?? ONE_BI;
}

function binom(a: number, b: number): bigint {
  if (b < 0 || b > a) return ZERO;
  return factorial(a) / (factorial(b) * factorial(a - b));
}

export function catalan(n: number): bigint {
  return binom(2 * n, n) / BigInt(n + 1);
}

/** Token strings of length r that take stack height s to exactly 1, staying at least 1. */
function completions(r: number, s: number): bigint {
  if (s < 1 || s - 1 > r || (r - s + 1) % 2 !== 0) return ZERO;
  if (r === 0) return s === 1 ? ONE_BI : ZERO;
  return (BigInt(s) * binom(r + 1, (r - s + 1) / 2)) / BigInt(r + 1);
}

function offset(n: number): bigint {
  let total = ZERO;
  for (let m = 0; m < n; m += 1) total += catalan(m);
  return total;
}

const constantCircuitCache = new WeakMap<Node, boolean>();

/** True when every leaf is the constant 1. Variables and typed inputs fail. */
export function isConstantCircuit(node: Node): boolean {
  const hit = constantCircuitCache.get(node);
  if (hit !== undefined) return hit;
  const seen = new Set<number>();
  const stack: Node[] = [node];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n.id)) continue;
    seen.add(n.id);
    if (n.type === "one") continue;
    if (n.type !== "eml" || !n.a || !n.b) {
      if (Object.isFrozen(node)) constantCircuitCache.set(node, false);
      return false;
    }
    stack.push(n.a, n.b);
  }
  if (Object.isFrozen(node)) constantCircuitCache.set(node, true);
  return true;
}

/** True if the string over {1,E} is a valid program (stack stays at least 1, ends at 1). */
export function isProgram(rpn: string): boolean {
  let h = 0;
  for (const t of rpn) {
    if (t === "1") h += 1;
    else if (t === "E") h -= 1;
    else return false;
    if (h < 1) return false;
  }
  return h === 1;
}

export function rankRpn(rpn: string): bigint {
  if (!isProgram(rpn)) throw new RangeError("Not a constant EML program.");
  const n = (rpn.length - 1) / 2;
  let r = ZERO;
  let h = 0;
  for (let i = 0; i < rpn.length; i += 1) {
    if (rpn[i] === "E") r += completions(rpn.length - i - 1, h + 1);
    h += rpn[i] === "1" ? 1 : -1;
  }
  return offset(n) + r;
}

export function unrankRpn(index: bigint, maxGates = MAX_RANK_GATES): string {
  if (index < ZERO) throw new RangeError("Program numbers start at 0.");
  let n = 0;
  let i = index;
  for (;;) {
    const c = catalan(n);
    if (i < c) break;
    i -= c;
    n += 1;
    if (n > maxGates) {
      const digits = approximateIndexDigits(approximateIndexBits(BigInt(maxGates)));
      throw new RangeError(
        `That program number needs more than ${maxGates} gates. Numbers from about 10^${digits.toString()} upward, including 10^1000, are not assigned.`,
      );
    }
  }
  const length = 2 * n + 1;
  let h = 0;
  let out = "";
  for (let p = 0; p < length; p += 1) {
    const c = completions(length - p - 1, h + 1);
    if (i < c) {
      out += "1";
      h += 1;
    } else {
      i -= c;
      out += "E";
      h -= 1;
    }
  }
  return out;
}

const rankCache = new WeakMap<Node, bigint | null>();

/** Program number, or null for variables, typed inputs, or more than maxGates eml nodes. */
export function rankProgram(node: Node, maxGates = MAX_RANK_GATES): bigint | null {
  const useCache = maxGates === MAX_RANK_GATES && Object.isFrozen(node);
  if (useCache && rankCache.has(node)) {
    return rankCache.get(node) ?? null;
  }
  const stats = circuitStats(node);
  let result: bigint | null = null;
  if (stats.treeGates <= BigInt(maxGates)) {
    const tokens = rpnTokens(node, 2 * maxGates + 1);
    if (tokens && !tokens.some((t) => t !== "1" && t !== "E")) {
      result = rankRpn(tokens.join(""));
    }
  }
  if (useCache) rankCache.set(node, result);
  return result;
}

/** Circuit for a program number. E hash-conses, so shared subtrees are shared nodes. */
export function unrankProgram(index: bigint, maxGates = MAX_RANK_GATES): Node {
  const stack: Node[] = [];
  for (const token of unrankRpn(index, maxGates)) {
    if (token === "1") {
      stack.push(ONE);
      continue;
    }
    const b = stack.pop();
    const a = stack.pop();
    if (!a || !b) throw new RangeError("That program number did not build a circuit.");
    stack.push(E(a, b));
  }
  const node = stack[0];
  if (!node || stack.length !== 1) throw new RangeError("That program number did not build a circuit.");
  return node;
}

/**
 * Cycle lemma: a word with one more 1 than E has exactly one rotation that is a program.
 * It starts just after the last position where the running height is lowest.
 */
export function rotateToProgram(word: string): string {
  let ones = 0;
  for (const token of word) {
    if (token === "1") ones += 1;
    else if (token !== "E") throw new RangeError("Use only 1 and E.");
  }
  if (2 * ones !== word.length + 1) throw new RangeError("A program has exactly one more 1 than E.");
  let h = 0;
  let min = 0;
  let pos = 0;
  for (let i = 0; i < word.length; i += 1) {
    h += word[i] === "1" ? 1 : -1;
    if (h <= min) {
      min = h;
      pos = i + 1;
    }
  }
  return word.slice(pos) + word.slice(0, pos);
}

/** Next or previous program number. Program #0 has no previous. */
export function stepProgram(index: bigint, delta: 1 | -1): bigint {
  const next = index + BigInt(delta);
  return next < ZERO ? ZERO : next;
}

/** log2 of a positive bigint, from its bits, accurate to the leading 53 bits. */
function log2Number(n: bigint): number {
  if (n <= ONE_BI) return 0;
  const text = n.toString(2);
  const floor = text.length - 1;
  const width = Math.min(text.length, 53);
  const mant = Number.parseInt(text.slice(0, width), 2);
  return Math.log2(mant) + (floor - (width - 1));
}

/**
 * Rounded log2 of Catalan(gates). The exponent is a bigint, so a tower past
 * 2^53 gates still reports its real magnitude. Stirling: log2(C_n) ≈ 2n − 1.5 log2(n) − 0.5 log2(π).
 */
export function approximateIndexBits(gates: bigint): bigint {
  if (gates <= ONE_BI) return ZERO;
  const correction = 1.5 * log2Number(gates) + 0.5 * Math.log2(Math.PI);
  const bits = gates * BigInt(2) - BigInt(Math.round(correction));
  return bits > ZERO ? bits : ZERO;
}

/** Decimal digits of an index whose bit length is `bits`: floor(bits · log10(2)). */
export function approximateIndexDigits(bits: bigint): bigint {
  if (bits <= ZERO) return ZERO;
  return (bits * BigInt(30103)) / BigInt(100000);
}

/** Every digit of a numbered constant. Null when it is not a constant or is past the rank limit. */
export function programIndexDigits(node: Node): string | null {
  if (!isConstantCircuit(node)) return null;
  let gates = ZERO;
  try {
    gates = circuitStats(node).treeGates;
  } catch {
    return null;
  }
  if (gates > BigInt(MAX_RANK_GATES)) return null;
  const rank = rankProgram(node);
  return rank === null ? null : rank.toString();
}

/** "program #N" for a constant circuit, or an approximate power of two above the rank limit. */
export function programNumberText(node: Node): string | null {
  if (!isConstantCircuit(node)) return null;
  let gates = ZERO;
  try {
    gates = circuitStats(node).treeGates;
  } catch {
    return null;
  }
  if (gates > BigInt(MAX_RANK_GATES)) return `program ≈ 2^${approximateIndexBits(gates).toString()}`;
  const text = programIndexDigits(node);
  if (text === null) return null;
  if (text.length > 16) return `program #${text.slice(0, 4)}…${text.slice(-4)} (${text.length} digits)`;
  return `program #${text}`;
}

/**
 * Why a constant has no program number. Null when it is numbered, or when it is not a constant.
 * Stepping uses this so a tower past the gate limit is not described as an ordinary non-program.
 */
export function unnumberedReason(node: Node): string | null {
  if (!isConstantCircuit(node)) return null;
  let gates = ZERO;
  try {
    gates = circuitStats(node).treeGates;
  } catch {
    return `This constant is past ${MAX_RANK_GATES} gates, so it is not numbered.`;
  }
  if (gates <= BigInt(MAX_RANK_GATES)) return null;
  const digits = approximateIndexDigits(approximateIndexBits(gates));
  return `This constant has ${gates.toString()} gates, past ${MAX_RANK_GATES}, so it is not numbered. Its index would be about 10^${digits.toString()}.`;
}

export type ParsedProgram =
  | { kind: "index"; index: bigint }
  | {
      kind: "word";
      word: string;
      /** What the user typed (bits stay bits), when a rotation changed it. */
      rotatedFrom: string | null;
      /** Set only for input that opted in with "old:". The bits it was typed as, in the old convention. */
      oldBits: string | null;
      /** For "old:" input, the same presses in the current convention (E = 1, the 1 key = 0), before any rotation. */
      newBits: string | null;
    };

/** Opt-in prefix for bits in the old convention (0 = EML, 1 = the 1 key). Nothing else selects it. */
export const OLD_BITS_PREFIX = "old:";

/** Bits in the current convention: E = 1, the 1 key = 0. x and y stay letters. */
export function bitsToWord(bits: string): string {
  return bits.replace(/[01]/g, (bit) => (bit === "1" ? "E" : "1"));
}

/** A word of 1, E, x, y in the current bit convention: E = 1, the 1 key = 0. */
export function wordToBits(word: string): string {
  return word.replace(/[1E]/g, (key) => (key === "E" ? "1" : "0"));
}

/**
 * A word of 1, E, x, and y has to be one RPN program.
 * Null when it is. The message says whether E ran out of values or the word left the wrong number.
 */
export function wordProgramError(word: string): string | null {
  let height = 0;
  for (const token of word) {
    if (token === "1" || token === "x" || token === "y") height += 1;
    else if (token === "E") {
      if (height < 2) return "That word uses E before it has two values.";
      height -= 1;
    } else {
      return "Use # and digits, bits of 0 and 1, or a word of 1, E, x, and y.";
    }
  }
  if (height !== 1) return "That word does not leave one value.";
  return null;
}

/**
 * A program number is # followed by digits. A string of 0 and 1 is button presses in
 * the current convention, E = 1 and the 1 key = 0 (the ID bits without their leading 1),
 * and is rotated into the one valid program. rotatedFrom is the text the user typed when
 * that rotation changed it.
 *
 * Which reading applies is set by the characters, never by trying both:
 * - any E or e: a word of 1, E, x, and y;
 * - any 0: bits;
 * - only 1, x, and y: bits, except the single key "1", which is the word 1
 *   (as bits it would be one E, which is never a program).
 *
 * Old-convention bits (0 = EML, 1 = the 1 key) are read only after the explicit prefix
 * "old:". Their meaning is never guessed from the content. Unprefixed old bits cannot be
 * misread: a valid old string has its E's as 0s, so read in the new convention it has
 * too many E's (pure 1/E) or ends in a leaf (with x or y), and is always rejected.
 *
 * A word of 1, E, x, and y is checked here, before it is built. Spaces inside a number are
 * an error, and a minus sign is reported on its own.
 */
export function parseProgramInput(source: string): ParsedProgram {
  const raw = source.trim();
  if (!raw) throw new RangeError("Enter a program number, bits, or a word of 1 and E.");
  if (raw.toLowerCase().startsWith(OLD_BITS_PREFIX)) return parseOldBits(raw.slice(OLD_BITS_PREFIX.length));
  if (raw.includes("-")) throw new RangeError("Program numbers are not negative.");
  if (raw.startsWith("#")) {
    if (/\s/.test(raw)) throw new RangeError("A program number cannot contain spaces.");
    const digits = raw.slice(1);
    if (!/^\d+$/.test(digits)) throw new RangeError("A program number is # followed by digits, such as #1.");
    return { kind: "index", index: BigInt(digits) };
  }
  if (/\s/.test(raw) && /[2-9]/.test(raw)) {
    throw new RangeError("A program number cannot contain spaces. Write it as # followed by the digits.");
  }
  const compact = raw.replace(/\s+/g, "");
  if (/[2-9]/.test(compact)) {
    throw new RangeError("Program numbers start with #. A string of 0 and 1 is bits.");
  }
  if (/[eE]/.test(compact) || compact === "1") {
    if (!/^[1eExXyY]+$/.test(compact)) {
      throw new RangeError("Use # and digits, bits of 0 and 1, or a word of 1, E, x, and y.");
    }
    const word = compact.replace(/e/g, "E").replace(/X/g, "x").replace(/Y/g, "y");
    if (/^[1E]+$/.test(word)) {
      const turned = rotateToProgram(word);
      return { kind: "word", word: turned, rotatedFrom: turned === word ? null : word, oldBits: null, newBits: null };
    }
    const mixed = wordProgramError(word);
    if (mixed) throw new RangeError(mixed);
    return { kind: "word", word, rotatedFrom: null, oldBits: null, newBits: null };
  }
  if (!/^[01xXyY]+$/.test(compact)) {
    throw new RangeError("Use # and digits, bits of 0 and 1, or a word of 1, E, x, and y.");
  }
  const bits = compact.replace(/X/g, "x").replace(/Y/g, "y");
  const pressed = bitsToWord(bits);
  const hint = ` Bits read as E = 1 and the 1 key = 0. For bits in the old convention (0 = EML), type ${OLD_BITS_PREFIX} in front.`;
  if (/^[1E]+$/.test(pressed)) {
    let turned: string;
    try {
      turned = rotateToProgram(pressed);
    } catch {
      throw new RangeError(`As bits, a program has exactly one more 0 (the 1 key) than 1 (E).${hint}`);
    }
    return { kind: "word", word: turned, rotatedFrom: turned === pressed ? null : bits, oldBits: null, newBits: null };
  }
  const mixed = wordProgramError(pressed);
  if (mixed) throw new RangeError(`${mixed}${hint}`);
  return { kind: "word", word: pressed, rotatedFrom: null, oldBits: null, newBits: null };
}

/**
 * The note shown after loading parsed word input, or null when there is nothing to say.
 * Old-convention input always says so, with the same presses in the current bits.
 */
export function loadNotice(parsed: ParsedProgram): string | null {
  if (parsed.kind !== "word") return null;
  const parts: string[] = [];
  if (parsed.oldBits !== null && parsed.newBits !== null) {
    parts.push(`Read in the old convention (0 = EML), shown here as ${parsed.newBits}.`);
  }
  const from = parsed.rotatedFrom;
  if (from !== null) {
    const fromBits = !/E/.test(from);
    parts.push(`Rotated ${from} to ${fromBits ? wordToBits(parsed.word) : parsed.word}.`);
  }
  return parts.length ? parts.join(" ") : null;
}

/** Bits after "old:": 0 = EML, 1 = the 1 key. Bits only; no numbers or words. */
function parseOldBits(rest: string): ParsedProgram {
  const bits = rest.replace(/\s+/g, "").replace(/X/g, "x").replace(/Y/g, "y");
  if (!bits) throw new RangeError(`Put old-convention bits after ${OLD_BITS_PREFIX}, such as ${OLD_BITS_PREFIX}110.`);
  if (!/^[01xy]+$/.test(bits)) {
    throw new RangeError(`After ${OLD_BITS_PREFIX} use only bits of 0 and 1 (0 = EML), with x or y.`);
  }
  const pressed = bits.replace(/0/g, "E");
  const newBits = wordToBits(pressed);
  if (/^[1E]+$/.test(pressed)) {
    let turned: string;
    try {
      turned = rotateToProgram(pressed);
    } catch {
      throw new RangeError("Read in the old convention (0 = EML), a program has exactly one more 1 than 0.");
    }
    return { kind: "word", word: turned, rotatedFrom: turned === pressed ? null : newBits, oldBits: bits, newBits };
  }
  const mixed = wordProgramError(pressed);
  if (mixed) throw new RangeError(mixed);
  return { kind: "word", word: pressed, rotatedFrom: null, oldBits: bits, newBits };
}
