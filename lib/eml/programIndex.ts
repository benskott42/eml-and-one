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

const FACT_CACHE_LIMIT = 2 * MAX_RANK_GATES + 2;
const fact: bigint[] = [ONE_BI];
function factorial(k: number): bigint {
  if (!Number.isInteger(k) || k < 0) throw new RangeError("Factorial requires a non-negative integer.");
  if (k < fact.length) return fact[k] ?? ONE_BI;
  const cacheStop = Math.min(k, FACT_CACHE_LIMIT);
  for (let i = fact.length; i <= cacheStop; i += 1) {
    const prev = fact[i - 1] ?? ONE_BI;
    fact.push(prev * BigInt(i));
  }
  let acc = fact[cacheStop] ?? ONE_BI;
  for (let i = cacheStop + 1; i <= k; i += 1) acc *= BigInt(i);
  return acc;
}

function binom(a: number, b: number): bigint {
  if (b < 0 || b > a) return ZERO;
  return factorial(a) / (factorial(b) * factorial(a - b));
}

export function catalan(n: number): bigint {
  if (!Number.isInteger(n) || n < 0) throw new RangeError("Catalan index must be a non-negative integer.");
  return binom(2 * n, n) / BigInt(n + 1);
}

/** Token strings of length r that take stack height s to exactly 1, staying at least 1. */
function completions(r: number, s: number): bigint {
  if (s < 1 || s - 1 > r || (r - s + 1) % 2 !== 0) return ZERO;
  if (r === 0) return s === 1 ? ONE_BI : ZERO;
  return (BigInt(s) * binom(r + 1, (r - s + 1) / 2)) / BigInt(r + 1);
}

const offsets: bigint[] = [ZERO];
function offset(n: number): bigint {
  if (n < offsets.length) return offsets[n] ?? ZERO;
  const cacheStop = Math.min(n, MAX_RANK_GATES + 1);
  for (let m = offsets.length; m <= cacheStop; m += 1) {
    offsets.push((offsets[m - 1] ?? ZERO) + catalan(m - 1));
  }
  let total = offsets[cacheStop] ?? ZERO;
  for (let m = cacheStop; m < n; m += 1) total += catalan(m);
  return total;
}

/** True when every leaf is the constant 1. Variables and typed inputs fail. */
export function isConstantCircuit(node: Node): boolean {
  const seen = new Set<number>();
  const stack: Node[] = [node];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n.id)) continue;
    seen.add(n.id);
    if (n.type === "one") continue;
    if (n.type !== "eml" || !n.a || !n.b) return false;
    stack.push(n.a, n.b);
  }
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
  if (!Number.isInteger(maxGates) || maxGates < 0) {
    throw new RangeError(`maxGates must be a non-negative integer.`);
  }
  let n = 0;
  let i = index;
  for (;;) {
    const c = catalan(n);
    if (i < c) break;
    i -= c;
    n += 1;
    if (n > maxGates) {
      const digits = approximateIndexDigits(approximateIndexBits(BigInt(maxGates)));
      const note = digits < BigInt(1000) ? ", including 10^1000," : "";
      throw new RangeError(
        `That program number needs more than ${maxGates} gates. Numbers from about 10^${digits.toString()} upward${note} are not assigned.`,
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

/** Program number, or null for variables, typed inputs, or more than maxGates eml nodes. */
export function rankProgram(node: Node, maxGates = MAX_RANK_GATES): bigint | null {
  if (!isConstantCircuit(node)) return null;
  let treeGates = ZERO;
  try {
    treeGates = circuitStats(node).treeGates;
  } catch {
    return null;
  }
  if (treeGates > BigInt(maxGates)) return null;
  const tokens = rpnTokens(node, 2 * maxGates + 1);
  if (!tokens || tokens.some((t) => t !== "1" && t !== "E")) return null;
  return rankRpn(tokens.join(""));
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
  return (bits * BigInt("3010299956639812")) / BigInt("10000000000000000");
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
  | { kind: "word"; word: string; rotatedFrom: string | null };

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
      return "Use # and digits, a string of 0 and 1, or a word of 1, E, x, and y.";
    }
  }
  if (height !== 1) return "That word does not leave one value.";
  return null;
}

/**
 * A program number is # followed by digits. A string of 0 and 1 is button presses
 * (0 is EML, 1 is the 1 key) and is rotated into the one valid program.
 * rotatedFrom is the text the user typed when that rotation changed it.
 * A word of 1, E, x, and y is checked here, before it is built. Spaces inside
 * a number are an error, and a minus sign is reported on its own.
 */
export function parseProgramInput(source: string): ParsedProgram {
  const raw = source.trim();
  if (!raw) throw new RangeError("Enter a program number, a press string, or a word of 1 and E.");
  if (/^#?\s*[-−]/.test(raw)) throw new RangeError("Program numbers are not negative.");
  if (raw.startsWith("#")) {
    if (/\s/.test(raw)) throw new RangeError("A program number cannot contain spaces.");
    const digits = raw.slice(1);
    if (!/^\d+$/.test(digits)) throw new RangeError("A program number is # followed by digits, such as #110.");
    return { kind: "index", index: BigInt(digits) };
  }
  if (/^[\d\s]+$/.test(raw) && /\s/.test(raw) && /[2-9]/.test(raw)) {
    throw new RangeError("A program number cannot contain spaces. Write it as # followed by the digits.");
  }
  const compact = raw.replace(/\s+/g, "");
  if (/^0[xX][0-9a-fA-F]+$/.test(compact)) {
    const bits = BigInt(compact).toString(2);
    const pressed = bits.replace(/0/g, "E");
    const turned = rotateToProgram(pressed);
    return { kind: "word", word: turned, rotatedFrom: turned === pressed ? null : bits };
  }
  if (/^0[bB][01]+$/.test(compact)) {
    const bits = compact.slice(2);
    const pressed = bits.replace(/0/g, "E");
    const turned = rotateToProgram(pressed);
    return { kind: "word", word: turned, rotatedFrom: turned === pressed ? null : bits };
  }
  if (/^\d+$/.test(compact) && /[2-9]/.test(compact)) {
    throw new RangeError("Program numbers start with #. A string of 0 and 1 is button presses.");
  }
  if (/[eE]/.test(compact)) {
    if (!/^[1eExXyY]+$/.test(compact)) {
      throw new RangeError("Use # and digits, a string of 0 and 1, or a word of 1, E, x, and y.");
    }
    const word = compact.replace(/e/g, "E").replace(/X/g, "x").replace(/Y/g, "y");
    if (/^[1E]+$/.test(word)) {
      const turned = rotateToProgram(word);
      return { kind: "word", word: turned, rotatedFrom: turned === word ? null : word };
    }
    const mixed = wordProgramError(word);
    if (mixed) throw new RangeError(mixed);
    return { kind: "word", word, rotatedFrom: null };
  }
  if (!/^[01xXyY]+$/.test(compact)) {
    throw new RangeError("Use # and digits, a string of 0 and 1, or a word of 1, E, x, and y.");
  }
  const pressed = compact.replace(/0/g, "E").replace(/X/g, "x").replace(/Y/g, "y");
  if (/^[1E]+$/.test(pressed)) {
    const turned = rotateToProgram(pressed);
    return { kind: "word", word: turned, rotatedFrom: turned === pressed ? null : compact };
  }
  const mixed = wordProgramError(pressed);
  if (mixed) throw new RangeError(mixed);
  return { kind: "word", word: pressed, rotatedFrom: null };
}
