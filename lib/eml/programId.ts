/**
 * Program IDs, per program-id-spec.md v1 (mathbot, 2026-11-20).
 *
 * Bits: E -> 1, the 1 key -> 0, written in key order, with one sentinel 1 in front.
 * The ID is that binary string read most significant bit first, so 11E -> 1001 = 9.
 * Decoding drops the leading 1 and maps 1 -> E, 0 -> 1. ID 1 is the empty string.
 *
 * Valid: scanning left to right from depth 0, `1` adds one, `E` needs depth >= 2 and
 * subtracts one, and the scan ends at depth 1.
 *
 * Program number #n (0-based) is the position among valid programs in ID order,
 * which is length first, then lexicographic with 1 < E.
 *
 * Everything is BigInt. The completion counts use a closed form (ballot numbers),
 * so prev, next and the dense index run in O(K^2) bigint operations with no search.
 */

const Z = BigInt(0);
const I1 = BigInt(1);
const I2 = BigInt(2);

/** Longest word this module will decode or build. It matches the calculator's rank limit (1000 gates). */
export const MAX_ID_KEYS = 2001;

const fact: bigint[] = [I1];
function factorial(k: number): bigint {
  for (let i = fact.length; i <= k; i += 1) fact.push((fact[i - 1] ?? I1) * BigInt(i));
  return fact[k] ?? I1;
}

function binom(a: number, b: number): bigint {
  if (b < 0 || b > a) return Z;
  return factorial(a) / (factorial(b) * factorial(a - b));
}

export function catalan(m: number): bigint {
  return binom(2 * m, m) / BigInt(m + 1);
}

/**
 * Ways to finish with `rem` keys starting from stack depth d >= 1 and end at depth 1,
 * where E needs depth >= 2 first. Same as completions(rem, d) in program_id_ref.py for d >= 1.
 */
export function completions(rem: number, d: number): bigint {
  if (d < 1 || d - 1 > rem || (rem - d + 1) % 2 !== 0) return Z;
  if (rem === 0) return d === 1 ? I1 : Z;
  return (BigInt(d) * binom(rem + 1, (rem - d + 1) / 2)) / BigInt(rem + 1);
}

export function isWordText(text: string): boolean {
  return /^[1E]*$/.test(text);
}

export function isValidWord(word: string): boolean {
  let d = 0;
  for (const c of word) {
    if (c === "1") d += 1;
    else if (c === "E") {
      if (d < 2) return false;
      d -= 1;
    } else return false;
  }
  return d === 1;
}

/** The bits of the ID as text, sentinel first. */
export function idBits(word: string): string {
  if (!isWordText(word)) throw new RangeError("A word uses only 1 and E.");
  let out = "1";
  for (const c of word) out += c === "E" ? "1" : "0";
  return out;
}

export function wordToId(word: string): bigint {
  return BigInt(`0b${idBits(word)}`);
}

export function idToWord(id: bigint): string {
  if (id < I1) throw new RangeError("IDs start at 1.");
  const bits = id.toString(2);
  if (bits.length - 1 > MAX_ID_KEYS) throw new RangeError(`That ID decodes to more than ${MAX_ID_KEYS} keys.`);
  let out = "";
  for (let i = 1; i < bits.length; i += 1) out += bits[i] === "1" ? "E" : "1";
  return out;
}

/** Key count of the word an ID decodes to, without decoding it. */
export function idKeys(id: bigint): number {
  return id < I1 ? -1 : id.toString(2).length - 1;
}

export function isValidId(id: bigint): boolean {
  if (id < I1 || idKeys(id) > MAX_ID_KEYS) return false;
  return isValidWord(idToWord(id));
}

function oddLengthOffset(K: number): bigint {
  let total = Z;
  for (let k = 1; k < K; k += 2) total += catalan((k - 1) / 2);
  return total;
}

/** 0-based program number of a valid word. */
export function indexOf(word: string): bigint {
  if (!isValidWord(word)) throw new RangeError("Not a valid program.");
  const K = word.length;
  let idx = oddLengthOffset(K);
  let d = 0;
  for (let p = 0; p < K; p += 1) {
    if (word[p] === "E") idx += completions(K - p - 1, d + 1);
    d += word[p] === "1" ? 1 : -1;
  }
  return idx;
}

/** Inverse of indexOf. Throws instead of clamping when n is negative or names a word past MAX_ID_KEYS. */
export function programAt(n: bigint): string {
  if (n < Z) throw new RangeError("Program numbers start at #0.");
  let K = 1;
  let rest = n;
  for (;;) {
    const c = catalan((K - 1) / 2);
    if (rest < c) break;
    rest -= c;
    K += 2;
    if (K > MAX_ID_KEYS) throw new RangeError(`That program number needs more than ${MAX_ID_KEYS} keys.`);
  }
  let w = "";
  let d = 0;
  for (let p = 0; p < K; p += 1) {
    const c1 = completions(K - p - 1, d + 1);
    if (rest < c1) {
      w += "1";
      d += 1;
    } else {
      rest -= c1;
      w += "E";
      d -= 1;
    }
  }
  return w;
}

/** Lexicographically smallest (or largest) valid completion, with 1 < E. */
function complete(prefix: string, depth: number, rem: number, largest: boolean): string {
  let out = prefix;
  let d = depth;
  let r = rem;
  while (r > 0) {
    const up = completions(r - 1, d + 1);
    const dn = d >= 2 ? completions(r - 1, d - 1) : Z;
    if ((!largest && up > Z) || (largest && dn === Z)) {
      out += "1";
      d += 1;
    } else {
      out += "E";
      d -= 1;
    }
    r -= 1;
  }
  return out;
}

export function firstWord(K: number): string {
  return "1".repeat((K + 1) / 2) + "E".repeat((K - 1) / 2);
}

export function lastWord(K: number): string {
  return K > 1 ? `11${"E1".repeat((K - 3) / 2)}E` : "1";
}

function legalDepths(w: string): number[] {
  const depths: number[] = [];
  let d = 0;
  for (const c of w) {
    depths.push(d);
    if (c === "E" && d < 2) break;
    d += c === "1" ? 1 : -1;
  }
  return depths;
}

/** Smallest valid ID strictly greater than id. */
export function nextValid(id: bigint): bigint {
  if (id < I2) return I2;
  const w = idToWord(id);
  const K = w.length;
  if (K % 2 === 0) return wordToId(firstWord(K + 1));
  const depths = legalDepths(w);
  for (let p = depths.length - 1; p >= 0; p -= 1) {
    const d = depths[p] ?? 0;
    if (w[p] === "1" && d >= 2 && completions(K - p - 1, d - 1) > Z) {
      return wordToId(complete(`${w.slice(0, p)}E`, d - 1, K - p - 1, false));
    }
  }
  if (K + 2 > MAX_ID_KEYS) throw new RangeError(`The next program has more than ${MAX_ID_KEYS} keys.`);
  return wordToId(firstWord(K + 2));
}

/** Largest valid ID strictly less than id, or null at or below 2. */
export function prevValid(id: bigint): bigint | null {
  if (id <= I2) return null;
  const w = idToWord(id);
  const K = w.length;
  if (K % 2 === 0) return wordToId(lastWord(K - 1));
  const depths = legalDepths(w);
  for (let p = depths.length - 1; p >= 0; p -= 1) {
    const d = depths[p] ?? 0;
    if (w[p] === "E" && completions(K - p - 1, d + 1) > Z) {
      return wordToId(complete(`${w.slice(0, p)}1`, d + 1, K - p - 1, true));
    }
  }
  return K > 1 ? wordToId(lastWord(K - 2)) : null;
}

/** The ID itself when valid, else whichever of prev and next is closer; the smaller ID wins a tie. */
export function nearestValid(id: bigint): bigint {
  if (isValidId(id)) return id;
  const a = prevValid(id);
  const b = nextValid(id);
  if (a === null) return b;
  return id - a <= b - id ? a : b;
}

export type JumpResult =
  | { ok: true; word: string; id: bigint; index: bigint; snappedFrom: bigint | null; decodedFrom: string | null }
  | { ok: false; error: string };

/**
 * Parse the jump field. Program mode accepts digits with an optional leading #.
 * ID mode accepts digits only. Nothing is clamped: out-of-range input is an error,
 * and an invalid ID is snapped to its nearest valid ID with snappedFrom set so the UI can say so.
 */
export function jump(text: string, mode: "program" | "id"): JumpResult {
  const raw = text.trim();
  if (!raw) return { ok: false, error: mode === "program" ? "Enter a program number, such as 1 or #1." : "Enter an ID, such as 9." };
  if (/^[-−]/.test(raw)) return { ok: false, error: mode === "program" ? "Program numbers start at #0." : "IDs start at 1." };
  const digits = mode === "program" ? raw.replace(/^#/, "") : raw;
  if (!/^\d+$/.test(digits)) {
    return {
      ok: false,
      error: mode === "program" ? "A program number is whole digits, optionally after #, such as #1." : "An ID is whole digits, such as 9.",
    };
  }
  const n = BigInt(digits);
  try {
    if (mode === "program") {
      const word = programAt(n);
      return { ok: true, word, id: wordToId(word), index: n, snappedFrom: null, decodedFrom: null };
    }
    if (n < I1) return { ok: false, error: "IDs start at 1." };
    if (idKeys(n) > MAX_ID_KEYS) return { ok: false, error: `That ID decodes to more than ${MAX_ID_KEYS} keys, so it is not loaded.` };
    const target = nearestValid(n);
    const word = idToWord(target);
    return {
      ok: true,
      word,
      id: target,
      index: indexOf(word),
      snappedFrom: target === n ? null : n,
      decodedFrom: target === n ? null : idToWord(n),
    };
  } catch (err) {
    return { ok: false, error: err instanceof Error ? err.message : String(err) };
  }
}
