/**
 * Binary representation of constant EML programs (1 = `1` key, 0 = `EML` key).
 *
 * Every valid n-gate constant EML program is a (2n + 1)-bit integer with:
 * - bit length 2n + 1 (odd),
 * - popcount n + 1 (one more 1 than 0),
 * - every prefix having strictly more 1s than 0s (Dyck-prefix integer,
 *   sequence: 1, 6, 26, 28, 106, 108, 114, 116, 120, ...; count per odd
 *   bit-length 2n + 1 is the Catalan number C_n).
 *
 * By the Cycle Lemma, all C(2n + 1, n + 1) balanced-weight (2n + 1)-bit
 * strings partition into C_n disjoint cyclic orbits of size 2n + 1, each
 * containing exactly one valid EML program.
 */
import { MAX_RANK_GATES, isProgram, rankRpn, rotateToProgram, unrankRpn } from "./programIndex";

export type BinaryProgramInfo = {
  hex: string;
  decimal: string | null;
  bits: number;
  ones: number;
  zeros: number;
};

export type CycleOrbit = {
  canonical: string;
  rotation: number;
  orbitSize: number;
};

export type BinaryTreeMetrics = {
  gates: number;
  maxStack: number;
  depth: number;
};

/** Convert a constant RPN word over {1, E} to its binary press string over {1, 0}. */
export function rpnToBinary(rpn: string): string {
  if (!/^[1E]+$/.test(rpn)) throw new RangeError("Use only 1 and E.");
  return rpn.replace(/E/g, "0");
}

/** Convert a binary press string over {1, 0} to an RPN word over {1, E}. */
export function binaryToRpn(bits: string): string {
  if (!/^[01]+$/.test(bits)) throw new RangeError("Use only 0 and 1.");
  return bits.replace(/0/g, "E");
}

/** True when positive integer `n` in binary is a valid constant EML program without rotation. */
export function isValidBinaryProgram(n: bigint): boolean {
  if (n <= BigInt(0)) return false;
  return isProgram(binaryToRpn(n.toString(2)));
}

/**
 * Binary integer metadata for a constant button-press string (1 = `1`, 0 = `EML`).
 * Returns null if `bits` is empty, contains non-binary chars, or exceeds `maxBits`.
 */
export function binaryProgramInfo(bits: string, maxBits = 256): BinaryProgramInfo | null {
  if (!bits || bits.length > maxBits || !/^[01]+$/.test(bits)) return null;
  let ones = 0;
  for (let i = 0; i < bits.length; i += 1) {
    if (bits[i] === "1") ones += 1;
  }
  const zeros = bits.length - ones;
  const value = BigInt(`0b${bits}`);
  return {
    hex: `0x${value.toString(16)}`,
    decimal: bits.length <= 64 ? value.toString(10) : null,
    bits: bits.length,
    ones,
    zeros,
  };
}

/**
 * Cycle Lemma orbit for a balanced binary string (n + 1 ones, n zeros).
 * Returns the unique valid binary program in its cyclic orbit and the left-rotation offset.
 */
export function cycleOrbit(bits: string): CycleOrbit {
  const rpn = binaryToRpn(bits);
  const rotated = rotateToProgram(rpn);
  const canonical = rpnToBinary(rotated);
  // Find the unique left-rotation offset in [0, bits.length) producing canonical.
  let rotation = 0;
  if (canonical !== bits) {
    for (let k = 1; k < bits.length; k += 1) {
      if (bits.slice(k) + bits.slice(0, k) === canonical) {
        rotation = k;
        break;
      }
    }
  }
  return { canonical, rotation, orbitSize: bits.length };
}

/**
 * Smallest valid binary EML program of `gates` gates (2*gates + 1 bits):
 * `1` followed by alternating `10` pairs, e.g. n=0 -> 1, n=1 -> 110 (6), n=2 -> 11010 (26).
 */
export function minBinaryProgram(gates: number): bigint {
  if (!Number.isInteger(gates) || gates < 0) throw new RangeError("Gate count must be a non-negative integer.");
  if (gates === 0) return BigInt(1);
  return BigInt(`0b1${"10".repeat(gates)}`);
}

/**
 * Largest valid binary EML program of `gates` gates (2*gates + 1 bits):
 * `n + 1` ones followed by `n` zeros, e.g. n=0 -> 1, n=1 -> 110 (6), n=2 -> 11100 (28).
 */
export function maxBinaryProgram(gates: number): bigint {
  if (!Number.isInteger(gates) || gates < 0) throw new RangeError("Gate count must be a non-negative integer.");
  return BigInt(`0b${"1".repeat(gates + 1)}${"0".repeat(gates)}`);
}

/**
 * Smallest valid binary EML program >= `n`, in O(bitlen) time.
 * Useful for stepping through the binary-program sequence 1, 6, 26, 28, 106, 108, 114, 116, 120, ...
 */
export function nextBinaryProgram(n: bigint): bigint {
  if (n <= BigInt(1)) return BigInt(1);
  const bits = n.toString(2);
  const len = bits.length;
  // Valid programs only exist at odd bit lengths 2g + 1.
  if (len % 2 === 0) return minBinaryProgram(len / 2);
  const gates = (len - 1) / 2;
  const hi = maxBinaryProgram(gates);
  if (n > hi) return minBinaryProgram(gates + 1);
  const lo = minBinaryProgram(gates);
  if (n <= lo) return lo;
  if (isValidBinaryProgram(n)) return n;

  // Find the smallest valid (2g + 1)-bit program strictly greater than `bits`:
  // scan from right to left for a '0' at index i that can be flipped to '1' while
  // keeping prefix[0..i-1] strictly valid and remaining ones/zeros feasible.
  const onesBefore: number[] = new Array<number>(len + 1).fill(0);
  const validPrefix: boolean[] = new Array<boolean>(len + 1).fill(true);
  let h = 0;
  for (let i = 0; i < len; i += 1) {
    onesBefore[i + 1] = onesBefore[i]! + (bits[i] === "1" ? 1 : 0);
    h += bits[i] === "1" ? 1 : -1;
    validPrefix[i + 1] = validPrefix[i]! && h >= 1;
  }

  for (let i = len - 1; i >= 1; i -= 1) {
    if (bits[i] !== "0" || !validPrefix[i]) continue;
    const onesUsed = onesBefore[i]! + 1;
    const zerosUsed = i - onesBefore[i]!;
    const remOnes = gates + 1 - onesUsed;
    const remZeros = gates - zerosUsed;
    if (remOnes < 0 || remZeros < 0) continue;
    // After placing '1' at i, height is (onesUsed - zerosUsed) >= 2.
    // To minimize the suffix lexicographically (smallest binary value), place as many
    // '0's as possible while keeping height >= 1, then alternate '10' for remaining ones.
    const heightAfter = onesUsed - zerosUsed;
    const dropZeros = Math.min(remZeros, heightAfter - 1);
    const suffix = `${"0".repeat(dropZeros)}${"10".repeat(remOnes)}${"0".repeat(remZeros - dropZeros - remOnes)}`;
    const candidate = `${bits.slice(0, i)}1${suffix}`;
    if (isProgram(binaryToRpn(candidate))) return BigInt(`0b${candidate}`);
  }
  return minBinaryProgram(gates + 1);
}

/**
 * Direct bijection from a valid binary EML program integer to its Catalan program rank (#N).
 * Throws if `n` is not a valid binary EML program.
 */
export function binaryToRank(n: bigint): bigint {
  if (!isValidBinaryProgram(n)) throw new RangeError("Not a valid binary EML program.");
  return rankRpn(binaryToRpn(n.toString(2)));
}

/**
 * Inverse bijection from a Catalan program rank (#N) to its binary EML program integer.
 * For example: #0 -> 1 (0x1), #1 -> 6 (0x6), #5 -> 116 (0x74).
 */
export function rankToBinary(rank: bigint, maxGates = MAX_RANK_GATES): bigint {
  return BigInt(`0b${rpnToBinary(unrankRpn(rank, maxGates))}`);
}

/**
 * Structural metrics of a valid constant binary EML program:
 * gate count, RPN stack high-water mark, and expression tree depth (0 for `1`).
 */
export function binaryTreeMetrics(bits: string): BinaryTreeMetrics {
  const rpn = binaryToRpn(bits);
  if (!isProgram(rpn)) throw new RangeError("Not a valid binary EML program.");
  const depths: number[] = [];
  let maxStack = 0;
  for (let i = 0; i < rpn.length; i += 1) {
    if (rpn[i] === "1") {
      depths.push(0);
      if (depths.length > maxStack) maxStack = depths.length;
    } else {
      const b = depths.pop()!;
      const a = depths.pop()!;
      depths.push(Math.max(a, b) + 1);
    }
  }
  return {
    gates: (rpn.length - 1) / 2,
    maxStack,
    depth: depths[0] ?? 0,
  };
}

/**
 * Dyck-path stack-height profile after each bit of a valid binary EML program.
 * Starts at 1, stays >= 1 throughout, and ends at 1.
 */
export function dyckProfile(bits: string): number[] {
  const rpn = binaryToRpn(bits);
  if (!isProgram(rpn)) throw new RangeError("Not a valid binary EML program.");
  const out: number[] = [];
  let h = 0;
  for (let i = 0; i < rpn.length; i += 1) {
    h += rpn[i] === "1" ? 1 : -1;
    out.push(h);
  }
  return out;
}

/**
 * Decode a valid binary EML program directly into its nested E(a, b) formula string.
 * For example: "110" -> "E(1, 1)", "1110100" -> "E(1, E(E(1, 1), 1))".
 */
export function binaryToFormula(bits: string): string {
  const rpn = binaryToRpn(bits);
  if (!isProgram(rpn)) throw new RangeError("Not a valid binary EML program.");
  const stack: string[] = [];
  for (let i = 0; i < rpn.length; i += 1) {
    if (rpn[i] === "1") {
      stack.push("1");
    } else {
      const b = stack.pop()!;
      const a = stack.pop()!;
      stack.push(`E(${a}, ${b})`);
    }
  }
  return stack[0] ?? "1";
}
