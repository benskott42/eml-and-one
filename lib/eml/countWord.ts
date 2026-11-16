/** Counting construction. n ≥ 2: K = 10n − 1; n = −m: K = 10m + 7; 1: K 1; 0: K 7. Exact on both cuts without ln 0; see docs/counting.md. These are constructions, not minimal words. */

export const BLOCK = "EEE1EE11";

export function countWord(n: number): string {
  if (!Number.isSafeInteger(n)) throw new RangeError(`countWord: integer required, got ${n}`);
  if (n === 1) return "1";
  if (n === 0) return "111E1EE";
  if (n >= 2) return "1".repeat(2 * n + 2) + BLOCK.repeat(n - 1) + "EE1EE";
  const m = -n;
  return "11".repeat(m) + "111" + BLOCK.repeat(m) + "E1EE";
}

export function countWordLength(n: number): number {
  if (!Number.isSafeInteger(n)) throw new RangeError(`countWord: integer required, got ${n}`);
  return n === 1 ? 1 : n === 0 ? 7 : n >= 2 ? 10 * n - 1 : 10 * -n + 7;
}

/** One span per `EEE1EE11` block, in press order. */
export function blockSpans(n: number): Array<[number, number]> {
  const word = countWord(n);
  const blocks = n >= 2 ? n - 1 : n <= -1 ? -n : 0;
  const start = n >= 2 ? 2 * n + 2 : n <= -1 ? 2 * -n + 3 : 0;
  const spans: Array<[number, number]> = [];
  for (let i = 0; i < blocks; i += 1) spans.push([start + 8 * i, start + 8 * i + 8]);
  for (const [from, to] of spans) {
    if (word.slice(from, to) !== BLOCK) throw new Error("span bug");
  }
  return spans;
}
