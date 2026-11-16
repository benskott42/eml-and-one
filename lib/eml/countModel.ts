import { BLOCK, blockSpans, countWord, countWordLength } from "./countWord";
import { linesFor, ln0Use, tableEntry, type CountEntry } from "./countTable";

export { BLOCK };

export type CountChoice = {
  n: number;
  word: string;
  K: number;
  source: "family" | "table";
  familyWord: string;
  familyK: number;
  familyLabel: string;
  table: CountEntry | null;
  spans: Array<[number, number]>;
  chunks: Array<{ label: string; start: number; end: number; kind: "prefix" | "blocks" | "tail" | "record"; reps?: number }>;
};

export function familyLabel(n: number): string {
  if (n >= 2) return "counting construction: K = 10n − 1 (gives exactly n on both cuts, without ln 0)";
  if (n <= -1) return "counting construction: K = 10m + 7, m = −n (gives exactly n on both cuts, without ln 0)";
  if (n === 1) return "the 1 key: 1 press";
  return "ln(1) via the ln template 11xE1EE: 7 presses";
}

export function choose(n: number, mode: "ln0" | "strict"): CountChoice {
  const familyWord = countWord(n);
  const familyK = countWordLength(n);
  const found = tableEntry(n, mode, familyWord);
  const table = found && found.k <= familyK ? found : null;
  const word = table && table.k < familyK ? table.word : familyWord;
  const spans = word === familyWord ? blockSpans(n) : [];
  const chunks: CountChoice["chunks"] = [];
  if (word !== familyWord) chunks.push({ label: "table word", start: 0, end: word.length, kind: "record" });
  else if (spans.length) {
    const start = spans[0]?.[0] ?? 0;
    const end = spans[spans.length - 1]?.[1] ?? start;
    chunks.push({ label: n >= 2 ? `push ${start} ones` : `(11)×${-n} then 111`, start: 0, end: start, kind: "prefix" });
    chunks.push({ label: "EEE1EE11", start, end, kind: "blocks", reps: spans.length });
    chunks.push({ label: n >= 2 ? "tail EE1EE" : "tail E1EE", start: end, end: word.length, kind: "tail" });
  } else chunks.push({ label: n === 1 ? "the 1 key" : "ln(1)", start: 0, end: word.length, kind: "record" });
  return {
    n,
    word,
    K: word.length,
    source: word === familyWord ? "family" : "table",
    familyWord,
    familyK,
    familyLabel: familyLabel(n),
    table,
    spans,
    chunks,
  };
}

/** Words the page can show, plus every program word the selection rule resolves. */
export function wordsForCutRule(): Array<[string, string]> {
  const words = new Map<string, string>();
  for (const mode of ["ln0", "strict"] as const) {
    for (let n = -50; n <= 50; n += 1) {
      const choice = choose(n, mode);
      words.set(choice.word, `${n}/${mode} K${choice.K}`);
      const line = linesFor(n).find((item) => mode === "ln0" || ln0Use(item) === "no" || ln0Use(item) === "both");
      if (line) {
        const entry = tableEntry(n, mode, choice.familyWord);
        if (entry) words.set(entry.word, `${n}/${mode} K${entry.k}`);
      }
    }
  }
  return [...words];
}
