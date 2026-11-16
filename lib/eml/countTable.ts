import table from "./best-known.json";
import { recordPill } from "./recordLabel";

export type CountEntry = {
  word: string;
  k: number;
  status: string;
  note: string;
  kind: "proven" | "known" | "upper";
  ln0: boolean;
  source: string;
};

type Min = { value: string; k: number; label: string; note: string };

const LINES = table.minimality as Min[];
const PROGRAMS = table.programs as Record<string, string>;

function asInt(value: string): number | null {
  if (!/^[−-]?\d+$/.test(value)) return null;
  return Number(value.replace("−", "-"));
}

/** Label first. The note is used only when the label does not say how ln 0 is used. */
export function ln0Use(line: Min): "yes" | "no" | "both" | "unknown" {
  for (const text of [line.label, line.note]) {
    if (/with or without ln 0/.test(text)) return "both";
    if (/without ln 0|does not use ln 0|does not need ln 0/.test(text)) return "no";
    if (/uses ln 0|depends on ln 0/.test(text)) return "yes";
  }
  return "unknown";
}

export function pillText(line: Min): string {
  return recordPill(line);
}

export function linesFor(n: number): Min[] {
  return LINES.filter((line) => asInt(line.value) === n);
}

/**
 * Shortest minimality line for n that the mode allows.
 * Strict mode reads programs["<n>-strict"] before programs["<n>"].
 * The other mode reads them in the opposite order, then the counting-construction word.
 */
export function tableEntry(n: number, mode: "ln0" | "strict", familyWord: string): CountEntry | null {
  if (n === 1) {
    const line = linesFor(1).find((item) => item.k === 1);
    return {
      word: "1",
      k: 1,
      status: recordPill(line ?? { value: "1", k: 1, label: "proven minimal", note: "" }),
      note: "",
      kind: "upper",
      ln0: false,
      source: "the 1 key itself",
    };
  }
  const lines = linesFor(n)
    .filter((line) => (mode === "strict" ? ln0Use(line) === "no" || ln0Use(line) === "both" : true))
    .sort((a, b) => a.k - b.k);
  for (const line of lines) {
    const keys = mode === "strict" ? [`${n}-strict`, `${n}`] : [`${n}`, `${n}-strict`];
    const word = [...keys.map((key) => PROGRAMS[key]), familyWord].find((item) => item && item.length === line.k) ?? null;
    if (!word) continue;
    return {
      word,
      k: line.k,
      status: pillText(line),
      note: line.note,
      kind: /^proven minimal/.test(line.label) ? "proven" : "known",
      ln0: ln0Use(line) === "yes",
      source: `best-known.json: ${line.value} at K ${line.k}`,
    };
  }
  return null;
}
