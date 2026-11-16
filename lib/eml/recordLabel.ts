export type StatusLine = {
  value: string;
  k: number;
  label: string;
  note: string;
};

/**
 * Status wording shared by the calculator's minimality list and the count-page pills.
 * n = 1 is the key itself. Other lines keep the entry's label, then the
 * "not proven" clause and a tie when the note is the only place those appear.
 */
export function recordPill(line: StatusLine): string {
  if (line.value === "1" && line.k === 1) return "the 1 key itself · K 1";
  let text = line.label;
  if (/not proven minimal/.test(line.note) && !/not proven/.test(line.label)) text += ", not proven minimal";
  const tie = /ties [^;]+/.exec(line.note);
  if (tie) text += ` (${tie[0]})`;
  return text;
}

/** The shared pill, plus the note when it states the basis for "proven minimal". */
export function recordLine(line: StatusLine): string {
  const pill = recordPill(line);
  if (/K ≤|2056/.test(line.note)) return `${pill}. ${line.note}`;
  return pill;
}
