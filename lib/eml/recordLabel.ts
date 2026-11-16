import { provedFromLine, PROVEN_MINIMAL, statusPill } from "./statusLabels";

export type StatusLine = {
  value: string;
  k: number;
  label: string;
  note: string;
};

/**
 * Status wording shared by the calculator's minimality list and the count-page pills.
 * A proved row uses the shared pill. Anything else keeps the entry's label,
 * then the unproved clause and a tie when the note is the only place those appear.
 */
export function recordPill(line: StatusLine): string {
  if (line.value === "1" && line.k === 1) return "the 1 key itself · K 1";
  if (provedFromLine(line.value, line.k)) return statusPill(true);
  let text = line.label;
  const unproved = `not ${PROVEN_MINIMAL}`;
  if (line.note.toLowerCase().includes(unproved) && !/not proven/.test(line.label)) text += `, ${unproved}`;
  const tie = /ties [^;]+/.exec(line.note);
  if (tie && !text.includes(tie[0])) text += ` (${tie[0]})`;
  return text;
}

/** Clauses of the note that the pill does not already say. */
export function noteBeside(note: string, pill: string): string {
  const have = pill.toLowerCase();
  return note
    .split(";")
    .map((clause) => clause.trim())
    .filter((clause) => clause.length > 0 && !have.includes(clause.toLowerCase()))
    .join("; ");
}

/** The pill, then every caveat the pill does not already show. */
export function recordLine(line: StatusLine): string {
  const pill = recordPill(line);
  const extra = noteBeside(line.note, pill);
  return extra ? `${pill}. ${extra}` : pill;
}
