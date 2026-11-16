import rows from "./integer-table.json";

type Row = {
  n: number;
  presses: number;
  pressesNoLn0: number;
  minimal: boolean;
  minimalNoLn0: boolean;
};

const TABLE = rows as Row[];

/** The only copy of the proved-row pill. */
export const PROVEN_MINIMAL = "proven minimal";

export function statusPill(proved: boolean): string {
  return proved ? PROVEN_MINIMAL : `shortest known, not ${PROVEN_MINIMAL}`;
}

function rowFor(n: number): Row | undefined {
  return TABLE.find((item) => item.n === n);
}

/** The integer table's flag. A construction label is not a status. */
export function provedMinimal(n: number, mode: "ln0" | "strict"): boolean {
  const row = rowFor(n);
  if (!row) return false;
  return mode === "ln0" ? row.minimal : row.minimalNoLn0;
}

export function provedFromLine(value: string, k: number): boolean {
  if (!/^[−-]?\d+$/.test(value)) return false;
  const n = Number(value.replace("−", "-"));
  const row = rowFor(n);
  if (!row) return false;
  if (k === row.presses) return row.minimal;
  if (k === row.pressesNoLn0) return row.minimalNoLn0;
  return false;
}
