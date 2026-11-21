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

/** An n with no integer-table row. A construction, not a searched length. */
export const CONSTRUCTION_RECORD = "a construction, not a search record";

export function statusPill(proved: boolean): string {
  return proved ? PROVEN_MINIMAL : `shortest known, not ${PROVEN_MINIMAL}`;
}

function rowFor(n: number): Row | undefined {
  return TABLE.find((item) => item.n === n);
}

/**
 * Whether the page should call n proved.
 * n = 1 stays neutral in the UI even though the table row is marked minimal:
 * the 1 key is not one of the proved values {0, −1, 2}.
 */
export function provedMinimal(n: number, mode: "ln0" | "strict"): boolean {
  if (n === 1) return false;
  const row = rowFor(n);
  if (!row) return false;
  return mode === "ln0" ? row.minimal : row.minimalNoLn0;
}

export function provedFromLine(value: string, k: number): boolean {
  if (!/^[−-]?\d+$/.test(value)) return false;
  const n = Number(value.replace("−", "-"));
  if (n === 1) return false;
  const row = rowFor(n);
  if (!row) return false;
  if (k === row.presses) return row.minimal;
  if (k === row.pressesNoLn0) return row.minimalNoLn0;
  return false;
}
