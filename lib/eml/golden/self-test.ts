/**
 * Parser and comparer checks. They use synthetic files, not the corpus.
 * A duplicate key, an unparseable line, a deleted row, and an edited row
 * must all exit non-zero with a message that names the problem.
 */
import { compareGolden, formatGolden, type GoldenEntry } from "./compare";

function row(source: string, exact = "1"): GoldenEntry {
  return {
    source,
    exactText: exact,
    exactNotes: ["certified"],
    floatText: exact,
    floatNotes: [],
    pressCount: "1",
    roundTrip: "OK",
  };
}

function assertFails(name: string, messages: string[], pattern: RegExp) {
  if (messages.length === 0 || !messages.some((message) => pattern.test(message))) {
    throw new Error(`${name}: expected ${pattern}, got ${JSON.stringify(messages)}`);
  }
}

export function runGoldenSelfTest(): void {
  const clean = formatGolden("in-process", [row("1+1"), row("pi", "3")]);

  const edited = clean.replace("exact: 1 |", "exact: 9 |");
  assertFails("edited row", compareGolden(edited, clean), /CHANGED: 1\+1/);

  const lines = clean.split("\n").filter((line) => line.startsWith("expr:"));
  const deleted = clean.replace(lines[1] + "\n", "").replace("# rows: 2", "# rows: 1");
  assertFails("deleted row", compareGolden(deleted, clean), /NEW: pi/);

  const duplicate = `${clean.trimEnd()}\n${lines[0]}\n`;
  assertFails("duplicate key", compareGolden(duplicate, duplicate), /duplicate key: 1\+1/);

  const oneEditedCopy = duplicate.replace("exact: 1 |", "exact: 8 |");
  assertFails("edited copy of a duplicate", compareGolden(oneEditedCopy, clean), /duplicate key: 1\+1/);

  const garbage = `${clean}this is not a golden row\n`;
  assertFails("unparseable line", compareGolden(garbage, clean), /unparseable/);

  const wire = formatGolden("fresh-process", [
    { ...row("sqrt(-0)", "−0"), eval2Text: "−0", eval2Notes: ["certified"] },
  ]);
  const wireDrop = wire.replace(/ \| eval2: −0 \| eval2-notes: certified/, "");
  assertFails("wire row missing second eval", compareGolden(wireDrop, wire), /unparseable|CHANGED/);

  if (compareGolden(clean, clean).length !== 0) {
    throw new Error("identical files should compare clean");
  }
}
