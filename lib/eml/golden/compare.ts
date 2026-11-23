/**
 * Golden file format. One expression per line, fields separated by " | ".
 * Comment lines start with "#". A data line that does not match, and a
 * repeated expression, are errors: the comparer exits non-zero.
 */

export type GoldenEntry = {
  source: string;
  exactText: string;
  exactNotes: string[];
  floatText: string;
  floatNotes: string[];
  pressCount: string;
  roundTrip: string;
  eval2Text?: string;
  eval2Notes?: string[];
  bug?: string;
};

export type GoldenMode = "in-process" | "fresh-process";

const REQUIRED = ["expr", "exact", "exact-notes", "float", "float-notes", "press", "round-trip"] as const;

export function formatEntry(entry: GoldenEntry): string {
  const parts = [
    `expr: ${entry.source}`,
    `exact: ${entry.exactText}`,
    `exact-notes: ${entry.exactNotes.join(",")}`,
    `float: ${entry.floatText}`,
    `float-notes: ${entry.floatNotes.join(",")}`,
    `press: ${entry.pressCount}`,
    `round-trip: ${entry.roundTrip}`,
  ];
  if (entry.eval2Text !== undefined) {
    parts.push(`eval2: ${entry.eval2Text}`);
    parts.push(`eval2-notes: ${(entry.eval2Notes ?? []).join(",")}`);
  }
  if (entry.bug) parts.push(`# KNOWN-BUG ${entry.bug}`);
  return parts.join(" | ");
}

export function formatGolden(mode: GoldenMode, entries: GoldenEntry[]): string {
  const lines = [
    "# EML and One golden output",
    `# mode: ${mode}`,
    `# rows: ${entries.length}`,
    "",
  ];
  for (const entry of entries) lines.push(formatEntry(entry));
  return `${lines.join("\n")}\n`;
}

type Parsed = { rows: Map<string, string>; errors: string[] };

export function parseGolden(content: string): Parsed {
  const rows = new Map<string, string>();
  const errors: string[] = [];
  let mode: GoldenMode | null = null;
  const lines = content.split("\n");
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    if (!line.trim()) continue;
    if (line.startsWith("#")) {
      const named = line.match(/^# mode: (in-process|fresh-process)$/);
      if (named) mode = named[1] as GoldenMode;
      continue;
    }
    const lineNo = index + 1;
    const fields = new Map<string, string>();
    let bug = "";
    let ok = true;
    for (const part of line.split(" | ")) {
      if (part.startsWith("# KNOWN-BUG ")) {
        if (bug) {
          errors.push(`line ${lineNo}: repeated KNOWN-BUG`);
          ok = false;
        }
        bug = part;
        continue;
      }
      const match = part.match(/^([a-z0-9-]+): (.*)$/);
      if (!match) {
        errors.push(`line ${lineNo}: unparseable field ${JSON.stringify(part)}`);
        ok = false;
        continue;
      }
      if (fields.has(match[1])) {
        errors.push(`line ${lineNo}: repeated field ${match[1]}`);
        ok = false;
      }
      fields.set(match[1], match[2]);
    }
    for (const name of REQUIRED) {
      if (!fields.has(name)) {
        errors.push(`line ${lineNo}: unparseable, missing ${name}`);
        ok = false;
      }
    }
    if (mode === "fresh-process" && (!fields.has("eval2") || !fields.has("eval2-notes"))) {
      errors.push(`line ${lineNo}: unparseable, fresh-process row missing eval2`);
      ok = false;
    }
    const source = fields.get("expr");
    if (!ok || source === undefined) continue;
    if (rows.has(source)) errors.push(`duplicate key: ${source}`);
    rows.set(source, line);
  }
  if (!mode) errors.push("unparseable: missing # mode line");
  const count = content.match(/^# rows: (\d+)$/m);
  if (!count) errors.push("unparseable: missing # rows line");
  else if (Number(count[1]) !== rows.size) errors.push(`# rows: ${count[1]} but ${rows.size} unique expressions`);
  return { rows, errors };
}

/** Messages that should make the harness exit non-zero. Empty means match. */
export function compareGolden(existing: string, generated: string): string[] {
  const before = parseGolden(existing);
  const after = parseGolden(generated);
  const messages = [...before.errors.map((error) => `existing: ${error}`), ...after.errors.map((error) => `generated: ${error}`)];
  if (before.errors.length || after.errors.length) return messages;
  for (const [source, line] of after.rows) {
    const previous = before.rows.get(source);
    if (previous === undefined) messages.push(`NEW: ${source}`);
    else if (previous !== line) messages.push(`CHANGED: ${source}\n  - ${previous}\n  + ${line}`);
  }
  for (const source of before.rows.keys()) {
    if (!after.rows.has(source)) messages.push(`REMOVED: ${source}`);
  }
  if (messages.length === 0 && existing !== generated) messages.push("file text differs from the generated golden");
  return messages;
}

/**
 * One shard's rows against the full file. Every generated row must match its line.
 * `owner` (shard 0) also reports rows the file has that the corpus does not, and a
 * file whose row count is not the corpus size.
 */
export function compareGoldenShard(existing: string, generated: string, corpus: string[], owner: boolean): string[] {
  const before = parseGolden(existing);
  const after = parseGolden(generated);
  const messages = [...before.errors.map((error) => `existing: ${error}`), ...after.errors.map((error) => `generated: ${error}`)];
  if (before.errors.length || after.errors.length) return messages;
  for (const [source, line] of after.rows) {
    const previous = before.rows.get(source);
    if (previous === undefined) messages.push(`NEW: ${source}`);
    else if (previous !== line) messages.push(`CHANGED: ${source}
  - ${previous}
  + ${line}`);
  }
  if (owner) {
    const known = new Set(corpus);
    for (const source of before.rows.keys()) if (!known.has(source)) messages.push(`REMOVED: ${source}`);
    if (before.rows.size !== corpus.length) messages.push(`row count ${before.rows.size}, corpus ${corpus.length}`);
  }
  return messages;
}
