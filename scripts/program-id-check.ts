/**
 * Unit checks for lib/eml/programId.ts against program-id-spec.md §6 and,
 * where practical, against outputs of mathbot's program_id_ref.py
 * (scripts/fixtures/program-id-vectors.json, made by scripts/program_id_vectors.py).
 * Run: npx tsx scripts/program-id-check.ts
 */
import fs from "node:fs";
import path from "node:path";
import {
  MAX_ID_KEYS, firstWord, idBits, idToWord, indexOf, isValidId, isValidWord, jump, lastWord,
  nearestValid, nextValid, prevValid, programAt, wordToId,
} from "../lib/eml/programId";
import { OLD_BITS_PREFIX, bitsToWord, loadNotice, parseProgramInput, rankRpn, unrankRpn, wordToBits, type ParsedProgram } from "../lib/eml/programIndex";
import { encodePresses, pressPreviewForNode } from "../lib/eml/presses";
import { nodeFromRpn } from "../lib/eml/node";

let failed = 0;
let passed = 0;
function expect(name: string, ok: boolean, detail = ""): void {
  if (ok) passed += 1;
  else {
    failed += 1;
    console.log(`FAIL ${name}${detail ? ` — ${detail}` : ""}`);
  }
}
const B = (n: number | string) => BigInt(n);

// §2 the headline example
expect("11E -> bits 1001", idBits("11E") === "1001");
expect("11E -> 9", wordToId("11E") === B(9));
expect("9 -> 11E", idToWord(B(9)) === "11E");
expect("ID 1 is the empty string", idToWord(B(1)) === "");

// §6 word table
const words: Array<[string, number, number]> = [
  ["1", 2, 0], ["11E", 9, 1], ["111EE", 35, 2], ["11E1E", 37, 3], ["111E1EE", 139, 5],
  ["1111E1EEE", 535, 10], ["1111EE11E1EEE", 8599, 100], ["111111EEE1EE11EE1EE", 531867, 2431],
];
for (const [w, id, n] of words) {
  expect(`§6 ${w} id`, wordToId(w) === B(id), wordToId(w).toString());
  expect(`§6 ${w} #`, indexOf(w) === B(n), indexOf(w).toString());
  expect(`§6 #${n} -> ${w}`, programAt(B(n)) === w);
  expect(`§6 ${w} matches the calculator's existing program number`, rankRpn(w) === B(n));
}

// §6 ID table: decodes, valid, prev, next, nearest
const ids: Array<[number, string, number | null, number, number]> = [
  [1, "", null, 2, 2], [3, "E", 2, 9, 2], [8, "111", 2, 9, 9], [10, "1E1", 9, 35, 9],
  [40, "1E111", 37, 135, 37], [100, "E11E11", 37, 135, 135], [1000, "EEEE1E111", 597, 2079, 597],
];
for (const [id, dec, prev, next, near] of ids) {
  expect(`§6 ID ${id} decodes`, idToWord(B(id)) === dec);
  expect(`§6 ID ${id} invalid`, !isValidId(B(id)));
  const p = prevValid(B(id));
  expect(`§6 ID ${id} prev`, prev === null ? p === null : p === B(prev), String(p));
  expect(`§6 ID ${id} next`, nextValid(B(id)) === B(next), nextValid(B(id)).toString());
  expect(`§6 ID ${id} nearest`, nearestValid(B(id)) === B(near), nearestValid(B(id)).toString());
}

// §3 first 20 valid IDs
const first20 = [2, 9, 35, 37, 135, 139, 141, 147, 149, 527, 535, 539, 541, 551, 555, 557, 563, 565, 583, 587];
const found: number[] = [];
for (let i = 1; found.length < 20; i += 1) if (isValidId(B(i))) found.push(i);
expect("§3 first 20 valid IDs", JSON.stringify(found) === JSON.stringify(first20), found.join(","));
expect("§3 even K is invalid", !isValidId(B(0b10101)) && !isValidWord("11"));

// §5 shapes
expect("first word K=7", firstWord(7) === "1111EEE" && isValidWord(firstWord(7)));
expect("last word K=7", lastWord(7) === "11E1E1E" && isValidWord(lastWord(7)));

// Cross-check against program_id_ref.py outputs
const fixture = JSON.parse(fs.readFileSync(path.join(__dirname, "fixtures", "program-id-vectors.json"), "utf8")) as {
  small: { valid: Array<[number, number]>; nav: Array<[number, number | null, number, number]> };
  big: Array<{ word: string; id: string; index: string; prev: string; next: string; programAtIndexPlus1: string }>;
};
let validCount = 0;
for (let i = 1; i < 1 << 14; i += 1) if (isValidId(B(i))) validCount += 1;
expect("ref: 197 valid IDs below 2^14", validCount === fixture.small.valid.length && validCount === 197, String(validCount));
for (const [id, n] of fixture.small.valid) {
  const w = idToWord(B(id));
  if (!(isValidWord(w) && indexOf(w) === B(n) && wordToId(programAt(B(n))) === B(id))) expect(`ref valid ${id}`, false);
}
expect("ref: every valid ID < 2^14 has the same # and round-trips", true);
let navBad = 0;
for (const [id, prev, next, near] of fixture.small.nav) {
  const p = prevValid(B(id));
  const ok = (prev === null ? p === null : p === B(prev)) && nextValid(B(id)) === B(next) && nearestValid(B(id)) === B(near);
  if (!ok) {
    navBad += 1;
    if (navBad < 5) console.log("nav mismatch", id, String(p), nextValid(B(id)).toString(), nearestValid(B(id)).toString(), prev, next, near);
  }
}
expect("ref: prev/next/nearest agree for every ID 0..2^13-1", navBad === 0, `${navBad} mismatches`);
for (const row of fixture.big) {
  const K = row.word.length;
  expect(`ref long K=${K} id`, wordToId(row.word) === B(row.id));
  expect(`ref long K=${K} #`, indexOf(row.word) === B(row.index) && rankRpn(row.word) === B(row.index));
  expect(`ref long K=${K} prev`, prevValid(B(row.id)) === B(row.prev));
  expect(`ref long K=${K} next`, nextValid(B(row.id)) === B(row.next));
  expect(`ref long K=${K} #+1`, programAt(B(row.index) + B(1)) === row.programAtIndexPlus1);
  expect(`ref long K=${K} next == #+1`, nextValid(B(row.id)) === wordToId(row.programAtIndexPlus1));
}

// BigInt round trip at the size limit
const longWord = `${"1".repeat(1001)}${"E".repeat(1000)}`;
expect("K=2001 round trip", idToWord(wordToId(longWord)) === longWord && longWord.length === MAX_ID_KEYS);
expect("K=2001 # matches existing rank", indexOf(longWord) === rankRpn(longWord));
expect("unrank agrees", unrankRpn(indexOf(longWord)) === longWord);

// Jump: no silent clamp
const ok9 = jump("9", "id");
expect("jump ID 9", ok9.ok && ok9.word === "11E" && ok9.snappedFrom === null);
const snap = jump("1000", "id");
expect("jump ID 1000 snaps to 597 and says so", snap.ok && snap.id === B(597) && snap.snappedFrom === B(1000) && snap.decodedFrom === "EEEE1E111");
const tie = jump("1", "id");
expect("jump ID 1 -> 2", tie.ok && tie.id === B(2));
const p1 = jump("#1", "program");
expect("jump #1", p1.ok && p1.word === "11E" && p1.id === B(9));
expect("jump program 2431", (() => { const r = jump("2431", "program"); return r.ok && r.word === "111111EEE1EE11EE1EE"; })());
for (const [text, mode] of [["", "id"], ["-3", "id"], ["0", "id"], ["abc", "id"], ["#9", "id"], ["1.5", "program"], ["-1", "program"], ["# 1", "program"]] as const) {
  const r = jump(text, mode);
  expect(`jump error for ${JSON.stringify(text)} (${mode})`, !r.ok, r.ok ? r.word : "");
}
const huge = jump(`1${"0".repeat(700)}`, "program");
expect("jump: a program number past the key limit is an error, not clamped", !huge.ok);
const hugeId = jump((BigInt(1) << BigInt(2100)).toString(), "id");
expect("jump: an ID past the key limit is an error, not clamped", !hugeId.ok);

// ---- One bit convention everywhere: E = 1, the 1 key = 0 (Ben's flipped encoding). ----
function allWords(maxK: number, alphabet: readonly string[]): string[] {
  const out: string[] = [];
  const walk = (prefix: string, depth: number) => {
    if (depth === 1 && prefix.length > 0) out.push(prefix);
    if (prefix.length >= maxK) return;
    for (const key of alphabet) {
      if (key === "E") { if (depth >= 2) walk(prefix + key, depth - 1); }
      else walk(prefix + key, depth + 1);
    }
  };
  walk("", 0);
  return out;
}
const words13 = allWords(13, ["1", "E"]);
expect("there are 197 programs up to 13 keys", words13.length === 197, String(words13.length));
let pressMismatch = "";
for (const w of words13) {
  const bits = encodePresses(w.split(""));
  if (bits !== idBits(w).slice(1) || bits !== wordToBits(w) || bitsToWord(bits) !== w) { pressMismatch = w; break; }
}
expect("press bits are the ID bits without the leading 1, for every program up to 13 keys", pressMismatch === "", pressMismatch);
expect("press line for 11E is 001", pressPreviewForNode(nodeFromRpn(["1", "1", "E"]))?.full === "001");
expect("press line for E(x, 1) is x01", pressPreviewForNode(nodeFromRpn(["x", "1", "E"]))?.full === "x01");

const parse = (text: string): ParsedProgram | string => { try { return parseProgramInput(text); } catch (err) { return err instanceof Error ? err.message : String(err); } };
const wordOf = (r: ParsedProgram | string) => (typeof r === "string" ? null : r.kind === "word" ? r.word : null);
const isOld = (r: ParsedProgram | string) => typeof r !== "string" && r.kind === "word" && r.oldBits !== null;

// Load box, current convention.
let newMismatch = "";
for (const w of words13) {
  const r = parse(wordToBits(w));
  if (wordOf(r) !== w || isOld(r) || (typeof r !== "string" && loadNotice(r) !== null)) { newMismatch = w; break; }
}
expect("Load: the bits of every program up to 13 keys load that program, with no note", newMismatch === "", newMismatch);
expect("Load: 001 is 11E", wordOf(parse("001")) === "11E");
expect("Load: 001 is program #1", rankRpn(wordOf(parse("001")) ?? "") === B(1));
expect("Load: 0 is the word 1", wordOf(parse("0")) === "1");
expect("Load: 1 alone is the word 1", wordOf(parse("1")) === "1");
expect("Load: x01 is E(x, 1)", wordOf(parse("x01")) === "x1E");
expect("Load: xy1 is E(x, y)", wordOf(parse("xy1")) === "xyE");
{
  const r = parse("100");
  expect("Load: 100 rotates to 11E with a note in bits", wordOf(r) === "11E" && typeof r !== "string" && loadNotice(r) === "Rotated 100 to 001.", JSON.stringify(r));
  const w = parse("E11");
  expect("Load: word E11 still rotates with a word note", typeof w !== "string" && loadNotice(w) === "Rotated E11 to 11E.");
}
{
  const r = parse("110");
  expect("Load: plain 110 is an error, not 11E", typeof r === "string", JSON.stringify(r));
  expect("Load: that error names the old: prefix", typeof r === "string" && r.includes(OLD_BITS_PREFIX), String(r));
}

// Load box, old convention (0 = EML), opt-in with old: only.
{
  const r = parse("old:110");
  expect("Load old: old:110 is 11E", wordOf(r) === "11E");
  expect("Load old: note text", typeof r !== "string" && loadNotice(r) === "Read in the old convention (0 = EML), shown here as 001.", typeof r !== "string" ? String(loadNotice(r)) : r);
  expect("Load old: prefix is case-insensitive and allows spaces", wordOf(parse("OLD: 1 1 0")) === "11E" && wordOf(parse("  Old:110")) === "11E");
  const v = parse("old:x10");
  expect("Load old: old:x10 is E(x, 1), shown as x01", wordOf(v) === "x1E" && typeof v !== "string" && loadNotice(v) === "Read in the old convention (0 = EML), shown here as x01.");
  const t = parse("old:011");
  expect("Load old: old:011 notes the conversion and the rotation", wordOf(t) === "11E" && typeof t !== "string" && loadNotice(t) === "Read in the old convention (0 = EML), shown here as 100. Rotated 100 to 001.", typeof t !== "string" ? String(loadNotice(t)) : t);
  for (const bad of ["old:", "old:11E", "old:#1", "old:12", "old:111"]) {
    expect(`Load old: ${bad} is an error`, typeof parse(bad) === "string");
  }
}
let oldMismatch = "";
for (const w of words13) {
  const oldBits = w.replace(/E/g, "0");
  const r = parse(`${OLD_BITS_PREFIX}${oldBits}`);
  if (wordOf(r) !== w || !isOld(r)) { oldMismatch = w; break; }
}
expect("Load old: every program up to 13 keys round-trips through old:", oldMismatch === "", oldMismatch);

// The old path can't be triggered by accident.
let accident = "";
for (const w of [...words13, ...allWords(9, ["1", "x", "y", "E"])]) {
  if (w.length === 1) continue; // 1, x and y are the same in both conventions
  const oldBits = w.replace(/E/g, "0");
  const r = parse(oldBits);
  if (typeof r !== "string") { accident = `${oldBits} -> ${JSON.stringify(r)}`; break; }
}
expect("no unprefixed old-convention string (up to 13 keys, and with x/y up to 9) loads anything", accident === "", accident);
for (const one of ["1", "x", "y"]) expect(`single key ${one} means the same in both conventions`, wordOf(parse(one)) === wordOf(parse(`old:${one}`)) && wordOf(parse(one)) === one);
let seed = 20261120;
const rand = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed; };
const chars = "01xyE #:";
let fuzzOld = "";
for (let i = 0; i < 20000; i += 1) {
  let t = "";
  const n = 1 + (rand() % 12);
  for (let j = 0; j < n; j += 1) t += chars[rand() % chars.length];
  if (t.trim().toLowerCase().startsWith(OLD_BITS_PREFIX)) continue;
  if (isOld(parse(t))) { fuzzOld = t; break; }
}
expect("fuzz: 20000 random inputs without the prefix never take the old path", fuzzOld === "", fuzzOld);
for (const near of ["old 110", "old110", "o:110", "legacy:110", "1old:10", "#old:110", "0=EML 110"]) {
  const r = parse(near);
  expect(`near-miss ${JSON.stringify(near)} does not take the old path`, !isOld(r), JSON.stringify(r));
}

console.log(`program-id-check: ${passed} passed, ${failed} failed`);
if (failed) process.exit(1);
