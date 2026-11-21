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
import { rankRpn, unrankRpn } from "../lib/eml/programIndex";

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

console.log(`program-id-check: ${passed} passed, ${failed} failed`);
if (failed) process.exit(1);
