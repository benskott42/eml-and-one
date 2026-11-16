/**
 * Count-to-n checks run at the end of eml:check.
 * The per-gate rule has no word, n, or gate exception.
 */
import { readFileSync, readdirSync, statSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import Decimal from "decimal.js";
import { checkCutTraces, exactTraceOf, floatTraceOf, onNegativeCutF, onNegativeCutZ, ruleSelfTest, setCutTrace } from "../lib/eml/cut";
import { choose, wordsForCutRule } from "../lib/eml/countModel";
import { linesFor, ln0Use } from "../lib/eml/countTable";
import { BLOCK, blockSpans, countWord, countWordLength } from "../lib/eml/countWord";
import { floatCertified, targetText } from "../lib/eml/countStatus";
import { exactParts, exactReport, formatExact, type ExactReport } from "../lib/eml/exact";
import { evaluateReport, nodeFromRpn, type EvalReport, type Node } from "../lib/eml/node";
import { samePrincipal } from "../lib/eml/principalBranch";
import { packCircuit, unpackCircuit } from "../lib/eml/wire";
import rows from "../lib/eml/integer-table.json";
import known from "../lib/eml/best-known.json";

const failures: string[] = [];

function fail(message: string): void {
  failures.push(message);
  if (failures.length <= 40) console.log(`FAIL ${message}`);
}

function stackOk(word: string): boolean {
  let depth = 0;
  for (const ch of word) {
    if (ch === "1") depth += 1;
    else {
      if (depth < 2) return false;
      depth -= 1;
    }
  }
  return depth === 1;
}

function closeTo(report: ExactReport, n: number): boolean {
  const digits = report.digits ?? 120;
  const tol = new Decimal(10).pow(-(digits - 10));
  return report.value.re.sub(n).abs().lte(tol) && report.value.im.abs().lte(tol);
}

function resolves(n: number, mode: "ln0" | "strict"): boolean {
  const family = countWord(n);
  const programs = known.programs as Record<string, string>;
  const lines = linesFor(n)
    .filter((line) => (mode === "strict" ? ln0Use(line) === "no" || ln0Use(line) === "both" : true))
    .sort((a, b) => a.k - b.k);
  for (const line of lines) {
    if (line.k > family.length) continue;
    const keys = mode === "strict" ? [`${n}-strict`, `${n}`] : [`${n}`, `${n}-strict`];
    const word = [...keys.map((key) => programs[key]), family].find((item) => item && item.length === line.k);
    if (word) return true;
  }
  return false;
}

type Row = (typeof rows)[number];

function expectStatus(row: Row, mode: "ln0" | "strict", label: string): void {
  if (row.n === 1) {
    if (label !== "the 1 key itself · K 1") fail(`n = 1 pill is ${JSON.stringify(label)}`);
    return;
  }
  const minimal = mode === "ln0" ? row.minimal : row.minimalNoLn0;
  // The table's free-text status describes the ln 0 word. The ln-0-free line is a different record.
  if (mode === "ln0" && row.status.startsWith("shortest known (")) {
    if (!label.startsWith(row.status)) fail(`${row.n}/${mode} status ${JSON.stringify(label)}`);
    if (!minimal && !label.includes("not proven minimal")) fail(`${row.n}/${mode} dropped the not-proven clause`);
    return;
  }
  if (minimal) {
    if (!label.startsWith("proven minimal")) fail(`${row.n}/${mode} should be proven, got ${JSON.stringify(label)}`);
    return;
  }
  if (!label.startsWith("shortest known") || !label.includes("not proven minimal")) {
    fail(`${row.n}/${mode} status ${JSON.stringify(label)}`);
  }
}

for (let n = -50; n <= 50; n += 1) {
  const word = countWord(n);
  const length = countWordLength(n);
  const formula = n === 1 ? 1 : n === 0 ? 7 : n >= 2 ? 10 * n - 1 : 10 * -n + 7;
  if (!/^[1E]+$/.test(word)) fail(`generator alphabet ${n}`);
  if (word.length !== length || length !== formula) fail(`generator length ${n}: ${word.length} ${length} ${formula}`);
  if (!stackOk(word)) fail(`generator stack ${n}`);
  for (const [from, to] of blockSpans(n)) {
    if (word.slice(from, to) !== BLOCK) fail(`generator block ${n} ${from}`);
  }
}
for (const bad of [1.5, Number.NaN, Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY]) {
  for (const fn of [countWord, countWordLength]) {
    let threw = false;
    try {
      fn(bad);
    } catch {
      threw = true;
    }
    if (!threw) fail(`non-integer ${bad} was accepted`);
  }
}

const expectedCuts: Record<string, number> = {
  "0/ln0": 0,
  "1/ln0": 0,
  "2/ln0": 0,
  "3/ln0": 0,
  "-1/ln0": 0,
  "4/ln0": 2,
  "7/ln0": 8,
  "50/ln0": 94,
  "-50/ln0": 96,
  "-2/ln0": 1,
  "-3/ln0": 1,
  "-4/ln0": 3,
  "-5/ln0": 5,
  "-6/ln0": 7,
  "-7/ln0": 9,
  "-8/ln0": 3,
  "-8/strict": 2,
  "-9/ln0": 3,
};

type Stored = { exact: ExactReport; floated: EvalReport; node: Node };
const byWord = new Map<string, Stored>();
const case2: string[] = [];
let ruleViolations = 0;

function examine(word: string, label: string): Stored {
  const hit = byWord.get(word);
  if (hit) return hit;
  const node = nodeFromRpn(word.split(""));
  const floated = evaluateReport(node, {}, { maxNodes: 80_000 });
  const exact = exactReport(node, {}, { maxNodes: 80_000 });
  const es = (word.match(/E/g) ?? []).length;
  let check;
  try {
    check = checkCutTraces(floatTraceOf(node), exactTraceOf(node));
  } catch (err) {
    ruleViolations += 1;
    fail(`${label}: ${err instanceof Error ? err.message : "trace failed"}`);
    const stored = { exact, floated, node };
    byWord.set(word, stored);
    return stored;
  }
  if (check.floatHits !== undefined && floatTraceOf(node).length !== es) {
    ruleViolations += 1;
    fail(`${label}: trace length ${floatTraceOf(node).length} vs ${es} E gates`);
  }
  if (!check.ok) {
    ruleViolations += check.violations.length;
    fail(`${label}: ${check.violations.join("; ")}`);
  }
  if (exact.cutHits !== check.exactHits) fail(`${label}: exact cut ${exact.cutHits} vs trace ${check.exactHits}`);
  for (const gate of check.case2) case2.push(`${word} K${word.length} ${gate.gate} ${gate.floatIm.toExponential(2)}`);
  const stored = { exact, floated, node };
  byWord.set(word, stored);
  return stored;
}

setCutTrace(true);
try {
  let direct = 0;
  for (const mode of ["ln0", "strict"] as const) {
    for (let n = -50; n <= 50; n += 1) {
      const choice = choose(n, mode);
      const stored = examine(choice.word, `${n}/${mode}`);
      direct += 1;
      const { exact, floated } = stored;
      if (exact.unverified || exact.singular || !closeTo(exact, n)) {
        fail(`${n}/${mode} exact ${exact.singular ?? ""} unverified=${exact.unverified === true} ${formatExact(exact.value)}`);
      }
      if (formatExact(exact.value) !== targetText(n)) fail(`${n}/${mode} format ${formatExact(exact.value)}`);
      if (mode === "strict" && exact.touchedLn0) fail(`${n}/strict touched ln 0`);
      if (choice.source === "family" && exact.touchedLn0) fail(`${n}/${mode} construction touched ln 0`);
      const tol = 1e-9 * Math.max(1, Math.abs(n));
      if (floated.underflowed || Math.abs(floated.value.re - n) > tol || Math.abs(floated.value.im) > tol) {
        fail(`${n}/${mode} float ${floated.value.re} ${floated.value.im} under=${floated.underflowed}`);
      }
      const want = expectedCuts[`${n}/${mode}`];
      if (want !== undefined && exact.cutHits !== want) fail(`${n}/${mode} cutHits ${exact.cutHits} expected ${want}`);
      if ((direct % 40) === 0) console.log(`count-check progress ${direct}/202`);
    }
  }
  for (const [word, label] of wordsForCutRule()) examine(word, label);
} finally {
  setCutTrace(false);
}

const huge = evaluateReport(nodeFromRpn(countWord(735).split("")));
const hugeExact = { text: "", re: 735, im: 0, singular: null, touchedLn0: false, underflowedExact: false, unverified: false };
if (!huge.underflowed || floatCertified({
  text: "",
  re: huge.value.re,
  im: huge.value.im,
  underflowed: huge.underflowed,
  overflowed: huge.overflowed,
  singular: huge.singular,
  touchedLn0: huge.touchedLn0,
}, hugeExact)) {
  fail(`countWord(735) underflowed=${huge.underflowed} certified=${floatCertified({
    text: "",
    re: huge.value.re,
    im: huge.value.im,
    underflowed: huge.underflowed,
    overflowed: huge.overflowed,
    singular: huge.singular,
    touchedLn0: huge.touchedLn0,
  }, hugeExact)}`);
}

let d3 = 0;
for (const mode of ["ln0", "strict"] as const) {
  for (let n = -50; n <= 50; n += 1) {
    if (n === 1) continue;
    d3 += 1;
    const choice = choose(n, mode);
    const has = choice.table !== null;
    if (has !== resolves(n, mode)) fail(`D3 ${n}/${mode} table=${has} resolves=${resolves(n, mode)}`);
  }
}

function fixed(n: number, mode: "ln0" | "strict", k: number, status: string): void {
  const choice = choose(n, mode);
  if (choice.K !== k) fail(`fixed K ${n}/${mode} is ${choice.K}, expected ${k}`);
  if (choice.table?.status !== status) fail(`fixed status ${n}/${mode} ${JSON.stringify(choice.table?.status)}`);
}
fixed(-1, "ln0", 15, "proven minimal (uses ln 0)");
fixed(-1, "strict", 17, "proven minimal without ln 0");
fixed(-2, "ln0", 25, "shortest known (depends on ln 0; unresolved tower trees remain), not proven minimal");
fixed(-2, "strict", 27, "shortest known without ln 0, not proven minimal");
if (!choose(-2, "strict").table?.note.includes("minimal conditional on Schanuel's conjecture")) fail("−2 strict is missing the Schanuel footnote");
fixed(-3, "ln0", 35, "shortest known, not proven minimal");
fixed(-3, "strict", 35, "shortest known, not proven minimal");
for (const [n, k] of [[-4, 45], [-5, 55], [-6, 65], [-7, 75], [-9, 79]] as const) {
  for (const mode of ["ln0", "strict"] as const) {
    fixed(n, mode, k, "shortest known, not proven minimal");
    if (choose(n, mode).table?.ln0) fail(`${n}/${mode} should not use ln 0`);
  }
}
fixed(-8, "ln0", 77, "shortest known, not proven minimal");
fixed(-8, "strict", 79, "shortest known, not proven minimal");
if (!choose(-8, "ln0").table?.ln0 || choose(-8, "strict").table?.ln0) fail("−8 ln 0 flags");
fixed(3, "ln0", 29, "shortest known, not proven minimal (ties Kaseorg's code-golf answer)");
fixed(3, "strict", 29, "shortest known, not proven minimal (ties Kaseorg's code-golf answer)");

for (const row of rows) {
  for (const mode of ["ln0", "strict"] as const) {
    const choice = choose(row.n, mode);
    const word = mode === "ln0" ? row.word : row.wordNoLn0;
    const presses = mode === "ln0" ? row.presses : row.pressesNoLn0;
    const uses = mode === "ln0" ? row.usesLn0 : false;
    if (choice.word !== word || choice.K !== presses) fail(`table row ${row.n}/${mode} ${choice.K} vs ${presses}`);
    const stored = byWord.get(choice.word);
    if (!stored) fail(`table row ${row.n}/${mode} was not evaluated`);
    else if (stored.exact.touchedLn0 !== uses) fail(`table row ${row.n}/${mode} touchedLn0 ${stored.exact.touchedLn0} vs ${uses}`);
    expectStatus(row, mode, choice.table?.status ?? "");
  }
}

const proved = new Set<string>();
for (const mode of ["ln0", "strict"] as const) {
  for (let n = -50; n <= 50; n += 1) {
    if (n === 1) continue;
    const status = choose(n, mode).table?.status ?? "";
    if (status.startsWith("proven minimal")) proved.add(`${n}/${mode}`);
  }
}
const provedWant = ["0/ln0", "0/strict", "-1/ln0", "-1/strict", "2/ln0", "2/strict"];
if ([...proved].sort().join() !== [...provedWant].sort().join()) fail(`proved set ${[...proved].join(" ")}`);

const points: Array<[number, number]> = [
  [-2, 0],
  [-2, -0],
  [-0, 0],
  [Number.NEGATIVE_INFINITY, 0],
  [Number.NaN, 0],
  [-2, 1e-300],
  [-2, -1e-300],
  [2, 0],
];
for (const [re, im] of points) {
  const left = onNegativeCutF(re, im);
  const right = onNegativeCutZ(exactParts(re, im));
  if (left !== right) fail(`cut edge (${re}, ${im}) float ${left} exact ${right}`);
}
for (const row of ruleSelfTest()) {
  if (row.got !== row.want) fail(`rule self-test ${row.name} got ${row.got}`);
}

const principal = new Map<string, boolean>();
for (const mode of ["ln0", "strict"] as const) {
  for (let n = -50; n <= 50; n += 1) {
    const choice = choose(n, mode);
    const key = `${n}:${choice.K}`;
    if (!principal.has(key)) principal.set(key, samePrincipal(choice.word));
  }
}
let principalOk = 0;
for (const [key, ok] of principal) {
  if (!ok) fail(`principal ${key}`);
  else principalOk += 1;
}

function filesUnder(dir: string): string[] {
  const out: string[] = [];
  for (const name of readdirSync(dir)) {
    const path = join(dir, name);
    if (statSync(path).isDirectory()) out.push(...filesUnder(path));
    else out.push(path);
  }
  return out;
}
const banned = /mathbot|compscibot|makerbot|reviewbot|brainstorm|upper bound: 10|shortest in this family|not proven shortest|not shown to be exact/;
for (const path of filesUnder(join(dirname(fileURLToPath(import.meta.url)), "../app/count"))) {
  const text = readFileSync(path, "utf8");
  if (banned.test(text)) fail(`copy ${path}`);
}

type WorkerReply = { type?: string; text?: string; cutHits?: number; message?: string };

async function finish(): Promise<void> {
  const inbox: WorkerReply[] = [];
  const fakeSelf = {
    postMessage(data: WorkerReply) {
      inbox.push(data);
    },
    onmessage: null as ((event: { data: { request: number; tokens: unknown; root: number; env: Record<string, never> } }) => void) | null,
  };
  (globalThis as { self?: typeof fakeSelf }).self = fakeSelf;
  await import("../lib/eml/exact.worker");

  let workerCases = 0;
  for (const mode of ["ln0", "strict"] as const) {
    for (let n = -50; n <= 50; n += 1) {
      const choice = choose(n, mode);
      const stored = byWord.get(choice.word);
      if (!stored) {
        fail(`worker missing ${n}/${mode}`);
        continue;
      }
      const packed = packCircuit(stored.node);
      const again = exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
      if (formatExact(again.value) !== formatExact(stored.exact.value) || again.cutHits !== stored.exact.cutHits) {
        fail(`worker path ${n}/${mode} ${formatExact(again.value)} cuts ${again.cutHits}`);
      }
      inbox.length = 0;
      fakeSelf.onmessage?.({ data: { request: workerCases + 1, tokens: packed.tokens, root: packed.root, env: {} } });
      const reply = inbox[0];
      if (!reply || reply.type !== "done" || reply.cutHits !== stored.exact.cutHits) {
        fail(`worker message ${n}/${mode} ${JSON.stringify(reply)}`);
      }
      workerCases += 1;
    }
  }

  console.log("count-check: 202 exact cases (direct and worker path)");
  console.log(`D3 table check: ${d3} mode rows`);
  console.log("new-word cases: −4 −5 −6 −7 −8 −9 and −8 without ln 0");
  console.log("cut-count table: 0, 1, 2, 3, −1 → 0; 4 → 2; 7 → 8; 50 → 94; −50 → 96; −2 K25 → 1; −3 → 1; −4 → 3; −5 → 5; −6 → 7; −7 → 9; −8 K77 → 3; −8 K79 → 2; −9 → 3");
  console.log(`per-gate cut rule: ${ruleViolations} violations`);
  if (case2.length) console.log(`case-2 gates:\n${case2.join("\n")}`);
  else console.log("case-2 gates: none");
  console.log(`principal set (${principalOk}/${principal.size})`);
  console.log(`underflow case: countWord(735) underflowed ${huge.underflowed}, floatCertified false`);
  console.log(`worker messages: ${workerCases}`);

  if (failures.length) {
    console.log(`${failures.length} count-check failures`);
    process.exit(1);
  }
  console.log("count-check passed");
}

void finish();
