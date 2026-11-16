/**
 * Count-to-n checks run at the end of eml:check.
 * The per-gate rule has no word, n, or gate exception.
 */
import { readFileSync, readdirSync, statSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import Decimal from "decimal.js";
import { checkCutTraces, exactTraceOf, floatTraceOf, onNegativeCutF, onNegativeCutZ, ruleSelfTest, setCutTrace } from "../lib/eml/cut";
import { choose, pagePill, wordsForCutRule } from "../lib/eml/countModel";
import { linesFor, ln0Use } from "../lib/eml/countTable";
import { noteBeside, recordLine } from "../lib/eml/recordLabel";
import { BLOCK, blockSpans, countWord, countWordLength } from "../lib/eml/countWord";
import { PROVEN_MINIMAL, provedMinimal } from "../lib/eml/statusLabels";
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

const USES_LN0 = `${PROVEN_MINIMAL} (uses ln 0)`;
const WITHOUT_LN0 = `${PROVEN_MINIMAL} without ln 0`;
const CONSTRUCTION = "a construction, not a search record";
const ONE_PILL = "the 1 key itself · K 1";

function expectStatus(row: Row, mode: "ln0" | "strict", label: string): void {
  if (row.n === 1) {
    if (label !== ONE_PILL) fail(`n = 1 pill is ${JSON.stringify(label)}`);
    if (provedMinimal(row.n, mode)) fail("n = 1 is shown as proved");
    return;
  }
  const line = linesFor(row.n).find((item) => item.k === (mode === "ln0" ? row.presses : row.pressesNoLn0));
  if (!line) {
    if (label !== CONSTRUCTION) fail(`${row.n}/${mode} has no row but shows ${JSON.stringify(label)}`);
    return;
  }
  const provedLabel = line.label === PROVEN_MINIMAL || line.label === USES_LN0 || line.label === WITHOUT_LN0;
  let want = line.label;
  if (!provedLabel) {
    const unproved = `not ${PROVEN_MINIMAL}`;
    if (line.note.toLowerCase().includes(unproved) && !line.label.toLowerCase().includes("not proven")) want += `, ${unproved}`;
    const tie = /ties [^;]+/.exec(line.note);
    if (tie && !want.includes(tie[0])) want += ` (${tie[0]})`;
  }
  if (label !== want) fail(`${row.n}/${mode} status ${JSON.stringify(label)} want ${JSON.stringify(want)}`);
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
  let threw = false;
  try {
    countWord(bad);
  } catch {
    threw = true;
  }
  if (!threw) fail(`non-integer ${bad} was accepted by countWord`);
  try {
    const length = countWordLength(bad);
    if (typeof length !== "number") fail(`countWordLength ${bad} returned ${length}`);
  } catch {
    fail(`countWordLength threw on ${bad}`);
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
    d3 += 1;
    const choice = choose(n, mode);
    const has = choice.table !== null;
    if (has !== resolves(n, mode)) fail(`D3 ${n}/${mode} table=${has} resolves=${resolves(n, mode)}`);
  }
}

function fixed(n: number, mode: "ln0" | "strict", k: number, status: string): void {
  const choice = choose(n, mode);
  if (choice.K !== k) fail(`fixed K ${n}/${mode} is ${choice.K}, expected ${k}`);
  const shown = pagePill(choice);
  if (shown !== status) fail(`fixed status ${n}/${mode} ${JSON.stringify(shown)} want ${JSON.stringify(status)}`);
}
fixed(-1, "ln0", 15, USES_LN0);
fixed(-1, "strict", 17, WITHOUT_LN0);
fixed(0, "ln0", 7, PROVEN_MINIMAL);
fixed(0, "strict", 7, PROVEN_MINIMAL);
fixed(1, "ln0", 1, ONE_PILL);
fixed(1, "strict", 1, ONE_PILL);
fixed(2, "ln0", 19, PROVEN_MINIMAL);
fixed(2, "strict", 19, PROVEN_MINIMAL);
fixed(-2, "ln0", 25, `shortest known (depends on ln 0; unresolved tower trees remain), not ${PROVEN_MINIMAL}`);
fixed(-2, "strict", 27, `shortest known without ln 0, not ${PROVEN_MINIMAL}`);
fixed(3, "ln0", 29, `shortest known, not ${PROVEN_MINIMAL} (ties Kaseorg's code-golf answer)`);
fixed(40, "ln0", 399, CONSTRUCTION);
fixed(-20, "strict", 207, CONSTRUCTION);
fixed(26, "ln0", 259, CONSTRUCTION);
fixed(-50, "ln0", 507, CONSTRUCTION);
if (choose(40, "ln0").table || choose(-20, "ln0").table) fail("40 and −20 are table rows");
if (choose(0, "ln0").familyLabel !== "ln(1) via the ln template 11xE1EE: 7 presses") fail(`family 0 ${choose(0, "ln0").familyLabel}`);
if (choose(1, "ln0").familyLabel !== "the 1 key: 1 press") fail(`family 1 ${choose(1, "ln0").familyLabel}`);
if (choose(1, "ln0").familyLabel.includes("counting construction")) fail("the 1 key is called a counting construction");
if (choose(4, "ln0").familyLabel !== "counting construction: K = 10n − 1 (gives exactly n on both cuts, without ln 0)") fail(`family 4 ${choose(4, "ln0").familyLabel}`);
if (choose(-1, "strict").familyLabel !== "counting construction: K = 10m + 7, m = −n (gives exactly n on both cuts, without ln 0)") fail(`family −1 ${choose(-1, "strict").familyLabel}`);
const oneRow = rows.find((row) => row.n === 1);
if (oneRow?.status !== "proven-minimal" || oneRow.minimal !== true || oneRow.minimalNoLn0 !== true) fail("n = 1 data row");
if (choose(1, "ln0").table?.status !== ONE_PILL || choose(1, "strict").table?.status !== ONE_PILL) fail("n = 1 table status");
const oneLine = known.minimality.find((row) => row.value === "1" && row.k === 1);
if (!oneLine) fail("missing 1, K 1 minimality line");
else if (recordLine(oneLine).includes(PROVEN_MINIMAL)) fail(`1 is labelled ${recordLine(oneLine)}`);
if (!choose(-2, "strict").table?.note.includes("minimal conditional on Schanuel's conjecture")) fail("−2 strict is missing the Schanuel footnote");
fixed(-3, "ln0", 35, `shortest known, not ${PROVEN_MINIMAL}`);
fixed(-3, "strict", 35, `shortest known, not ${PROVEN_MINIMAL}`);
for (const [n, k] of [[-4, 45], [-5, 55], [-6, 65], [-7, 75], [-9, 79]] as const) {
  for (const mode of ["ln0", "strict"] as const) {
    fixed(n, mode, k, `shortest known, not ${PROVEN_MINIMAL}`);
    if (choose(n, mode).table?.ln0) fail(`${n}/${mode} should not use ln 0`);
  }
}
fixed(-8, "ln0", 77, `shortest known, not ${PROVEN_MINIMAL}`);
fixed(-8, "strict", 79, `shortest known, not ${PROVEN_MINIMAL}`);
if (!choose(-8, "ln0").table?.ln0 || choose(-8, "strict").table?.ln0) fail("−8 ln 0 flags");
fixed(3, "strict", 29, `shortest known, not ${PROVEN_MINIMAL} (ties Kaseorg's code-golf answer)`);

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
    expectStatus(row, mode, pagePill(choice));
  }
}

const provedLabels = new Set([PROVEN_MINIMAL, USES_LN0, WITHOUT_LN0]);
const proved = new Set<string>();
for (const mode of ["ln0", "strict"] as const) {
  for (let n = -50; n <= 50; n += 1) {
    const choice = choose(n, mode);
    const flag = provedMinimal(n, mode);
    const pill = pagePill(choice);
    if (n !== 1 && choice.table === null && pill !== CONSTRUCTION) fail(`construction pill ${n}/${mode} ${pill}`);
    if (provedLabels.has(pill)) proved.add(`${n}/${mode}`);
    if (provedLabels.has(pill) !== flag) fail(`pill follows the flag ${n}/${mode} ${pill}`);
    const basis = noteBeside(choice.table?.note ?? "", pill);
    if (n === 1 && basis !== "") fail(`n = 1 basis ${basis}`);
    if (flag && (basis.includes(PROVEN_MINIMAL) || basis.toLowerCase().includes("shortest known"))) fail(`proved basis ${n}/${mode} ${basis}`);
  }
  const zeroPill = pagePill(choose(0, mode));
  const zero = noteBeside(choose(0, mode).table?.note ?? "", zeroPill);
  if (zeroPill !== PROVEN_MINIMAL || !zero.includes("K ≤ 5") || !zero.includes("with or without ln 0")) fail(`basis 0/${mode} ${zeroPill} ${zero}`);
  const negChoice = choose(-1, mode);
  const negPill = pagePill(negChoice);
  const neg = noteBeside(negChoice.table?.note ?? "", negPill);
  if (mode === "ln0" && (negPill !== USES_LN0 || !neg.includes("K ≤ 13"))) fail(`basis −1/${mode} ${negPill} ${neg}`);
  if (mode === "strict" && (negPill !== WITHOUT_LN0 || !neg.includes("the only shorter −1 is the K 15 word, and that word uses ln 0"))) fail(`basis −1/${mode} ${negPill} ${neg}`);
  const two = noteBeside(choose(2, mode).table?.note ?? "", pagePill(choose(2, mode)));
  if (!two.includes("2056")) fail(`basis 2/${mode} ${two}`);
}
const provedWant = ["0/ln0", "0/strict", "-1/ln0", "-1/strict", "2/ln0", "2/strict"];
if ([...proved].sort().join() !== [...provedWant].sort().join()) fail(`proved set ${[...proved].join(" ")}`);

function minimalityLine(value: string, k: number) {
  return known.minimality.find((row) => row.value === value && row.k === k);
}
const ipi = recordLine(minimalityLine("+iπ on this cut (−iπ on the principal log)", 21) ?? { value: "", k: 0, label: "", note: "" });
const eightCaveat = recordLine(minimalityLine("−8", 77) ?? { value: "", k: 0, label: "", note: "" });
const half = recordLine(minimalityLine("1/2", 29) ?? { value: "", k: 0, label: "", note: "" });
const schanuel = recordLine(minimalityLine("−2", 27) ?? { value: "", k: 0, label: "", note: "" });
if (!ipi.includes("unresolved tower trees remain")) fail(`+iπ caveat ${ipi}`);
if (!eightCaveat.includes("depends on ln 0")) fail(`−8 caveat ${eightCaveat}`);
if (!half.includes("depends on ln 0")) fail(`1/2 caveat ${half}`);
if (!schanuel.includes("Schanuel")) fail(`−2 K 27 caveat ${schanuel}`);

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
const repo = join(dirname(fileURLToPath(import.meta.url)), "..");
for (const path of filesUnder(join(repo, "app/count"))) {
  if (banned.test(readFileSync(path, "utf8"))) fail(`copy ${path}`);
}
const exts = new Set([".ts", ".tsx", ".mjs", ".js", ".css"]);
const quoted = `"${PROVEN_MINIMAL}"`;
const retired = [["proved", "minimal"].join(" "), ["shortest", "possible"].join(" ")];
const copies: string[] = [];
let quotedCount = 0;
for (const dir of ["app", "components", "lib", "scripts"]) {
  for (const path of filesUnder(join(repo, dir))) {
    const ext = path.slice(path.lastIndexOf("."));
    if (!exts.has(ext)) continue;
    const text = readFileSync(path, "utf8");
    quotedCount += text.split(quoted).length - 1;
    const countFeature = /\/(app\/count|app\/counting|statusLabels|recordLabel|countTable|countWord|countStatus|count-check|count-e2e)/.test(path);
    if (!countFeature) continue;
    for (const phrase of retired) {
      if (text.includes(phrase)) copies.push(`${path} contains ${phrase}`);
    }
    if (path.endsWith("/statusLabels.ts") || path.endsWith("\\statusLabels.ts")) continue;
    if (text.includes(quoted)) copies.push(`${path} contains ${quoted}`);
  }
}
if (quotedCount !== 1) fail(`the pill literal is defined ${quotedCount} times`);
if (copies.length) fail(`pill text is copied: ${copies.join("; ")}`);

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
