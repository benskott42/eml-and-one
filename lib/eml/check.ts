import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { branchChecks, runPropertyChecks } from "./check-properties";
import path from "node:path";
import { c, casinh, cdiv, cexp, close, clog, cmul, csin, ctan, eml } from "./complex";
import { applyModeSwitch, commitHistory, drainQueue, exactScreen, finiteLossMessage, modeRequest, underflowDisclosure, undoHistory } from "./history";
import type { Decimal } from "decimal.js";
import { beyondFloatBound, exactClose, exactEvaluate, exactParts, exactReport, exactToFloat, exactUnderflowsFloat, exactValueAt, formatExact } from "./exact";
import { captionName, formatC, recognize } from "./format";
import { ballVerdict, enclose } from "./enclose";
import { acceptsConstantProgram, acceptsConstantValue, functionFingerprint, ln0Dependence, searchConstants, searchConstantsMerged } from "./golf";
import {
  applyBinaryNode,
  applyUnaryNode,
  bindInput,
  constantNode,
  integerNode,
  literalNode,
  seriesShortcutNote,
  X,
  Y,
  tAdd,
  tArcsin,
  tArsinh,
  tExp,
  tHalf,
  tI,
  tMul,
  tSub,
  tTwo,
  unaryNode,
} from "./library";
import { domainAdd, domainSub, knownValue, naiveSub, rangeOf, rotSubCircuit } from "./lowering";
import {
  type Node,
  E,
  EmlError,
  ONE,
  SINGULAR_INDET,
  SINGULAR_LN0,
  SINGULAR_POLE,
  SINGULAR_PRECISION,
  SINGULAR_RANGE,
  SINGULAR_TRIG,
  V,
  circuitStats,
  describe,
  evaluate,
  evaluateReport,
  expUnderflows,
  input,
  isolateCircuit,
  provenInteger,
  isPure,
  nodeFromRpn,
  rpnTokens,
  substitute,
} from "./node";
import {
  approximateIndexBits,
  catalan,
  isProgram,
  parseProgramInput,
  programIndexDigits,
  programNumberText,
  rankProgram,
  rankRpn,
  rotateToProgram,
  stepProgram,
  unnumberedReason,
  unrankProgram,
  unrankRpn,
} from "./programIndex";
import { encodePresses, previewPresses, pressPreviewForNode } from "./presses";
import { agreementNote, compileExpression, referenceExpression } from "./parse";
import { packCircuit, unpackCircuit } from "./wire";
import { SHORT_PROGRAMS, applyProgram, nodeFromCompact, programK, programNode } from "./programs";
import table from "./best-known.json";
import { keyCostEntries, keyCosts } from "../../components/keyTables";
import { compileSubmission } from "../../components/submitTurn";
import { runCertifyChecks } from "./check-certify";
import shardWeights from "./check-shards.json";

let failed = 0;

/**
 * EML_SHARD=i/N runs only the top-level blocks assigned to shard i (0-based) of N,
 * so CI can run the suite as parallel jobs. Setup outside the blocks runs in every
 * shard. A block must not read anything another block sets: they may run in
 * different processes. Blocks are dealt by the measured weights in
 * check-shards.json (greedy, heaviest first); a block missing from it goes
 * round-robin. EML_BLOCK_TIMES=1 prints each block's wall time.
 * EML_ONLY_BLOCK=<id>[,<id>...] runs only those blocks (overrides EML_SHARD).
 * check-shards.json holds cold times: each block alone in its own process with
 * EML_ONLY_BLOCK=<id> EML_BLOCK_TIMES=1, free of caches warmed by shard-mates.
 */
const shardMatch = /^(\d+)\/(\d+)$/.exec(process.env.EML_SHARD ?? "");
const shardIndex = shardMatch ? Number(shardMatch[1]) : 0;
const shardCount = shardMatch ? Math.max(1, Number(shardMatch[2])) : 1;
const shardOf = assignShards(shardCount);
const onlyBlocks = process.env.EML_ONLY_BLOCK ? new Set(process.env.EML_ONLY_BLOCK.split(",").map(Number)) : null;
const blockTimes = process.env.EML_BLOCK_TIMES === "1";
let openBlock = -1;
let openedAt = 0;

function assignShards(count: number): Map<number, number> {
  const owner = new Map<number, number>();
  if (count <= 1) return owner;
  const load = Array.from({ length: count }, () => 0);
  const weights = Object.entries(shardWeights as Record<string, number>).map(([id, ms]) => [Number(id), ms] as const);
  weights.sort((a, b) => b[1] - a[1] || a[0] - b[0]);
  for (const [id, ms] of weights) {
    let best = 0;
    for (let k = 1; k < count; k += 1) if (load[k] < load[best]) best = k;
    owner.set(id, best);
    load[best] += ms;
  }
  return owner;
}

function closeBlockTimer(): void {
  if (blockTimes && openBlock >= 0) console.log(`block ${openBlock} ${Math.round(performance.now() - openedAt)} ms`);
  openBlock = -1;
}

function shardTurn(id: number): boolean {
  closeBlockTimer();
  const mine = onlyBlocks ? onlyBlocks.has(id) : shardCount <= 1 || (shardOf.get(id) ?? id % shardCount) === shardIndex;
  if (mine) {
    openBlock = id;
    openedAt = performance.now();
  }
  return mine;
}
const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
const tsxCli = path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs");

/** A fresh node process. `npx` and `URL.pathname` both break on Windows. */
function runTsx(script: string, input: string, timeout = 180_000) {
  return spawnSync(process.execPath, [tsxCli, path.join(repoRoot, script)], {
    cwd: repoRoot,
    input,
    encoding: "utf8",
    timeout,
  });
}

function relClose(got: { re: number; im: number }, want: { re: number; im: number }, tol = 1e-12): boolean {
  const scale = Math.max(Math.hypot(want.re, want.im), 1e-320);
  return Math.hypot(got.re - want.re, got.im - want.im) <= tol * scale;
}

function check(name: string, got: { re: number; im: number }, want: { re: number; im: number }, tol = 1e-6) {
  const ok = close(got, want, tol) && Number.isFinite(got.re) && Number.isFinite(got.im);
  if (!ok) {
    failed += 1;
    console.log("FAIL", name, "got", formatC(got), got, "want", want);
  }
}

const e = eml(c(1), c(1));
check("eml(1,1)=e", e, c(Math.E), 1e-15);

check("0", evaluate(constantNode("0")), c(0), 1e-12);
check("-1", evaluate(constantNode("-1")), c(-1), 1e-9);
check("2", evaluate(constantNode("2")), c(2), 1e-9);
check("1/2", evaluate(constantNode("1/2")), c(0.5), 1e-8);
check("2/3", evaluate(constantNode("2/3")), c(2 / 3), 1e-8);
check("sqrt2", evaluate(constantNode("sqrt(2)")), c(Math.SQRT2), 1e-6);
check("i", evaluate(constantNode("i")), c(0, 1), 1e-6);
check("pi", evaluate(constantNode("pi")), c(Math.PI), 1e-6);
check("e const", evaluate(constantNode("e")), c(Math.E), 1e-12);

function applyUnary(name: string, x: number, want: number, tol = 1e-6) {
  const node = applyUnaryNode(name, bindInput(c(x), "x"));
  const stats = circuitStats(node);
  const got = evaluate(node, { x: c(x) });
  check(`${name}(${x}) gates=${stats.dagGates} depth=${stats.depth}`, got, c(want), tol);
}

applyUnary("ln", 2, Math.log(2));
applyUnary("ln", 0.5, Math.log(0.5));
applyUnary("ln", Math.E, 1);
applyUnary("exp", 0, 1);
applyUnary("exp", 1, Math.E);
applyUnary("exp", -1, 1 / Math.E);
applyUnary("sqrt", 4, 2);
applyUnary("sqrt", 2, Math.SQRT2);
applyUnary("sqr", 7, 49);
applyUnary("inv", 4, 0.25);
applyUnary("minus", 3, -3);
applyUnary("minus", -2.5, 2.5);
applyUnary("sin", 0, 0);
applyUnary("sin", Math.PI / 6, 0.5);
applyUnary("sin", Math.PI / 2, 1);
applyUnary("sin", Math.PI, 0, 1e-5);
applyUnary("sin", 1, Math.sin(1));
applyUnary("sin", 4, Math.sin(4), 1e-5);
applyUnary("sin", -1, Math.sin(-1));
applyUnary("cos", 0, 1);
applyUnary("cos", Math.PI / 3, 0.5);
applyUnary("cos", Math.PI, -1, 1e-5);
applyUnary("cos", 10, Math.cos(10), 1e-4);
applyUnary("tan", Math.PI / 4, 1, 1e-5);
applyUnary("sinh", 0.7, Math.sinh(0.7), 1e-5);
applyUnary("cosh", 0.7, Math.cosh(0.7), 1e-5);
applyUnary("tanh", 0.7, Math.tanh(0.7), 1e-5);
applyUnary("arcsin", 0.5, Math.asin(0.5), 1e-5);
applyUnary("arccos", 0.5, Math.acos(0.5), 1e-5);
applyUnary("arctan", 1, Math.PI / 4, 1e-5);
applyUnary("arsinh", 0.8, Math.asinh(0.8), 1e-5);
applyUnary("sigma", 0, 0.5, 1e-5);

function applyBinary(name: string, x: number, y: number, want: number, tol = 1e-6) {
  const node = applyBinaryNode(name, bindInput(c(x), "x"), bindInput(c(y), "y"));
  check(`${name}(${x},${y})`, evaluate(node, { x: c(x), y: c(y) }), c(want), tol);
}

applyBinary("add", 3, 4, 7);
applyBinary("sub", 3, 4, -1);
applyBinary("mul", -2, -3, 6);
applyBinary("mul", 2.5, 4, 10);
applyBinary("div", 3, 4, 0.75);
applyBinary("pow", 2, 10, 1024);
applyBinary("pow", 9, 0.5, 3);
applyBinary("log", 2, 8, 3);
applyBinary("avg", 2, 8, 5);
applyBinary("hypot", 3, 4, 5);

const lnRpn = rpnTokens(substitute(unaryNode("ln"), { x: bindInput(c(2), "x") }));
if (lnRpn?.join(" ") !== "1 1 x E 1 E E") {
  failed += 1;
  console.log("FAIL ln rpn", lnRpn);
}

const exprs: [string, number][] = [
  ["e", Math.E],
  ["pi", Math.PI],
  ["i*i", -1],
  ["ln(2)", Math.log(2)],
  ["sin(pi/6)", 0.5],
  ["cos(pi/3)", 0.5],
  ["sqrt(2)", Math.SQRT2],
  ["2^10", 1024],
  ["(1+sqrt(5))/2", (1 + Math.sqrt(5)) / 2],
  ["log(2, 8)", 3],
  ["hypot(3, 4)", 5],
  ["2+2*2", 6],
  ["2^3^2", 512],
  ["-2^2", -4],
  ["2^-2^2", 1 / 16],
  ["2*-3^2", -18],
  ["(-2)^2", 4],
  ["tanh(1)", Math.tanh(1)],
  ["avg(2, 8)", 5],
  ["(-2)*(-3)", 6],
  ["exp(ln(7))", 7],
  ["0^1", 0],
  ["0^2", 0],
  ["sqrt(0)", 0],
  ["(1-1)^2", 0],
  ["400+400", 800],
  ["1000-1000", 0],
  ["2^10+2^10", 2048],
  ["1024-1024", 0],
  ["2^100-2^100", 0],
  ["(1e-6)^2", 1e-12],
  ["1000000-999999", 1],
  ["exp(-25)", Math.exp(-25)],
];

for (const [source, want] of exprs) {
  const node = compileExpression(source, {});
  const got = evaluate(node);
  const ref = referenceExpression(source, {});
  check(`expr ${source}`, got, c(want), 1e-5);
  if (ref) check(`ref ${source}`, ref, c(want), 1e-9);
}

check("(1e-6)^2 tight", evaluate(compileExpression("(1e-6)^2", {})), c(1e-12), 1e-6);
check("million minus exact", exactToFloat(exactEvaluate(compileExpression("1000000-999999", {}))), c(1), 1e-9);

if (formatC(c(1e-9)) === "0" || formatC(c(Math.exp(-25))) === "0" || formatC(c(1e-20)) === "0") {
  failed += 1;
  console.log("FAIL small values displayed as 0", formatC(c(1e-9)), formatC(c(Math.exp(-25))), formatC(c(1e-20)));
}
if (formatC(c(0, Infinity)) !== "∞i") {
  failed += 1;
  console.log("FAIL imag infinity", formatC(c(0, Infinity)));
}
// A fraction twelve digits can show is not printed as the nearby integer.
for (const [value, want] of [
  [c(2e9 / 3), "666666666.667"],
  [c(1e9 / 7), "142857142.857"],
  [c(500000000.5), "500000000.5"],
  [c(0, 1e10 / 3), "3.333333×10^9i"],
  [c(3 + 4e-13), "3"],
  [c(1e14 + 0.25), "100000000000000"],
  [c(0, 1 + 1e-10), "1.0000000001i"],
  [c(0, -(1 + 1e-13)), "−i"],
] as const) {
  if (formatC(value) !== want) {
    failed += 1;
    console.log("FAIL float display digits", value, formatC(value), "want", want);
  }
}
// The imaginary coefficient keeps the digits the real part would show.
for (const [source, want] of [
  ["i*(1+10^-12)", "1.000000000001i"],
  ["i*(1-10^-72)", `0.${"9".repeat(72)}i`],
  ["2-i*(1+3*10^-13)", "2 − 1.0000000000003i"],
  ["exp(i*pi/2)", "i"],
] as const) {
  const text = formatExact(exactEvaluate(compileExpression(source, {})));
  if (text !== want) {
    failed += 1;
    console.log("FAIL exact imaginary digits", source, text, "want", want);
  }
}
const expTiny = evaluate(compileExpression("exp(-50)", {}));
const expWant = Math.exp(-50);
if (Math.abs(expTiny.re - expWant) > 1e-6 * expWant || expTiny.im !== 0) {
  failed += 1;
  console.log("FAIL exp(-50)", expTiny, expWant);
}
const belowCut = evaluate(compileExpression("ln(-1-1e-9*i)", {}));
if (!(belowCut.im < 0)) {
  failed += 1;
  console.log("FAIL ln below the cut", belowCut);
}
check("sqrt(-4) via radical", evaluate(compileExpression("√-4", {})), c(0, 2), 1e-6);
if (shardTurn(0)) {
  const huge = compileExpression("asinh(1e200)", {});
  const wide = exactToFloat(exactEvaluate(huge));
  check("asinh huge exact", wide, c(Math.asinh(1e200)), 1e-8);
}
check("hypot huge", evaluate(compileExpression("hypot(1e200,1e200)", {})), c(Math.hypot(1e200, 1e200)), 1e-6);
const hypotTiny = evaluate(compileExpression("hypot(1e-200,1e-200)", {}));
const hypotTinyWant = Math.hypot(1e-200, 1e-200);
if (Math.abs(hypotTiny.re - hypotTinyWant) > 1e-6 * hypotTinyWant || Math.abs(hypotTiny.im) > 1e-9 * hypotTinyWant) {
  failed += 1;
  console.log("FAIL hypot tiny", hypotTiny, hypotTinyWant);
}
if (shardTurn(1)) {
  const at = exactReport(compileExpression("atan(1/0)", {}));
  if (at.value.im.isFinite() || at.singular === null) {
    failed += 1;
    console.log("FAIL atan(inf) circuit", formatExact(at.value), at.singular);
  }
}
if (recognize(c(1e-9)) === "0" || recognize(c(0.999999996973)) === "1" || recognize(c(3.141592654)) !== null || recognize(c(Math.PI)) !== "π") {
  failed += 1;
  console.log("FAIL recognize", recognize(c(1e-9)), recognize(c(0.999999996973)), recognize(c(3.141592654)), recognize(c(Math.PI)));
}
try {
  literalNode("0x10");
  failed += 1;
  console.log("FAIL 0x10 was accepted");
} catch {
  // hex is not a decimal literal
}
for (const blank of ["", " "]) {
  try {
    literalNode(blank);
    failed += 1;
    console.log("FAIL blank literal was accepted", JSON.stringify(blank));
  } catch (err) {
    if (!(err instanceof EmlError)) {
      failed += 1;
      console.log("FAIL blank literal", err);
    }
  }
}

try {
  evaluate({ type: "eml", a: ONE } as Node);
  failed += 1;
  console.log("FAIL missing child did not throw");
} catch (err) {
  if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
    failed += 1;
    console.log("FAIL missing child", err);
  }
}
for (const name of ["toString", "constructor", "x"]) {
  try {
    evaluate(V(name), {});
    failed += 1;
    console.log("FAIL unbound name was accepted", name);
  } catch (err) {
    if (!(err instanceof EmlError)) {
      failed += 1;
      console.log("FAIL unbound name", name, err);
    }
  }
}
check("own toString binding", evaluate(V("toString"), { toString: c(4) }), c(4), 1e-9);
if (rpnTokens(ONE, 0) !== null || describe(V("abcdefghij"), 4) !== null) {
  failed += 1;
  console.log("FAIL leaf budget", rpnTokens(ONE, 0), describe(V("abcdefghij"), 4));
}
if (rpnTokens(ONE, 1)?.join(" ") !== "1" || describe(ONE, 1) !== "1") {
  failed += 1;
  console.log("FAIL leaf within budget", rpnTokens(ONE, 1), describe(ONE, 1));
}

check("integer 6", evaluate(integerNode(6)), c(6), 1e-8);
if (shardTurn(2)) {
  const neg = integerNode(-1000);
  const wide = exactToFloat(exactEvaluate(neg));
  check("integer -1000 exact", wide, c(-1000), 1e-9);
  const narrow = evaluate(neg);
  if (Number.isFinite(narrow.re) && !close(narrow, c(-1000), 1e-6)) {
    failed += 1;
    console.log("FAIL integer -1000 float", narrow);
  }
}

const lnNeg = evaluate(compileExpression("ln(-1)", {}));
const lnNegRef = referenceExpression("ln(-1)", {});
check("ln(-1)", lnNeg, c(0, Math.PI), 1e-6);
if (!lnNegRef) {
  failed += 1;
  console.log("FAIL ln(-1) reference missing");
} else {
  check("ln(-1) reference", lnNegRef, c(0, Math.PI), 1e-9);
}

const cube = evaluate(compileExpression("(-8)^(1/3)", {}));
check("cube root of -8", cube, c(1, Math.sqrt(3)), 1e-5);

const divNeg = evaluate(compileExpression("(-1)/0", {}));
if (divNeg.re !== -Infinity || divNeg.im !== 0) {
  failed += 1;
  console.log("FAIL (-1)/0", divNeg);
}
const divPos = evaluate(compileExpression("1/0", {}));
if (divPos.re !== Infinity || divPos.im !== 0) {
  failed += 1;
  console.log("FAIL 1/0", divPos);
}

if (shardTurn(3)) {
  const pole = evaluate(compileExpression("tan(pi/2)", {}));
  if (Number.isFinite(pole.re) && Math.abs(pole.re) < 1e6) {
    failed += 1;
    console.log("FAIL tan(pi/2) stayed small", pole);
  }
}
check("arcsin(2)", evaluate(compileExpression("arcsin(2)", {})), c(Math.PI / 2, -1.3169578969248166), 1e-6);
check("arccos(2)", evaluate(compileExpression("arccos(2)", {})), c(0, 1.3169578969248166), 1e-6);
if (shardTurn(4)) {
  const sinhNode = compileExpression("sinh(710)", {});
  const coshNode = compileExpression("cosh(710)", {});
  check("sinh(710) exact", exactToFloat(exactEvaluate(sinhNode)), c(Math.sinh(710)), 1e-6);
  check("cosh(710) exact", exactToFloat(exactEvaluate(coshNode)), c(Math.cosh(710)), 1e-6);
}

const hugeQuotient = evaluate(compileExpression("1e308/2", {}));
if (Math.abs(hugeQuotient.re - 5e307) > 1e-6 * 5e307 || hugeQuotient.im !== 0) {
  failed += 1;
  console.log("FAIL 1e308/2", hugeQuotient);
}
const tanImag = evaluate(applyUnaryNode("tan", bindInput(c(0, 2), "z")), { z: c(0, 2) });
check("tan(2i)", tanImag, c(0, Math.tanh(2)), 1e-6);
const divNegZero = cdiv(c(1), c(-0));
if (divNegZero.re !== -Infinity || divNegZero.im !== 0) {
  failed += 1;
  console.log("FAIL direct 1/(-0)", divNegZero);
}

const below = evaluate(compileExpression("ln(-1-1e-9*i)", {}));
if (!(below.im < 0)) {
  failed += 1;
  console.log("FAIL ln just below the cut", below);
}

if (constantNode("pi").type !== "eml" || constantNode("i").type !== "eml" || constantNode("e").type !== "eml") {
  failed += 1;
  console.log("FAIL constants collapsed", constantNode("pi").type, constantNode("i").type, constantNode("e").type);
}

for (const source of ["0^2", "sqrt(0)", "(1-1)^2", "(-1)/0"]) {
  const tokens = rpnTokens(compileExpression(source, {}), 40);
  if (tokens?.includes("undefined")) {
    failed += 1;
    console.log("FAIL program tape", source, tokens);
  }
}

const sinNode = applyUnaryNode("sin", bindInput(c(Math.PI / 6), "x"));
if (sinNode.type !== "eml") {
  failed += 1;
  console.log("FAIL sin(pi/6) was not kept as an EML circuit");
}

function sharedPow(depth: number): Node {
  let node: Node = ONE;
  for (let i = 0; i < depth; i++) node = E(node, node);
  return node;
}

let nested = "1";
for (let i = 0; i < 3; i++) nested = `eml(${nested}, ${nested})`;
if (describe(sharedPow(3)) !== nested) {
  failed += 1;
  console.log("FAIL shared describe", describe(sharedPow(3)));
}
const deepDescribe = sharedPow(20);
const describeStart = performance.now();
const deepText = describe(deepDescribe);
if (deepText !== null || performance.now() - describeStart > 50) {
  failed += 1;
  console.log("FAIL deep describe", deepText, performance.now() - describeStart);
}
if (rpnTokens(deepDescribe) !== null) {
  failed += 1;
  console.log("FAIL deep rpn", rpnTokens(deepDescribe));
}
const sharedGate = E(ONE, ONE);
if (rpnTokens(E(sharedGate, sharedGate))?.join(" ") !== "1 1 E 1 1 E E") {
  failed += 1;
  console.log("FAIL shared rpn", rpnTokens(E(sharedGate, sharedGate)));
}
if (describe(unaryNode("ln")) === null) {
  failed += 1;
  console.log("FAIL ln describe");
}
const lnStats = circuitStats(substitute(unaryNode("ln"), { x: bindInput(c(2), "x") }));
if (lnStats.dagGates !== 3 || lnStats.depth !== 3) {
  failed += 1;
  console.log("FAIL ln stats", lnStats);
}
const powStats = circuitStats(sharedPow(8));
if (powStats.dagGates !== 8 || powStats.depth !== 8) {
  failed += 1;
  console.log("FAIL shared stats", powStats);
}
evaluate(sharedPow(8));

function absClose(name: string, got: { re: number; im: number }, re: number, im: number, tol = 1e-8) {
  if (Math.abs(got.re - re) > tol || Math.abs(got.im - im) > tol) {
    failed += 1;
    console.log("FAIL", name, got, "want", re, im);
  }
}

const ii = tI();
const a = tAdd(tTwo(), tMul(tHalf(), ii));
const b4 = tAdd(ONE, tMul(integerNode(4), ii));
const b3 = tAdd(ONE, tMul(integerNode(3), ii));
const b7 = tMul(integerNode(7), ii);
const sub4 = domainSub(a, b4);
absClose("a-(1+4i)", evaluate(sub4), 1, -3.5);
absClose("a-(1+4i) exact", exactToFloat(exactEvaluate(sub4)), 1, -3.5);
const naive4 = evaluate(naiveSub(a, b4));
if (Math.abs(naive4.im + 3.5) < 0.2) {
  failed += 1;
  console.log("FAIL naive a-(1+4i) should miss 1-3.5i", naive4);
}
absClose("naive a-(1+4i) folded", naive4, 1, -3.5 + 2 * Math.PI, 1e-8);
absClose("a-(1+3i) control", evaluate(domainSub(a, b3)), 1, -2.5);
absClose("a-7i", evaluate(domainSub(a, b7)), 2, -6.5);
const naive7 = evaluate(naiveSub(a, b7));
if (Math.abs(naive7.im + 6.5) < 0.2) {
  failed += 1;
  console.log("FAIL naive a-7i", naive7);
}
const b35 = tAdd(tTwo(), tMul(tAdd(integerNode(3), tHalf()), ii));
absClose("2-(2+3.5i)", evaluate(domainSub(tTwo(), b35)), 0, -3.5);
absClose("2-(1-4i)", evaluate(domainSub(tTwo(), tAdd(ONE, tMul(integerNode(-4), ii)))), 1, 4);

const product = evaluate(compileExpression("(1+2*i)*(1+3*i)", {}));
absClose("(1+2i)(1+3i)", product, -5, 5);
const lnOfNeg = evaluate(compileExpression("ln(-2)", {}));
absClose("ln(-2)", lnOfNeg, Math.log(2), Math.PI);
absClose("ln(-2) exact", exactToFloat(exactEvaluate(compileExpression("ln(-2)", {}))), Math.log(2), Math.PI);
absClose("ln(-0.4+0.2i)", evaluate(compileExpression("ln(-0.4+0.2*i)", {})), Math.log(Math.hypot(-0.4, 0.2)), Math.atan2(0.2, -0.4));
if (formatC(c(1, 1e-8)).includes("i") === false) {
  failed += 1;
  console.log("FAIL small imag dropped", formatC(c(1, 1e-8)));
}

const above = E(input(c(0), "0"), input(c(-2, 1e-300), "z"));
const belowTiny = E(input(c(0), "0"), input(c(-2, -1e-300), "z"));
const aboveIm = exactEvaluate(above).im.neg();
const belowIm = exactEvaluate(belowTiny).im.neg();
if (!(aboveIm.gt(0) && belowIm.lt(0))) {
  failed += 1;
  console.log("FAIL ±1e-300 sides", aboveIm.toString(), belowIm.toString());
}

for (const id of ["0", "-1", "2", "1/2", "i", "pi", "sqrt(2)", "e"]) {
  if (!isPure(constantNode(id))) {
    failed += 1;
    console.log("FAIL impure", id);
  }
}
for (const id of ["-2", "-1/2", "3", "1/2-strict"]) {
  if (!isPure(programNode(id))) {
    failed += 1;
    console.log("FAIL impure program", id);
  }
}
if (!isPure(literalNode("10")) || !isPure(literalNode("0.1"))) {
  failed += 1;
  console.log("FAIL impure literal");
}
if (programK("-2") !== 25 || programK("-1/2") !== 29 || programK("1/2") !== 29 || programK("1/2-strict") !== 31) {
  failed += 1;
  console.log("FAIL record lengths", programK("-2"), programK("-1/2"), programK("1/2-strict"));
}
if (!exactClose(exactEvaluate(programNode("-2")), -2, 0, 15)) {
  failed += 1;
  console.log("FAIL -2 value");
}
const strictHalf = exactReport(programNode("1/2-strict"));
if (strictHalf.singular !== null || !exactClose(strictHalf.value, 0.5, 0, 15)) {
  failed += 1;
  console.log("FAIL strict 1/2", formatExact(strictHalf.value), strictHalf.singular);
}
for (const [id, re] of [
  ["-1/2-strict", -0.5],
  ["1/2-alt", 0.5],
] as const) {
  if (programK(id) !== 31) {
    failed += 1;
    console.log("FAIL K31 word length", id, programK(id));
  }
  const wide = exactReport(programNode(id));
  const floated = evaluateReport(programNode(id));
  if (
    wide.touchedLn0 ||
    floated.touchedLn0 ||
    wide.singular !== null ||
    !acceptsConstantProgram(programNode(id), re, 0)
  ) {
    failed += 1;
    console.log("FAIL K31 no-inf half", id, wide.touchedLn0, floated.touchedLn0, wide.singular);
  }
}
const halfReport = evaluateReport(programNode("1/2"));
if (halfReport.singular !== null || !halfReport.touchedLn0) {
  failed += 1;
  console.log("FAIL 1/2 ln 0 should cancel", halfReport.singular, halfReport.touchedLn0);
}
const third = exactParts(1, 0).re.div(3);
const storedPi = exactEvaluate(programNode("pi")).re;
const checkRecord = (id: string, k: number, re: Decimal.Value, im: Decimal.Value, usesLn0: boolean) => {
  if (programK(id) !== k) {
    failed += 1;
    console.log("FAIL record length", id, programK(id), k);
  }
  const report = exactReport(programNode(id), {}, { maxNodes: 200_000 });
  if (report.singular !== null || report.touchedLn0 !== usesLn0 || !exactClose(report.value, re, im, 30)) {
    failed += 1;
    console.log("FAIL record value", id, formatExact(report.value), report.singular, report.touchedLn0);
  }
};
checkRecord("-ipi", 45, 0, storedPi.neg(), true);
checkRecord("-ipi-strict", 47, 0, storedPi.neg(), false);
checkRecord("4", 39, 4, 0, false);
checkRecord("2/3", 39, third.mul(2), 0, false);
checkRecord("-1/3", 41, third.neg(), 0, false);
checkRecord("-3", 35, -3, 0, false);
checkRecord("1/3", 35, third, 0, true);
checkRecord("1/3-strict", 37, third, 0, false);
const thirdImpostor = "111E1111E11E11E1E11EEEEE11EEE1E1EEE1E";
if (
  thirdImpostor.length !== 37 ||
  Object.values(SHORT_PROGRAMS).includes(thirdImpostor) ||
  exactClose(exactEvaluate(nodeFromCompact(thirdImpostor), {}, { maxNodes: 200_000 }), 1 / 3, 0, 12)
) {
  failed += 1;
  console.log("FAIL 1/3 impostor was stored or accepted");
}
const lnZero = evaluateReport(compileExpression("ln(0)", {}));
if (lnZero.value.re !== -Infinity || lnZero.singular !== SINGULAR_LN0) {
  failed += 1;
  console.log("FAIL ln 0", lnZero);
}
const expNegInf = evaluate(compileExpression("exp(ln(0))", {}));
if (expNegInf.re !== 0 || expNegInf.im !== 0) {
  failed += 1;
  console.log("FAIL exp(-inf)", expNegInf);
}
const indeterminate = eml(c(Infinity), c(Infinity));
if (!Number.isNaN(indeterminate.re)) {
  failed += 1;
  console.log("FAIL inf-inf", indeterminate);
}
const zeroInf = evaluateReport(compileExpression("0*(1/0)", {}));
if (zeroInf.singular !== SINGULAR_INDET || !Number.isNaN(zeroInf.value.re) || !Number.isNaN(zeroInf.value.im)) {
  failed += 1;
  console.log("FAIL 0*inf", zeroInf);
}
const zeroInfExact = exactReport(compileExpression("0*(1/0)", {}), {}, { maxNodes: 20_000 });
if (zeroInfExact.singular !== SINGULAR_INDET || !zeroInfExact.value.re.isNaN()) {
  failed += 1;
  console.log("FAIL exact 0*inf", formatExact(zeroInfExact.value), zeroInfExact.singular);
}
if (shardTurn(5)) {
  const rawMul = applyProgram("mul", {
    x: E(input({ re: -Infinity, im: 0 }, "−∞"), ONE),
    y: applyProgram("div", { x: input({ re: 5, im: 0 }, "5"), y: input({ re: 0, im: 0 }, "0") }),
  });
  const rawReport = exactReport(rawMul);
  if (rawReport.singular !== SINGULAR_INDET || !rawReport.value.re.isNaN() || !rawReport.value.im.isNaN()) {
    failed += 1;
    console.log("FAIL raw mul(exp(−∞), 5/0)", formatExact(rawReport.value), rawReport.singular);
  }
}
if (shardTurn(6)) {
  const logged = compileExpression("ln(-0)", {});
  const floated = evaluateReport(logged);
  const exact = exactReport(logged);
  const sameImag = floated.value.im > 0 && exact.value.im.isPos() && floated.value.re === -Infinity && exact.value.re.isNeg() && !exact.value.re.isFinite();
  if (!sameImag) {
    failed += 1;
    console.log("FAIL ln(−0) banks", floated.value, formatExact(exact.value));
  }
  const below = evaluateReport(compileExpression("ln(-2-1e-20*i)", {}));
  const dust = evaluateReport(compileExpression("ln(-2-1e-35*i)", {}));
  const belowExact = exactReport(compileExpression("ln(-2-1e-20*i)", {}));
  if (!below.nearCut || !dust.nearCut || !belowExact.value.im.isNeg()) {
    failed += 1;
    console.log("FAIL near-cut log", below.nearCut, below.value, dust.nearCut, dust.value, formatExact(belowExact.value));
  }
  const clear = evaluateReport(compileExpression("ln(-2-1e-12*i)", {}));
  if (clear.nearCut || clear.value.im >= 0) {
    failed += 1;
    console.log("FAIL log clearly below the cut was flagged", clear.value, clear.nearCut);
  }
}
if (shardTurn(7)) {
  const huge = evaluateReport(compileExpression("x-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(1e200, 2e7) });
  if (huge.singular !== SINGULAR_RANGE || !Number.isNaN(huge.value.re)) {
    failed += 1;
    console.log("FAIL huge subtrahend message", huge.singular, huge.value);
  }
}
if (clog(c(-1, 0)).im !== -Math.PI || clog(c(-1, -0)).im !== -Math.PI) {
  failed += 1;
  console.log("FAIL pinned cut", clog(c(-1, 0)), clog(c(-1, -0)));
}
if (evaluate(constantNode("i")).im <= 0) {
  failed += 1;
  console.log("FAIL i sign");
}

const wantedK: Record<string, number> = {
  e: 3,
  "0": 7,
  "-1": 15,
  "2": 19,
  ipi: 21,
};
const searchedRun = searchConstants(21);
const searched = searchedRun.hits;
// The pool keeps every finite circuit that did not overflow: 16311 through K 21, the same as v1.0.
if (searchedRun.pool !== 16311) {
  failed += 1;
  console.log("FAIL K21 pool changed", searchedRun.pool);
}
for (const [id, k] of Object.entries(wantedK)) {
  const hit = searched.find((item) => item.id === id);
  if (!hit || hit.k !== k) {
    failed += 1;
    console.log("FAIL K", id, hit, "want", k);
  }
}
const ipiWord = "111111E1EEEE11E1E1EEE";
const ipiNode = nodeFromRpn(ipiWord.split(""));
const ipiValue = evaluate(ipiNode);
if (ipiValue.im <= 0 || Math.abs(ipiValue.re) > 1e-6) {
  failed += 1;
  console.log("FAIL K21 word is +iπ on this cut", ipiValue);
}
const ipiHit = searched.find((item) => item.rpn === ipiWord);
if (ipiHit && ipiHit.id !== "ipi") {
  failed += 1;
  console.log("FAIL golf labeled the K21 word", ipiHit.id);
}
const namedIpi = searched.find((item) => item.id === "ipi");
if (namedIpi && evaluate(nodeFromRpn(namedIpi.rpn.split(""))).im <= 0) {
  failed += 1;
  console.log("FAIL golf ipi label is the negative cut", namedIpi.rpn);
}
const negPi = exactValueAt(ipiNode, 280).im.neg();
const k33Word = "11111EE1E1111E1E1EEEE1EE11E1E1EEE";
const k35Word = "11111111E1E1EEEEEE111EEE1E11E1E1EEE";
const k33Node = nodeFromCompact(k33Word);
const k35Node = nodeFromCompact(k35Word);
// The K 33 word is 5.724×10^(−116) − iπ. A 40-digit read either loses that part (0) or,
// once it re-reads a log just off the negative axis, keeps its true value. Never −iπ.
const k33At40 = exactValueAt(k33Node, 40);
const k33Re = k33At40.re.isZero() || k33At40.re.sub("5.724022659417535e-116").abs().lt("1e-129");
if (!k33Re || acceptsConstantProgram(k33Node, 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL K33 word", k33At40.re.toString(), acceptsConstantProgram(k33Node, 0, -Math.PI));
}
if (acceptsConstantProgram(k35Node, 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL K35 −iπ impostor was accepted");
}
// A deeper one: −9×10^(−307) − i(π − 4×10^(−307)). The ball and the 280-digit compare
// both read it as −iπ; exact mode sees the 10^(−306) part it passes through.
const k35DeepNode = nodeFromCompact("11111111E11E1EE1EEEEEE1E1E11E1E1EEE");
if (acceptsConstantProgram(k35DeepNode, 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL K35 −iπ impostor near 10^(−307) was accepted");
}
const rot = rotSubCircuit(V("x"), V("y"));
const rotStats = circuitStats(rot);
if (rotStats.rpnLength !== BigInt(131) || rotStats.dagGates !== 34) {
  failed += 1;
  console.log("FAIL rotSub size", rotStats.rpnLength.toString(), rotStats.dagGates);
}
if (!acceptsConstantValue(exactParts(0, negPi), 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL exact −iπ was rejected");
}
if (!acceptsConstantValue(exactValueAt(ipiNode, 280), 0, Math.PI)) {
  failed += 1;
  console.log("FAIL K21 +iπ failed the 240-digit check");
}
if (acceptsConstantValue(exactParts("-1.00000000000000000001", "0"), -1, 0)) {
  failed += 1;
  console.log("FAIL −1 + 10^(−20) was accepted");
}
if (acceptsConstantValue(exactParts("0", "3.1415926535897932384726433832795"), 0, Math.PI)) {
  failed += 1;
  console.log("FAIL i(π + 10^(−20)) was accepted");
}
if (searched.some((hit) => hit.id === "-ipi")) {
  failed += 1;
  console.log("FAIL golf kept a −iπ hit by K 21");
}
const minusOne = searched.find((item) => item.id === "-1");
const halfHit = searched.find((item) => item.id === "1/2");
if (minusOne && (!minusOne.usesLn0 || minusOne.singular)) {
  failed += 1;
  console.log("FAIL -1 ln 0 should be recorded but finite", minusOne);
}
if (halfHit) {
  failed += 1;
  console.log("FAIL 1/2 appeared before K 21", halfHit);
}
const noInf = searchConstants(15, { allowLn0: false }).hits;
if (noInf.some((hit) => hit.usesLn0 || hit.domain === "extended") || noInf.some((hit) => hit.id === "-1")) {
  failed += 1;
  console.log("FAIL no-inf search kept a ln 0 program", noInf);
}
if (!noInf.some((hit) => hit.id === "0") || !noInf.some((hit) => hit.id === "e")) {
  failed += 1;
  console.log("FAIL no-inf search dropped a finite constant", noInf.map((hit) => hit.id));
}
if (shardTurn(8)) {
  const k23Word = "111111E1E1EEE1EE11E1EEE";
  const k23Node = nodeFromCompact(k23Word);
  const k23Ball = enclose(k23Node);
  if (ballVerdict(k23Ball, 0, -Math.PI) === "equal" || ballVerdict(k23Ball, 0, Math.PI) === "equal") {
    failed += 1;
    console.log("FAIL K23 ball certified a branch", k23Ball.cut, k23Ball.im.toString());
  }
  if (!acceptsConstantProgram(k23Node, 0, Math.PI) || acceptsConstantProgram(k23Node, 0, -Math.PI)) {
    failed += 1;
    console.log("FAIL K23 acceptance", acceptsConstantProgram(k23Node, 0, Math.PI), acceptsConstantProgram(k23Node, 0, -Math.PI));
  }
  const halfNode = programNode("1/2-strict");
  if (ballVerdict(enclose(halfNode), 0.5, 0) === "equal" || !acceptsConstantProgram(halfNode, 0.5, 0)) {
    failed += 1;
    console.log("FAIL cut ball certified 1/2", ballVerdict(enclose(halfNode), 0.5, 0));
  }
  for (const [id, re, im] of [
    ["e", Math.E, 0],
    ["0", 0, 0],
    ["2", 2, 0],
    ["3", 3, 0],
  ] as const) {
    const verdict = ballVerdict(enclose(programNode(id)), re, im);
    if (verdict !== "equal" || !acceptsConstantProgram(programNode(id), re, im)) {
      failed += 1;
      console.log("FAIL ball did not certify", id, verdict);
    }
  }
  const noInfPi = searchConstants(23, { allowLn0: false }).hits;
  const cleanPi = noInfPi.find((item) => item.id === "ipi");
  if (!cleanPi || cleanPi.k !== 23 || cleanPi.usesLn0 || cleanPi.rpn !== k23Word) {
    failed += 1;
    console.log("FAIL no-inf +iπ", cleanPi);
  }
}
if (minusOne && ln0Dependence(minusOne) !== "depends on ln 0 = −∞") {
  failed += 1;
  console.log("FAIL -1 was not labeled as depending on ln 0", minusOne);
}
const solo = searchConstantsMerged(15, 1);
const split = searchConstantsMerged(15, 4);
for (const id of ["e", "0", "-1"]) {
  if (solo.find((item) => item.id === id)?.k !== split.find((item) => item.id === id)?.k) {
    failed += 1;
    console.log("FAIL worker merge", id, solo, split);
  }
}
const fingerA = functionFingerprint(tAdd(X, Y), (point) => ({ x: point, y: { re: 0.3, im: -0.2 } }));
const fingerB = functionFingerprint(tAdd(Y, X), (point) => ({ x: point, y: { re: 0.3, im: -0.2 } }));
if (fingerA !== fingerB) {
  failed += 1;
  console.log("FAIL fingerprint add");
}
const kept = exactToFloat(exactEvaluate(tAdd(X, Y), { x: c(-2.5, 1e-4), y: c(0.3, -0.2) }));
absClose("exact add keeps 1e-4", kept, -2.2, -0.1999, 1e-12);

const gate = E(ONE, ONE);
if (gate.type !== "eml") throw new Error("expected an eml node");
const cycle = { type: "eml" as const, a: gate, b: ONE, id: -1 };
cycle.a = cycle;
try {
  evaluate(cycle);
  failed += 1;
  console.log("FAIL cycle evaluate did not throw");
} catch (err) {
  if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
    failed += 1;
    console.log("FAIL cycle evaluate", err);
  }
}
try {
  circuitStats(cycle);
  failed += 1;
  console.log("FAIL cycle stats did not throw");
} catch (err) {
  if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
    failed += 1;
    console.log("FAIL cycle stats", err);
  }
}
if (describe(cycle) !== null || rpnTokens(cycle) !== null) {
  failed += 1;
  console.log("FAIL cycle text", describe(cycle), rpnTokens(cycle));
}
if (evaluate(ONE).re !== 1 || evaluate(ONE).im !== 0) {
  failed += 1;
  console.log("FAIL one", evaluate(ONE));
}

const regressions: [string, number, number][] = [
  ["sin(1e-5)", 1e-5, 0],
  ["sin(pi/6)", 0.5, 0],
  ["asinh(-2)", Math.asinh(-2), 0],
  ["asinh(0)", 0, 0],
  ["hypot(-3,4)", 5, 0],
  ["hypot(0,5)", 5, 0],
  ["avg(0,5)", 2.5, 0],
  ["1000+i", 1000, 1],
  ["arcsin(1)", Math.PI / 2, 0],
  ["0-ln(-2)", -Math.log(2), -Math.PI],
  ["1-ln(-1)", 1, -Math.PI],
  ["2-(pi-1e-12)*i", 2, -(Math.PI - 1e-12)],
  ["sqrt(1e-4)", 0.01, 0],
  ["(1+1e-15)-1", 0, 0],
];
for (const [source, re, im] of regressions) {
  const got = evaluate(compileExpression(source, {}));
  if (source === "(1+1e-15)-1") {
    const exact = exactToFloat(exactEvaluate(compileExpression(source, {})));
    if (got.re === 0 || got.im !== 0 || !close(got, c(1.1102230246251565e-15), 1e-6)) {
      failed += 1;
      console.log("FAIL float tiny subtraction", got);
    }
    if (!close(exact, c(1e-15), 1e-9)) {
      failed += 1;
      console.log("FAIL exact tiny subtraction", exact);
    }
    continue;
  }
  if (!close(got, c(re, im), 1e-8)) {
    failed += 1;
    console.log("FAIL", source, got, re, im);
  }
}

// (a − c) − c is a − 2c. mpmath at 50 digits. Hardware is the float circuit;
// exact is compared at 40 digits, which these circuits actually reach.
if (shardTurn(9)) {
  const rows: Array<{ source: string; re: string; im: string; vars?: Record<string, Node> }> = [
    { source: "e-1-1", re: "0.71828182845904523536028747135266249775724709369996", im: "0" },
    { source: "pi-1-1", re: "1.1415926535897932384626433832795028841971693993751", im: "0" },
    { source: "10-3-3", re: "4", im: "0" },
    { source: "2*e-e-e", re: "0", im: "0" },
    { source: "arcosh(e-1)", re: "1.1364211033963852565125274801058381954056538237393", im: "0" },
    { source: "arcosh(pi-1)", re: "1.3950997261071488078584719796130035077474855890456", im: "0" },
    { source: "sin(1.5-1-1)", re: "-0.4794255386042030002732879352155713880818033679406", im: "0" },
    { source: "pi-1-1-1", re: "0.14159265358979323846264338327950288419716939937511", im: "0" },
    { source: "(1.5-7)-7+7", re: "-5.5", im: "0" },
    { source: "x-y-y", re: "-3.5", im: "0", vars: { x: literalNode("0.5"), y: literalNode("2") } },
    { source: "(2+3i)-1-1", re: "0", im: "3" },
    // The two identities subComplement still folds.
    { source: "e-(e-1)", re: "1", im: "0" },
    { source: "(e-1)-e", re: "-1", im: "0" },
  ];
  for (const row of rows) {
    const node = compileExpression(row.source, row.vars ?? {});
    const hw = evaluateReport(node);
    const ex = exactReport(node);
    const want = c(Number(row.re), Number(row.im));
    const err = Math.hypot(hw.value.re - want.re, hw.value.im - want.im);
    const scale = Math.max(Math.hypot(want.re, want.im), 1);
    const hardwareOk = !hw.singular && err <= 1e-12 * scale;
    const exactOk = ex.singular === null && exactClose(ex.value, row.re, row.im, 40);
    if (!hardwareOk || !exactOk) {
      failed += 1;
      console.log("FAIL repeated subtraction", row.source, hw.value, hw.singular, formatExact(ex.value), ex.singular, "want", row.re, row.im);
    }
  }
}

const zeroSubtrahends = ["3-ln(2/2)", "1+ln(2/2)", "1-ln(1/1)", "1-log(2,1)", "1-sin(0*pi)"];
for (const source of zeroSubtrahends) {
  const node = compileExpression(source, {});
  const got = evaluateReport(node);
  const want = source.startsWith("3") ? c(3) : c(1);
  const exact = exactToFloat(exactEvaluate(node));
  if (!close(got.value, want, 1e-9) || got.overflowed || !close(exact, want, 1e-9)) {
    failed += 1;
    console.log("FAIL zero subtrahend", source, got.value, got.overflowed, exact);
  }
}
if (shardTurn(10)) {
  // A variable is not the integer 0, so y = 0 at runtime still runs the scaled
  // circuit. √(b²) is 0 there, k is 1, and both modes are that gate result.
  const bounds = [
    { x: c(5), y: c(0) },
    { x: c(0), y: c(0) },
  ];
  for (const source of ["x-y", "x+y"]) {
    const node = compileExpression(source, { x: V("x"), y: V("y") });
    const length = circuitStats(node).rpnLength;
    if (node === V("x") || length < BigInt(500)) {
      failed += 1;
      console.log("FAIL variable zero left the scaled circuit", source, length.toString());
    }
    for (const env of bounds) {
      const got = evaluateReport(node, env);
      const exact = exactReport(node, env);
      const want = env.x;
      // The scaled gates agree through 70 digits. The last places are dust, not a dropped term.
      const exactOk = exact.singular === null && exactClose(exact.value, want.re, want.im, 70);
      if (got.singular || !close(got.value, want, 1e-8) || !exactOk) {
        failed += 1;
        console.log("FAIL variable zero", source, env, got.value, got.singular, formatExact(exact.value), exact.singular);
      }
    }
  }
}
if (shardTurn(11)) {
  const tiny = [
    ["1e-100-3e-100", c(-2e-100)],
    ["0-1e-90", c(-1e-90)],
  ] as const;
  for (const [source, want] of tiny) {
    const node = compileExpression(source, {});
    const got = evaluate(node);
    const exact = exactToFloat(exactEvaluate(node));
    if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9)) {
      failed += 1;
      console.log("FAIL tiny difference", source, got, exact, want);
    }
  }
  for (const source of ["1-1e-72", "1-1e-80"]) {
    const text = formatExact(exactEvaluate(compileExpression(source, {})));
    if (text === "1" || !text.includes("999")) {
      failed += 1;
      console.log("FAIL exact residual digits", source, text);
    }
  }
  const subnormal = compileExpression("5e-324", {});
  const sub = evaluateReport(subnormal);
  const subExact = exactToFloat(exactEvaluate(subnormal));
  if (!sub.underflowed || sub.value.re !== 0 || underflowDisclosure(sub.value, sub.underflowed) !== "underflowed to 0; not a mathematical zero") {
    failed += 1;
    console.log("FAIL subnormal disclosure", sub.value, sub.underflowed);
  }
  if (!beyondFloatBound(sub.value, subExact)) {
    failed += 1;
    console.log("FAIL subnormal exact disagrees and must replace the float 0", sub.value, subExact);
  }
  const computing = exactScreen("computing");
  const cancelled = exactScreen("cancelled", "2.718");
  const filled = exactScreen("ready", "2.718281828");
  if (computing.text !== "computing" || computing.text.includes("2.718") || cancelled.text !== "—" || cancelled.note !== "cancelled" || filled.text !== "2.718281828" || filled.note !== null) {
    failed += 1;
    console.log("FAIL exact screen", computing, cancelled, filled);
  }
  const pi = Math.PI;
  const halfTurn = (got: { re: number; im: number }, want: { re: number; im: number }) => Object.is(got.re, want.re) && Object.is(got.im, want.im);
  for (const sign of [1, -1]) {
    const neg = cexp(c(Number.NEGATIVE_INFINITY, sign * pi));
    const pos = cexp(c(Number.POSITIVE_INFINITY, sign * pi));
    if (!halfTurn(neg, c(-0, -0)) || !halfTurn(pos, c(Number.NEGATIVE_INFINITY, 0))) {
      failed += 1;
      console.log("FAIL half-turn exponential", sign, neg, pos);
    }
  }
  const lnNegInf = clog(c(Number.NEGATIVE_INFINITY));
  const lnNegZero = clog(c(-0));
  if (!Object.is(lnNegInf.im, -pi) || lnNegInf.re !== Number.POSITIVE_INFINITY || !Object.is(lnNegZero.im, -pi) || lnNegZero.re !== Number.NEGATIVE_INFINITY) {
    failed += 1;
    console.log("FAIL lower-bank log", lnNegInf, lnNegZero);
  }
  for (const source of ["ln(-0)", "ln(-inf)"]) {
    const composed = evaluate(compileExpression(source, {}));
    const real = source === "ln(-0)" ? Number.NEGATIVE_INFINITY : Number.POSITIVE_INFINITY;
    if (!Object.is(composed.im, pi) || composed.re !== real) {
      failed += 1;
      console.log("FAIL composed log keeps +π", source, composed);
    }
  }
  for (const source of ["sqrt(0)", "sqrt(-0)"]) {
    const node = compileExpression(source, {});
    const got = evaluate(node);
    const exact = exactEvaluate(node);
    const wantRe = source === "sqrt(-0)" ? -0 : 0;
    if (!Object.is(got.re, wantRe) || got.im !== 0 || !exact.re.eq(0) || !exact.im.eq(0)) {
      failed += 1;
      console.log("FAIL sqrt zero", source, got, formatExact(exact));
    }
    if (source === "sqrt(-0)" && !exact.re.isNegative()) {
      failed += 1;
      console.log("FAIL sqrt(-0) lost its sign", formatExact(exact));
    }
  }
  const tinyY = [c(0), c(-0), c(Number.MIN_VALUE), c(-Number.MIN_VALUE)];
  for (const source of ["x-y", "x+y"]) {
    const node = compileExpression(source, { x: V("x"), y: V("y") });
    for (const y of tinyY) {
      const env = { x: c(5), y };
      const got = evaluate(node, env);
      const exact = exactToFloat(exactEvaluate(node, env));
      const want = source === "x-y" ? c(5 - y.re, -y.im) : c(5 + y.re, y.im);
      if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9)) {
        failed += 1;
        console.log("FAIL variable tiny y", source, y, got, exact, want);
      }
    }
    const seen = evaluate(node, { x: c(0), y: c(1e-300) });
    const opposite = evaluate(node, { x: c(0), y: c(-1e-300) });
    const flipped = source === "x-y" ? seen.re < 0 && opposite.re > 0 : seen.re > 0 && opposite.re < 0;
    if (!flipped) {
      failed += 1;
      console.log("FAIL sign mutation", source, seen, opposite);
    }
    const subnormal = evaluateReport(node, { x: c(0), y: c(Number.MIN_VALUE) });
    const subExact = exactToFloat(exactEvaluate(node, { x: c(0), y: c(Number.MIN_VALUE) }));
    const subSigned = source === "x-y" ? subnormal.value.re < 0 : subnormal.value.re > 0;
    const bothZero = subnormal.value.re === 0 && subExact.re === 0;
    if (!subSigned && !subnormal.underflowed && !beyondFloatBound(subnormal.value, subExact) && !bothZero) {
      failed += 1;
      console.log("FAIL subnormal sign", source, subnormal.value, subExact, subnormal.underflowed);
    }
  }
  const sqrtZero = evaluate(compileExpression("sqrt(0)", {}));
  const sqrtNegZero = evaluate(compileExpression("sqrt(-0)", {}));
  if (Object.is(sqrtZero.re, sqrtNegZero.re)) {
    failed += 1;
    console.log("FAIL sqrt sign mutation", sqrtZero, sqrtNegZero);
  }
  if (beyondFloatBound(c(0), c(1e-90)) !== true || beyondFloatBound(c(1), c(1)) !== false || beyondFloatBound(c(1), c(1 + 1e-12)) !== false || beyondFloatBound(c(1), c(1 + 1e-6)) !== true) {
    failed += 1;
    console.log("FAIL float bound");
  }
}
const asinhCases: Array<[string, number]> = [
  ["asinh(0.5-3)", Math.asinh(-2.5)],
  ["asinh(-sqrt(2))", Math.asinh(-Math.SQRT2)],
  ["asinh(cos(3))", Math.asinh(Math.cos(3))],
  ["asinh(-2)", Math.asinh(-2)],
  ["asinh(0)", 0],
];
for (const [source, want] of asinhCases) {
  const got = evaluate(compileExpression(source, {}));
  if (!close(got, c(want), 1e-8) || Math.abs(got.im) > 1e-8) {
    failed += 1;
    console.log("FAIL asinh", source, got);
  }
}
if (shardTurn(12)) {
  const negative = evaluate(tArsinh(V("x")), { x: c(-2) });
  const zero = evaluate(tArsinh(V("x")), { x: c(0) });
  if (!close(negative, c(Math.asinh(-2)), 1e-8) || !close(zero, c(0), 0)) {
    failed += 1;
    console.log("FAIL variable asinh", negative, zero);
  }
}
const bigSub = evaluate(compileExpression("2-1e8*i", {}));
if (!close(bigSub, c(2, -1e8), 1e-6)) {
  failed += 1;
  console.log("FAIL 2-1e8 i", bigSub);
}
if (!isPure(literalNode("1e-6")) || !isPure(literalNode("2.5E-3")) || !isPure(literalNode("1.5e20")) || isPure(literalNode("-0"))) {
  failed += 1;
  console.log("FAIL impure typed literal");
}
if (!Number.isNaN(cmul(c(0), c(Infinity)).re) || !Number.isNaN(cdiv(c(NaN), c(0)).re)) {
  failed += 1;
  console.log("FAIL 0·∞ or NaN/0");
}
const tangent = ctan(c(1, 800));
if (!close(tangent, c(0, 1), 1e-6)) {
  failed += 1;
  console.log("FAIL tan(1+800i)", tangent);
}
const deep = `${"(".repeat(10000)}1${")".repeat(10000)}`;
if (evaluate(compileExpression(deep, {})).re !== 1) {
  failed += 1;
  console.log("FAIL 10000 parentheses");
}
const many = Array.from({ length: 4000 }, () => "1").join("+");
if (!close(evaluate(compileExpression(many, {})), c(4000), 1e-8)) {
  failed += 1;
  console.log("FAIL long sum");
}
const sinFloat = csin(c(Math.PI / 6));
if (!close(sinFloat, c(0.5), 1e-15) || Math.abs(sinFloat.im) > 1e-15) {
  failed += 1;
  console.log("FAIL float sin(pi/6)", sinFloat);
}

function conformance(name: string, source: string, want: { re: number; im: number }, singular: string | null = null) {
  const node = compileExpression(source, {});
  const floated = evaluateReport(node);
  const exact = exactReport(node, {}, { maxNodes: 200_000 });
  const ref = referenceExpression(source, {});
  if (!close(floated.value, want, 1e-9) || floated.singular !== singular) {
    failed += 1;
    console.log("FAIL float", name, floated.value, floated.singular);
  }
  if (!exactClose(exact.value, want.re, want.im, 12) || exact.singular !== singular) {
    failed += 1;
    console.log("FAIL exact", name, formatExact(exact.value), exact.singular);
  }
  if (!ref || !close(ref, want, 1e-9)) {
    failed += 1;
    console.log("FAIL reference", name, ref);
  }
}

conformance("ln just below the cut", "ln(-1-1e-15*i)", c(0, -Math.PI));
conformance("0-ln(0)", "0-ln(0)", c(Infinity, 0), SINGULAR_LN0);
if (shardTurn(13)) {
  // Float64 cannot recover a real 2 beside an imaginary 10^16 through exp and ln:
  // one ulp of the angle is already larger than 2. Exact mode still has both.
  const scaledImag = evaluate(compileExpression("2-1e16*i", {}));
  if (!Number.isFinite(scaledImag.im) || Math.abs(scaledImag.im + 1e16) / 1e16 > 1e-6) {
    failed += 1;
    console.log("FAIL 2-1e16i float imaginary part", scaledImag);
  }
}
check("implicit i", evaluate(compileExpression("2-1e16i", {})), evaluate(compileExpression("2-1e16*i", {})), 0);
if (shardTurn(14)) {
  const inf = evaluate(compileExpression("inf", {}));
  if (inf.re !== Infinity || inf.im !== 0) {
    failed += 1;
    console.log("FAIL inf", inf);
  }
}
check("tan(1+800i) juxtaposition", evaluate(compileExpression("tan(1+800i)", {})), c(0, 1), 1e-6);
if (shardTurn(15)) {
  const exact = exactReport(compileExpression("2-1e16*i", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 2, "-1e16", 12)) {
    failed += 1;
    console.log("FAIL exact 2-1e16i", formatExact(exact.value));
  }
}
if (shardTurn(16)) {
  const exact = exactReport(compileExpression("10000000000000001-10000000000000000", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 20)) {
    failed += 1;
    console.log("FAIL exact big integer sub", formatExact(exact.value));
  }
}
check("big integer sub is not the zero program", evaluate(compileExpression("10000000000000001-10000000000000000", {})), c(1), 0);
if (shardTurn(17)) {
  const exact = exactReport(compileExpression("(2^53+1)-2^53", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 12)) {
    failed += 1;
    console.log("FAIL exact 2^53", formatExact(exact.value));
  }
}
if (shardTurn(18)) {
  const exact = exactReport(compileExpression("(1e16+1)-1e16", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 12)) {
    failed += 1;
    console.log("FAIL exact 1e16+1-1e16", formatExact(exact.value));
  }
}
if (shardTurn(19)) {
  const exact = exactReport(compileExpression("(1+1e-20)-1", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, "1e-20", 0, 12)) {
    failed += 1;
    console.log("FAIL exact (1+1e-20)-1", formatExact(exact.value));
  }
}
if (shardTurn(20)) {
  const node = compileExpression("1-((1e9+pi+1e-10)-1e9)*i", {});
  const exact = exactReport(node, {}, { maxNodes: 400_000 });
  if (exact.value.im.gt(0) || !exactClose(exact.value, 1, exact.value.im, 8)) {
    failed += 1;
    console.log("FAIL exact near-pi sign", formatExact(exact.value));
  }
  if (!close(evaluate(node), c(1, -Math.PI), 1e-4)) {
    failed += 1;
    console.log("FAIL float near-pi", evaluate(node));
  }
}
if (shardTurn(21)) {
  const exact = exactReport(compileExpression("(1e17+pi)-1e17", {}), {}, { maxNodes: 400_000 });
  if (!exactClose(exact.value, Math.PI, 0, 10)) {
    failed += 1;
    console.log("FAIL exact (1e17+pi)-1e17", formatExact(exact.value));
  }
}
if (shardTurn(22)) {
  const variable = tSub(literalNode("1"), V("x"));
  const exact = exactReport(variable, { x: c(1e20) }, { maxNodes: 400_000 });
  if (exact.value.re.plus("99999999999999999999").abs().gt("1e-6")) {
    failed += 1;
    console.log("FAIL variable 1-1e20", exact.value.re.toString());
  }
}
if (shardTurn(23)) {
  const exact = exactReport(compileExpression("1e308+1e308", {}), {}, { maxNodes: 400_000 });
  if (!exactClose(exact.value, "2e308", 0, 12)) {
    failed += 1;
    console.log("FAIL exact 1e308+1e308", formatExact(exact.value));
  }
  const avg = exactReport(compileExpression("avg(1e308,1e308)", {}), {}, { maxNodes: 400_000 });
  if (!exactClose(avg.value, "1e308", 0, 12)) {
    failed += 1;
    console.log("FAIL exact avg 1e308", formatExact(avg.value));
  }
}
check("exp(800)/exp(799)", evaluate(compileExpression("exp(800)/exp(799)", {})), c(Math.E), 1e-12);
check("tan(1+800i)", evaluate(compileExpression("tan(1+800*i)", {})), c(0, 1), 1e-6);
check("tan(1-800i)", evaluate(compileExpression("tan(1-800*i)", {})), c(0, -1), 1e-6);
check("tan(1-i)", evaluate(compileExpression("tan(1-i)", {})), ctan(c(1, -1)), 1e-6);
check("tan(1+i)", evaluate(compileExpression("tan(1+i)", {})), ctan(c(1, 1)), 1e-6);
if (!close(ctan(c(1, -1)), c(0.27175258531951174, -1.0839233273386948), 1e-9)) {
  failed += 1;
  console.log("FAIL ctan negative imag", ctan(c(1, -1)));
}
if (shardTurn(24)) {
  const asinh = evaluate(tArsinh(V("x")), { x: c(1000) });
  if (!close(asinh, c(Math.asinh(1000)), 1e-9)) {
    failed += 1;
    console.log("FAIL variable asinh(1000)", asinh);
  }
}
if (shardTurn(25)) {
  let threw = false;
  try {
    literalNode("1e400000000");
  } catch (err) {
    threw = err instanceof EmlError && /exponent is too large/i.test(err.message);
  }
  if (!threw) {
    failed += 1;
    console.log("FAIL 1e400 message");
  }
}
if (!close(evaluate(literalNode("5.")), c(5), 0)) {
  failed += 1;
  console.log("FAIL literal 5.", evaluate(literalNode("5.")));
}
const twentyK = Array.from({ length: 20_000 }, () => "1").join("+");
if (shardTurn(26)) {
  const summed = compileExpression(twentyK, {});
  const sum = evaluateReport(summed, {}, { maxNodes: 2_000_000 });
  if (!close(sum.value, c(20000), 1e-12) || sum.value.im !== 0) {
    failed += 1;
    console.log("FAIL 20000 ones", sum.value, sum.singular, rangeOf(summed).int?.toString(), provenInteger(summed)?.toString(), summed.type);
  }
}

if (shardTurn(27)) {
  let total = BigInt(0);
  for (let n = 0; n <= 12; n += 1) total += catalan(n);
  for (let i = BigInt(0); i < total; i += BigInt(1)) {
    const rpn = unrankRpn(i);
    if (rankRpn(rpn) !== i || !isProgram(rpn)) {
      failed += 1;
      console.log("FAIL program round trip", i.toString(), rpn);
      break;
    }
    const node = unrankProgram(i);
    if (rankProgram(node) !== i || unrankProgram(i) !== node) {
      failed += 1;
      console.log("FAIL node round trip", i.toString());
      break;
    }
  }
}
if (shardTurn(28)) {
  const first = `${"1".repeat(1001)}${"E".repeat(1000)}`;
  const index = rankRpn(first);
  const last = unrankRpn(index + catalan(1000) - BigInt(1));
  if (unrankRpn(index) !== first || rankRpn(last) !== index + catalan(1000) - BigInt(1)) {
    failed += 1;
    console.log("FAIL n=1000 round trip");
  }
  const node = unrankProgram(index);
  if (rankProgram(node) !== index || unrankProgram(index) !== node) {
    failed += 1;
    console.log("FAIL n=1000 node round trip");
  }
  let tower: Node = ONE;
  for (let i = 0; i < 20; i += 1) tower = E(tower, tower);
  if (rankProgram(tower) !== null || !programNumberText(tower)?.startsWith("program ≈ 2^")) {
    failed += 1;
    console.log("FAIL large program number", programNumberText(tower));
  }
}
if (approximateIndexBits(BigInt(10)) !== BigInt(14)) {
  failed += 1;
  console.log("FAIL approximate bits", approximateIndexBits(BigInt(10)));
}
const numbered: Array<[bigint, ReturnType<typeof c>]> = [
  [BigInt(1), c(Math.E)],
  [BigInt(5), c(0)],
  [BigInt(242), c(-1)],
  [BigInt(2431), c(2)],
  [BigInt(98362), c(-2)],
];
for (const [index, value] of numbered) {
  const node = unrankProgram(index);
  if (!close(evaluate(node), value, 1e-9) || rankProgram(node) !== index) {
    failed += 1;
    console.log("FAIL known program", index.toString(), evaluate(node));
  }
}
if (stepProgram(BigInt(0), -1) !== BigInt(0) || stepProgram(BigInt(5), 1) !== BigInt(6) || stepProgram(BigInt(5), -1) !== BigInt(4)) {
  failed += 1;
  console.log("FAIL stepProgram");
}
if (rankProgram(V("x")) !== null || rankProgram(E(V("y"), ONE)) !== null || rankProgram(input(c(3), "3")) !== null) {
  failed += 1;
  console.log("FAIL rank of a non-constant");
}
for (let n = 0; n <= 7; n += 1) {
  const count = catalan(n);
  let begin = BigInt(0);
  for (let m = 0; m < n; m += 1) begin += catalan(m);
  for (let k = BigInt(0); k < count; k += BigInt(1)) {
    const rpn = unrankRpn(begin + k);
    const turns: string[] = [];
    for (let i = 0; i < rpn.length; i += 1) turns.push(rpn.slice(i) + rpn.slice(0, i));
    const valid = turns.filter(isProgram);
    if (valid.length !== 1 || valid[0] !== rpn || turns.some((turn) => rotateToProgram(turn) !== rpn)) {
      failed += 1;
      console.log("FAIL rotation", rpn);
      n = 8;
      break;
    }
  }
}

if (shardTurn(29)) {
  const short = previewPresses("110");
  const exact = previewPresses("1".repeat(30));
  const over = previewPresses("1".repeat(31));
  if (short.preview !== "110" || short.truncated || short.presses !== BigInt(3)) {
    failed += 1;
    console.log("FAIL short presses", short);
  }
  if (exact.preview !== "1".repeat(30) || exact.truncated || exact.presses !== BigInt(30)) {
    failed += 1;
    console.log("FAIL 30 presses", exact);
  }
  if (over.preview !== `${"1".repeat(30)}…` || !over.truncated || over.presses !== BigInt(31)) {
    failed += 1;
    console.log("FAIL 31 presses", over);
  }
  if (encodePresses(["1", "1", "E"]) !== "110" || encodePresses(["1", "x", "E", "y"]) !== "1x0y" || encodePresses(["2"]) !== null) {
    failed += 1;
    console.log("FAIL press alphabet");
  }
  const emlPress = pressPreviewForNode(E(ONE, ONE));
  const named = pressPreviewForNode(E(V("x"), ONE));
  if (!emlPress || emlPress.full !== "110" || emlPress.usesVariables) {
    failed += 1;
    console.log("FAIL e presses", emlPress);
  }
  if (!named || named.full !== "x10" || !named.usesVariables) {
    failed += 1;
    console.log("FAIL variable presses", named);
  }
  if (pressPreviewForNode(input(c(3), "3")) !== null) {
    failed += 1;
    console.log("FAIL typed press string");
  }
  let wide: Node = ONE;
  for (let i = 0; i < 15; i += 1) wide = E(wide, ONE);
  const widePress = pressPreviewForNode(wide);
  if (!widePress || widePress.presses !== BigInt(31) || !widePress.truncated || widePress.preview.length !== 31 || !widePress.preview.endsWith("…")) {
    failed += 1;
    console.log("FAIL wide press preview", widePress);
  }
  let shared: Node = ONE;
  for (let i = 0; i < 14; i += 1) shared = E(shared, shared);
  const over20k = pressPreviewForNode(shared);
  if (!over20k || over20k.presses !== (BigInt(1) << BigInt(15)) - BigInt(1) || over20k.copyable || over20k.presses <= BigInt(20_000)) {
    failed += 1;
    console.log("FAIL press count past 20000", over20k?.presses.toString());
  }
  let tower61: Node = ONE;
  for (let i = 0; i < 61; i += 1) tower61 = E(tower61, tower61);
  const huge = pressPreviewForNode(tower61);
  const hugeCount = (BigInt(1) << BigInt(62)) - BigInt(1);
  if (!huge || huge.presses !== hugeCount || huge.copyable || huge.presses === BigInt(Number.MAX_SAFE_INTEGER)) {
    failed += 1;
    console.log("FAIL press count past 2^53", huge?.presses.toString());
  }
  const hugeNumber = programNumberText(tower61);
  const bits = /2\^(\d+)/.exec(hugeNumber ?? "");
  if (!bits || BigInt(bits[1] ?? "0") < BigInt(2) ** BigInt(60)) {
    failed += 1;
    console.log("FAIL tower index bits", hugeNumber);
  }
  const reason = unnumberedReason(tower61);
  if (!reason || !reason.includes("past 1000") || !reason.includes("10^")) {
    failed += 1;
    console.log("FAIL unnumbered reason", reason);
  }
}

if (shardTurn(30)) {
  const records: Record<string, string> = {
    e: "1",
    "0": "5",
    "-inf": "24",
    "-1": "242",
    "2": "2431",
    "-2": "98362",
    ipi: "7948",
    ln2: "85587",
    "3": "1086729",
    "-1/2": "1131653",
    "1/2": "2246702",
    "1/2-strict": "8107003",
    sqrt2: "1432982456885549",
    i: "99292101684726",
    pi: "3125315318547434611379164",
  };
  for (const [id, indexText] of Object.entries(records)) {
    const index = BigInt(indexText);
    const node = programNode(id);
    if (rankProgram(node) !== index || unrankProgram(index) !== node) {
      failed += 1;
      console.log("FAIL record number", id, rankProgram(node)?.toString());
      break;
    }
    if (id === "pi") {
      const digits = programIndexDigits(node);
      const shown = programNumberText(node);
      if (digits !== indexText || shown !== `program #${indexText.slice(0, 4)}…${indexText.slice(-4)} (${indexText.length} digits)`) {
        failed += 1;
        console.log("FAIL pi number text", digits, shown);
      }
    }
  }
  if (rankRpn("1") !== BigInt(0)) {
    failed += 1;
    console.log("FAIL program 0");
  }
}

if (shardTurn(31)) {
  const copied = pressPreviewForNode(unrankProgram(BigInt(1)));
  const pasted = copied ? parseProgramInput(copied.full) : null;
  const roundTrip = pasted && pasted.kind === "word" ? rankProgram(nodeFromRpn(pasted.word.split(""))) : null;
  if (!copied || copied.full !== "110" || pasted?.kind !== "word" || pasted.word !== "11E" || roundTrip !== BigInt(1)) {
    failed += 1;
    console.log("FAIL copy paste round trip", copied?.full, pasted, roundTrip?.toString());
  }
  const one = parseProgramInput("1");
  const hashOne = parseProgramInput("#1");
  const hash110 = parseProgramInput("#110");
  const wordE = parseProgramInput("1E1");
  const wordLower = parseProgramInput("1e1");
  const spacedWord = parseProgramInput("1 1 E");
  const variable = parseProgramInput("x10");
  if (one.kind !== "word" || rankRpn(one.word) !== BigInt(0)) {
    failed += 1;
    console.log("FAIL press 1 is program 0", one);
  }
  if (hashOne.kind !== "index" || hashOne.index !== BigInt(1) || hash110.kind !== "index" || hash110.index !== BigInt(110)) {
    failed += 1;
    console.log("FAIL hash numbers", hashOne, hash110);
  }
  if (wordE.kind !== "word" || wordE.word !== "11E" || wordE.rotatedFrom !== "1E1" || wordLower.kind !== "word" || wordLower.word !== "11E" || wordLower.rotatedFrom !== "1E1" || spacedWord.kind !== "word" || spacedWord.word !== "11E" || spacedWord.rotatedFrom !== null) {
    failed += 1;
    console.log("FAIL word input", wordE, wordLower, spacedWord);
  }
  const turned = parseProgramInput("E11");
  const turnedPress = parseProgramInput("011");
  if (turned.kind !== "word" || turned.word !== "11E" || turned.rotatedFrom !== "E11" || turnedPress.kind !== "word" || turnedPress.word !== "11E" || turnedPress.rotatedFrom !== "011") {
    failed += 1;
    console.log("FAIL rotated word", turned, turnedPress);
  }
  for (const [text, needle] of [["xE", "two values"], ["xy", "one value"], ["Exy", "two values"]] as const) {
    let message = "";
    try {
      parseProgramInput(text);
    } catch (err) {
      message = err instanceof Error ? err.message : "";
    }
    if (!message.includes(needle) || /missing a value|did not leave one value/i.test(message)) {
      failed += 1;
      console.log("FAIL variable word", text, message);
    }
  }
  if (variable.kind !== "word" || variable.word !== "x1E" || nodeFromRpn(variable.word.split("")) !== E(V("x"), ONE)) {
    failed += 1;
    console.log("FAIL variable presses", variable);
  }
  for (const text of ["1 2", "#1 2", "12 0"]) {
    let message = "";
    try {
      parseProgramInput(text);
    } catch (err) {
      message = err instanceof Error ? err.message : "";
    }
    if (!/space/i.test(message)) {
      failed += 1;
      console.log("FAIL spaces in a number", text, message);
    }
  }
  for (const text of ["-5", "#-5"]) {
    let message = "";
    try {
      parseProgramInput(text);
    } catch (err) {
      message = err instanceof Error ? err.message : "";
    }
    if (!/negative/i.test(message)) {
      failed += 1;
      console.log("FAIL negative program", text, message);
    }
  }
  let bare = "";
  try {
    parseProgramInput("12");
  } catch (err) {
    bare = err instanceof Error ? err.message : "";
  }
  if (!bare.includes("#")) {
    failed += 1;
    console.log("FAIL bare digits", bare);
  }
  let tooBig = "";
  try {
    unrankProgram(BigInt(10) ** BigInt(1000));
  } catch (err) {
    tooBig = err instanceof Error ? err.message : "";
  }
  if (!tooBig.includes("1000 gates") || !tooBig.includes("10^1000")) {
    failed += 1;
    console.log("FAIL gate limit message", tooBig);
  }
}

if (shardTurn(32)) {
  const near = unrankProgram(BigInt(431));
  const report = evaluateReport(near);
  // Guard digits past 240. This overflowed word then agrees with −1, so the
  // 240-digit check does not reject it. The float overflow flag does.
  const exact = exactValueAt(near, 280);
  if (!report.overflowed || !close(report.value, c(-1), 1e-9) || report.singular !== null) {
    failed += 1;
    console.log("FAIL #431 overflow flag", report);
  }
  if (!acceptsConstantValue(exact, -1, 0) || acceptsConstantProgram(near, -1, 0)) {
    failed += 1;
    console.log("FAIL #431 golf near-miss", acceptsConstantValue(exact, -1, 0), acceptsConstantProgram(near, -1, 0));
  }
  const minus = unrankProgram(BigInt(242));
  const minusReport = evaluateReport(minus);
  if (minusReport.overflowed || minusReport.underflowed || !acceptsConstantProgram(minus, -1, 0)) {
    failed += 1;
    console.log("FAIL real -1 still accepted", minusReport.overflowed, minusReport.underflowed);
  }
  const underNode = unrankProgram(BigInt(5884));
  const underWord = rpnTokens(underNode, 40)?.join("") ?? "";
  const underReport = evaluateReport(underNode);
  const underCoarse = exactValueAt(underNode, 40);
  if (underWord !== "11E111E1E1EEE1E11EE" || !underReport.underflowed || underReport.overflowed || underReport.value.re !== -1 || underReport.value.im !== 0) {
    failed += 1;
    console.log("FAIL #5884 underflow", underWord, underReport);
  }
  if (!exactClose(underCoarse, -1, 0, 12) || acceptsConstantProgram(underNode, -1, 0)) {
    failed += 1;
    console.log("FAIL #5884 golf near-miss", exactClose(underCoarse, -1, 0, 12), acceptsConstantProgram(underNode, -1, 0));
  }
  const expOfPole = evaluateReport(E(input(c(-Infinity), "−∞"), ONE));
  if (expOfPole.underflowed || expOfPole.value.re !== 0 || !expUnderflows(c(-800)) || expUnderflows(c(-Infinity)) || expUnderflows(c(0))) {
    failed += 1;
    console.log("FAIL ln 0 is not underflow", expOfPole, expUnderflows(c(-800)), expUnderflows(c(-Infinity)));
  }
  const half = programNode("1/2");
  if (!evaluateReport(half).touchedLn0 || evaluateReport(half).overflowed) {
    failed += 1;
    console.log("FAIL ln 0 is not overflow");
  }
}

if (close(c(8e-12), c(1e-12), 1e-6)) {
  failed += 1;
  console.log("FAIL close accepts a 700% error near 1e-12");
}

if (shardTurn(33)) {
  const circuit = evaluate(compileExpression("1/(-0)", {}));
  const ref = referenceExpression("1/(-0)", {});
  if (circuit.re !== -Infinity || ref?.re !== -Infinity || circuit.im !== 0 || ref?.im !== 0) {
    failed += 1;
    console.log("FAIL 1/(-0) agreement", circuit, ref);
  }
}

if (shardTurn(34)) {
  const typed = evaluateReport(compileExpression("0*inf", {}));
  const typedExact = exactReport(compileExpression("0*inf", {}), {}, { maxNodes: 20_000 });
  if (typed.singular !== SINGULAR_INDET || !Number.isNaN(typed.value.re) || !Number.isNaN(typed.value.im)) {
    failed += 1;
    console.log("FAIL typed 0*inf", typed);
  }
  if (typedExact.singular !== SINGULAR_INDET || !typedExact.value.re.isNaN()) {
    failed += 1;
    console.log("FAIL exact typed 0*inf", formatExact(typedExact.value), typedExact.singular);
  }
  for (const source of ["ln(0)*0", "0*ln(0)", "ln(0)*(1-1)"]) {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, { maxNodes: 20_000 });
    const ex = exactReport(node, {}, { maxNodes: 20_000 });
    const text = formatExact(ex.value).replace(/\u200b/g, "");
    if (
      hw.singular === null ||
      !Number.isNaN(hw.value.re) ||
      !Number.isNaN(hw.value.im) ||
      ex.singular !== SINGULAR_INDET ||
      !ex.value.re.isNaN() ||
      !ex.value.im.isNaN() ||
      text === "0" ||
      text === "−0"
    ) {
      failed += 1;
      console.log("FAIL 0 times ln 0", source, hw.singular, hw.value, ex.singular, text);
    } else {
      console.log("indet", source, text, ex.singular);
    }
  }
  const gap = compileExpression("inf-inf", {});
  const gapReport = evaluateReport(gap);
  const gapExact = exactReport(gap, {}, { maxNodes: 20_000 });
  const extended = [
    ["ln(0)*2", "−∞"],
    ["ln(0)*(-2)", "∞"],
    ["(-2)*ln(0)", "∞"],
    ["2*ln(0)", "−∞"],
    ["ln(0)*0", "undefined"],
    ["sin(inf)", "undefined"],
    ["sin(ln(0))", "undefined"],
    ["cos(inf)", "undefined"],
    ["cos(ln(0))", "undefined"],
    ["sin((inf+1)-1)", "undefined"],
    ["tan(inf)", "undefined"],
    ["tan(ln(0))", "undefined"],
    ["sqrt(ln(0))", "∞i"],
    ["ln(0)*i", "−∞i"],
    ["inf*i", "∞i"],
    ["i*inf", "∞i"],
    ["i*ln(0)", "−∞i"],
    ["sqrt(inf)", "∞"],
    ["sqrt(ln(0))^2", "−∞"],
    ["(-inf)*i", "−∞i"],
    ["i*(-inf)", "−∞i"],
    ["-(sqrt(ln(0)))", "−∞i"],
    ["(inf*i)*i", "−∞"],
    ["ln(0)*i*i", "∞"],
    ["sqrt(inf)^2", "∞"],
    ["1/(inf*i)", "0"],
    ["(inf*i)*(inf*i)", "−∞"],
    ["inf*(inf*i)", "∞i"],
    ["(-inf)*(-inf)", "∞"],
    ["inf*(1+i)", "unverified"],
    ["(inf*i)^3", "−∞i"],
    ["(inf*i)^4", "∞"],
    ["(inf*i)^5", "∞i"],
    ["(inf*i)^-1", "0"],
    ["(inf*i)^-2", "0"],
    ["(-inf)^3", "−∞"],
    ["(-inf)^2", "∞"],
    ["(inf*i)^0.5", "unverified"],
    ["ln(0)-1", "unverified"],
    ["ln(0)+i", "unverified"],
    ["(inf*i)/2", "unverified"],
    ["ln(ln(0)*i)", "unverified"],
    ["ln(0)+0", "−∞"],
    ["ln(0)-0", "−∞"],
    ["ln(0)+1", "unverified"],
    ["ln(0)*i+1", "unverified"],
    ["inf+1", "unverified"],
    ["1+inf", "unverified"],
    ["1+2+inf", "unverified"],
    ["inf+inf", "unverified"],
    ["1+ln(0)", "unverified"],
    ["ln(0)+ln(0)", "unverified"],
    ["1+inf*i", "unverified"],
    ["inf-ln(0)", "∞"],
    ["inf*i+0", "∞i"],
    ["sqrt(ln(0))+0", "∞i"],
    ["ln(0)*i-0", "−∞i"],
    ["sqrt(inf*i)", "unverified"],
    ["ln(inf*i)", "unverified"],
    ["(inf*i)/i", "unverified"],
    ["ln(ln(0))", "∞ + 3.14159265359i"],
    ["exp(800)-exp(800)", "0"],
    ["exp(800)-exp(800)+1", "1"],
    ["exp(1000)/exp(1000)", "1"],
  ] as const;
  for (const [source, want] of extended) {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, { maxNodes: 200_000 });
    const ex = exactReport(node, {}, { maxNodes: 200_000 });
    const floatText = formatC(hw.value);
    const exactText = formatExact(ex.value).replace(/\u200b/g, "");
    const flagged = want === "unverified";
    const floatOk = flagged ? hw.unverified === true && floatText !== "∞" : floatText === want;
    const exactOk = flagged ? ex.unverified === true && exactText !== "∞" : exactText === want;
    if (!floatOk || !exactOk || (!flagged && floatText !== exactText)) {
      failed += 1;
      console.log("FAIL extended value", source, floatText, exactText, hw.singular, ex.singular, hw.unverified, ex.unverified);
    }
  }
  // The in-process rows never pack. The screen's exact worker evaluates the packed circuit.
  const freshAngles = ["sin(inf)", "cos(inf)", "sin(ln(0))", "cos(ln(0))", "tan(inf)", "tan(ln(0))"];
  const freshDirected = [
    ["sqrt(ln(0))", "∞i"],
    ["ln(0)*i", "−∞i"],
    ["inf*i", "∞i"],
    ["i*inf", "∞i"],
    ["i*ln(0)", "−∞i"],
    ["sqrt(inf)", "∞"],
    ["sqrt(ln(0))^2", "−∞"],
    ["(-inf)*i", "−∞i"],
    ["i*(-inf)", "−∞i"],
    ["-(sqrt(ln(0)))", "−∞i"],
    ["(inf*i)*i", "−∞"],
    ["ln(0)*i*i", "∞"],
    ["sqrt(inf)^2", "∞"],
    ["1/(inf*i)", "0"],
    ["(inf*i)*(inf*i)", "−∞"],
    ["inf*(inf*i)", "∞i"],
    ["(-inf)*(-inf)", "∞"],
    ["inf*(1+i)", "unverified"],
    ["(inf*i)^3", "−∞i"],
    ["(inf*i)^4", "∞"],
    ["(inf*i)^5", "∞i"],
    ["(inf*i)^-1", "0"],
    ["(inf*i)^-2", "0"],
    ["(-inf)^3", "−∞"],
    ["(-inf)^2", "∞"],
    ["(inf*i)^0.5", "unverified"],
    ["ln(0)-1", "unverified"],
    ["ln(0)+i", "unverified"],
    ["(inf*i)/2", "unverified"],
    ["ln(ln(0)*i)", "unverified"],
    ["ln(0)+0", "−∞"],
    ["ln(0)-0", "−∞"],
    ["ln(0)+1", "unverified"],
    ["ln(0)*i+1", "unverified"],
    ["inf+1", "unverified"],
    ["1+inf", "unverified"],
    ["1+2+inf", "unverified"],
    ["inf+inf", "unverified"],
    ["1+ln(0)", "unverified"],
    ["ln(0)+ln(0)", "unverified"],
    ["1+inf*i", "unverified"],
    ["inf-ln(0)", "∞"],
    ["inf*i+0", "∞i"],
    ["sqrt(ln(0))+0", "∞i"],
    ["ln(0)*i-0", "−∞i"],
    ["sqrt(inf*i)", "unverified"],
    ["ln(inf*i)", "unverified"],
    ["(inf*i)/i", "unverified"],
    ["ln(ln(0))", "∞ + 3.14159265359i"],
    ["exp(800)-exp(800)", "0"],
    ["exp(800)-exp(800)+1", "1"],
    ["exp(1000)/exp(1000)", "1"],
  ] as const;
  const freshJobs = [...freshAngles, ...freshDirected.map(([source]) => source)].map((source) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root };
  });
  const freshAnglesRun = runTsx("scripts/fresh-exact.ts", JSON.stringify(freshJobs));
  if (freshAnglesRun.status !== 0) {
    failed += 1;
    console.log("FAIL fresh trig infinity", freshAnglesRun.status, freshAnglesRun.stderr);
  } else {
    const rows = JSON.parse(freshAnglesRun.stdout) as Array<{ source: string; text: string; singular: string | null; unverified: boolean }>;
    const directed = new Map<string, string>(freshDirected.map(([source, want]) => [source, want]));
    for (const row of rows) {
      const text = row.text.replace(/\u200b/g, "");
      const want = directed.get(row.source);
      if (want === "unverified") {
        if (!row.unverified || text === "∞") {
          failed += 1;
          console.log("FAIL fresh directed infinity", row.source, text, row.singular, row.unverified);
        }
      } else if (want !== undefined) {
        if (text !== want || row.unverified) {
          failed += 1;
          console.log("FAIL fresh directed infinity", row.source, text, row.singular, row.unverified);
        }
      } else if (text !== "undefined" || row.singular === null) {
        failed += 1;
        console.log("FAIL fresh trig infinity", row.source, text, row.singular);
      }
    }
  }
  // Direct compile is checked in `extended`. The screen packs the same circuit
  // for the exact worker; unpack here so a packed overflow difference cannot
  // ship a certified −∞.
  for (const [source, want] of [
    ["exp(800)-exp(800)", "0"],
    ["exp(800)-exp(800)+1", "1"],
    ["exp(1000)/exp(1000)", "1"],
  ] as const) {
    const packed = packCircuit(compileExpression(source, {}));
    const rebuilt = unpackCircuit(packed.tokens, packed.root);
    const direct = exactReport(compileExpression(source, {}), {}, { maxNodes: 200_000 });
    const wire = exactReport(rebuilt, {}, { maxNodes: 200_000 });
    const directText = formatExact(direct.value).replace(/\u200b/g, "");
    const wireText = formatExact(wire.value).replace(/\u200b/g, "");
    if (direct.unverified || wire.unverified || directText !== want || wireText !== want) {
      failed += 1;
      console.log("FAIL packed overflow cancel", source, directText, wireText, direct.unverified, wire.unverified);
    }
  }
  if (gap === programNode("0") || gapReport.singular !== SINGULAR_INDET) {
    failed += 1;
    console.log("FAIL inf-inf", gapReport, gap === programNode("0"));
  }
  if (!Number.isNaN(gapReport.value.re) || !gapExact.value.re.isNaN()) {
    failed += 1;
    console.log("FAIL inf-inf value", gapReport.value, formatExact(gapExact.value));
  }
  const powDiff = evaluate(compileExpression("(2^53+1)-2^53", {}));
  if (powDiff.re !== 1 || powDiff.im !== 0) {
    failed += 1;
    console.log("FAIL float (2^53+1)-2^53", powDiff);
  }
  const hugeReal = evaluate(compileExpression("1e300+i", {}));
  const hugeExact = exactEvaluate(compileExpression("1e300+i", {}), {}, { maxNodes: 400_000 });
  // 10^300 is large enough that a unit imaginary is below exact mode's cancellation
  // tolerance after scaling, and float reconstruction does not keep it either.
  if (Math.abs(hugeReal.re - 1e300) / 1e300 > 1e-9 || hugeExact.re.minus("1e300").abs().div("1e300").gt("1e-12")) {
    failed += 1;
    console.log("FAIL 1e300+i", hugeReal, hugeExact.re.toString(), hugeExact.im.toString());
  }
  const overflow = evaluateReport(compileExpression("10^400/7", {}), {}, { maxNodes: 400_000 });
  if (overflow.value.re !== Infinity || !overflow.overflowed) {
    failed += 1;
    console.log("FAIL 10^400/7 overflow", overflow.value, overflow.overflowed, overflow.singular);
  }
  const bigInt = "1234567890123456789012345678901234567890";
  const shown = formatExact(exactEvaluate(compileExpression("9007199254740993", {}), {}, { maxNodes: 200_000 }));
  const shown40 = formatExact(exactEvaluate(compileExpression(bigInt, {}), {}, { maxNodes: 400_000 }));
  if (shown.replace(/\u200b/g, "") !== "9007199254740993" || shown40.replace(/\u200b/g, "") !== bigInt) {
    failed += 1;
    const lit = compileExpression("9007199254740993", {});
    console.log("FAIL exact integer text", shown, shown40, rangeOf(lit).int?.toString(), provenInteger(lit)?.toString());
  }
  const signed = evaluate(literalNode("-0"));
  if (!Object.is(signed.re, -0) || signed.im !== 0) {
    failed += 1;
    console.log("FAIL literal -0", signed);
  }
}

if (shardTurn(35)) {
  const wide = exactEvaluate(compileExpression("1e40+i", {}));
  if (wide.re.toExponential(2) !== "1.00e+40" || wide.im.minus(1).abs().gt("1e-6")) {
    failed += 1;
    console.log("FAIL exact 1e40+i drops the imaginary part", wide.re.toString(), wide.im.toString());
  }
}

if (shardTurn(36)) {
  let history = { past: [] as string[], current: "empty" };
  history = commitHistory(history, "one");
  history = commitHistory(history, "two");
  const queue: Array<() => void> = [];
  queue.push(() => {
    history = undoHistory(history);
  });
  queue.push(() => {
    history = undoHistory(history);
  });
  drainQueue(queue);
  if (history.current !== "empty" || history.past.length !== 0) {
    failed += 1;
    console.log("FAIL queued undo replayed a stale snapshot", history);
  }
  const switched = applyModeSwitch({
    previous: ["old-a", "old-b"],
    recomputed: ["new-a"],
    error: "exact timed out",
    fail: (item, error) => `${item}:${error}`,
  });
  if (switched.error !== "exact timed out" || switched.stack[0] !== "new-a" || switched.stack[1] !== "old-b:exact timed out") {
    failed += 1;
    console.log("FAIL mode switch left an old value", switched);
  }
}

/** Block 37's seeded random sources. The isolate rebuild (block 43) uses them too. */
function fuzzSources(): string[] {
  let seed = 20261115;
  const rand = () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const atoms = ["0", "1", "2", "0.5", "-1", "e", "1e-300", "1e-15", "1e-9", "1e-5", "1e200", "1e300", "-1e200"];
  const bins = ["+", "-", "*", "/"];
  const uns = ["sin", "cos", "exp", "sqrt"];
  const nest = (depth: number): string => {
    const roll = rand();
    if (depth <= 0 || roll < 0.5) return atoms[Math.floor(rand() * atoms.length)] ?? "1";
    if (roll < 0.75) {
      const fn = uns[Math.floor(rand() * uns.length)] ?? "exp";
      return `${fn}(${nest(depth - 1)})`;
    }
    const op = bins[Math.floor(rand() * bins.length)] ?? "+";
    return `(${nest(depth - 1)}${op}${nest(depth - 1)})`;
  };
  return Array.from({ length: 20 }, () => nest(2));
}

if (shardTurn(37)) {
  for (const source of fuzzSources()) {
    try {
      const node = compileExpression(source, {});
      const got = evaluate(node);
      const ref = referenceExpression(source, {});
      const exact = exactToFloat(exactEvaluate(node));
      if (!ref || ![got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite)) continue;
      const huge = source.includes("1e200") || source.includes("1e300");
      const flagged = huge && evaluateReport(node).singular !== null;
      if (!flagged && (!close(got, ref, 1e-4) || !close(exact, ref, 1e-4))) {
        failed += 1;
        console.log("FAIL fuzz", source, got, exact, ref);
      }
    } catch (err) {
      failed += 1;
      console.log("FAIL fuzz threw", source, err);
    }
  }
}

if (shardTurn(38)) {
  const variableCases: Array<[string, Record<string, { re: number; im: number }>, { re: number; im: number }]> = [
    ["x-y", { x: c(1), y: c(0) }, c(1)],
    ["x-y", { x: c(0), y: c(0) }, c(0)],
    ["x+y", { x: c(0), y: c(0) }, c(0)],
    ["asinh(x)", { x: c(-2) }, c(Math.asinh(-2))],
    ["asinh(x)", { x: c(0) }, c(0)],
    ["asinh(x)", { x: c(0, 0.5) }, c(0, Math.PI / 6)],
    ["asinh(x)", { x: c(0, 2) }, casinh(c(0, 2))],
    ["asinh(x)", { x: c(0, -2) }, casinh(c(0, -2))],
    ["asinh(x)", { x: c(0, 3) }, casinh(c(0, 3))],
    ["asinh(x)", { x: c(0, -3) }, casinh(c(0, -3))],
    ["asinh(x)", { x: c(-3, 0.5) }, casinh(c(-3, 0.5))],
    ["arcsin(x)", { x: c(0.5) }, c(Math.asin(0.5))],
    ["arcsin(x)", { x: c(1) }, c(Math.PI / 2)],
    ["hypot(x,y)", { x: c(0), y: c(0) }, c(0)],
    ["avg(x,y)", { x: c(0), y: c(0) }, c(0)],
    ["tan(x)", { x: c(1, 800) }, c(0, 1)],
  ];
  for (const [source, env, want] of variableCases) {
    const node = compileExpression(source, { x: V("x"), y: V("y") });
    const got = evaluate(node, env);
    const exact = exactToFloat(exactEvaluate(node, env));
    if (!close(got, want, 1e-8) || !close(exact, want, 1e-6)) {
      failed += 1;
      console.log("FAIL variable", source, env, got, exact, want);
    }
  }
  const tinyAsinh = [1e-5, -1e-5, 1e-9, -1e-9, 1e-12, -1e-12, 1e-15, -1e-15];
  for (const x of tinyAsinh) {
    const literal = compileExpression(`asinh(${x})`, {});
    const got = evaluate(literal);
    const exact = exactToFloat(exactEvaluate(literal));
    const want = c(Math.asinh(x));
    if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9) || Math.abs(got.im) > 1e-12 * Math.max(Math.abs(x), 1e-30)) {
      failed += 1;
      console.log("FAIL tiny asinh literal", x, got, exact, want);
    }
    const variable = compileExpression("asinh(x)", { x: V("x") });
    const report = evaluateReport(variable, { x: c(x) });
    const exactVar = exactToFloat(exactEvaluate(variable, { x: c(x) }));
    const underflow = Math.abs(x) < 1e-12;
    if (underflow) {
      if (report.singular !== SINGULAR_PRECISION || !relClose(exactVar, want, 1e-9)) {
        failed += 1;
        console.log("FAIL tiny asinh variable", x, report.singular, report.value, exactVar, want);
      }
    } else if (
      report.singular === SINGULAR_PRECISION ||
      !relClose(exactVar, want, 1e-9) ||
      (!relClose(report.value, want, 1e-4) && !beyondFloatBound(report.value, exactVar))
    ) {
      failed += 1;
      console.log("FAIL tiny asinh variable", x, report.singular, report.value, exactVar, want);
    }
  }
  const axisAsinh: Array<[string, { re: number; im: number }]> = [
    ["asinh(2*i)", c(0, 2)],
    ["asinh(-2*i)", c(0, -2)],
    ["asinh(3*i)", c(0, 3)],
    ["asinh(-3*i)", c(0, -3)],
  ];
  for (const [source, z] of axisAsinh) {
    const want = casinh(z);
    const literal = compileExpression(source, {});
    const lit = evaluate(literal);
    const litExact = exactToFloat(exactEvaluate(literal));
    if (!relClose(lit, want, 1e-9) || !relClose(litExact, want, 1e-9)) {
      failed += 1;
      console.log("FAIL imag-axis asinh literal", source, lit, litExact, want);
    }
    const variable = compileExpression("asinh(x)", { x: V("x") });
    const varFloat = evaluate(variable, { x: z });
    const varExact = exactToFloat(exactEvaluate(variable, { x: z }));
    if (!relClose(varFloat, want, 1e-9) || !relClose(varExact, want, 1e-9)) {
      failed += 1;
      console.log("FAIL imag-axis asinh variable", source, varFloat, varExact, want);
    }
  }
  const moderate = evaluateReport(tArsinh(V("x")), { x: c(-2) });
  if (moderate.singular === SINGULAR_PRECISION || !close(moderate.value, c(Math.asinh(-2)), 1e-8)) {
    failed += 1;
    console.log("FAIL asinh(-2) was flagged", moderate.singular, moderate.value);
  }
  for (const [source, want] of [
    ["1e-20+1e-20", 2e-20],
    ["1e-18+1.4e-20", 1e-18 + 1.4e-20],
    ["1e-10+1e-10", 2e-10],
  ] as const) {
    const node = compileExpression(source, {});
    const got = evaluate(node);
    const exact = exactToFloat(exactEvaluate(node));
    if (!relClose(got, c(want), 1e-9) || !relClose(exact, c(want), 1e-9)) {
      failed += 1;
      console.log("FAIL tiny add", source, got, exact, want);
    }
  }
  const tinySum = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(1e-20), y: c(1e-20) });
  const tinyMix = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(1e-18), y: c(1.4e-20) });
  const zeroSum = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(0), y: c(0) });
  if (tinySum.singular !== SINGULAR_PRECISION || tinyMix.singular !== SINGULAR_PRECISION || zeroSum.singular === SINGULAR_PRECISION || zeroSum.value.re !== 0) {
    failed += 1;
    console.log("FAIL unknown tiny add flag", tinySum, tinyMix, zeroSum);
  }
  const arcCases: Array<[Node, Record<string, { re: number; im: number }>]> = [
    [compileExpression("arcsin(-1)", {}), {}],
    [compileExpression("arcsin(x)", { x: V("x") }), { x: c(-1) }],
    [tArcsin(input(c(-1), "-1")), {}],
  ];
  for (const [node, env] of arcCases) {
    const got = evaluate(node, env);
    const variable = Object.keys(env).length > 0;
    const tol = variable ? 1e-7 : 1e-12;
    if (Math.abs(got.re + Math.PI / 2) > tol || Math.abs(got.im) > tol) {
      failed += 1;
      console.log("FAIL arcsin(-1)", variable ? "variable" : "literal", got);
    }
  }
  const arcExact = exactToFloat(exactEvaluate(compileExpression("arcsin(-1)", {})));
  if (Math.abs(arcExact.re + Math.PI / 2) > 1e-9 || Math.abs(arcExact.im) > 1e-9) {
    failed += 1;
    console.log("FAIL exact arcsin(-1)", arcExact);
  }
  const infFold = evaluateReport(compileExpression("(1+1/0)-1/0", {}));
  const infExact = exactReport(compileExpression("(1+1/0)-1/0", {}));
  const infIsOne = infFold.value.re === 1 && infFold.value.im === 0;
  const infExactIsOne = infExact.value.re.eq(1) && infExact.value.im.eq(0);
  if (infIsOne || infExactIsOne || !Number.isNaN(infFold.value.re) || !infExact.value.re.isNaN() || !infFold.singular || !infExact.singular) {
    failed += 1;
    console.log("FAIL (1+∞)-∞", infFold.value, infFold.singular, formatExact(infExact.value), infExact.singular);
  }
  const varFold = evaluateReport(compileExpression("(x+y)-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(Infinity) });
  const varExact = exactReport(compileExpression("(x+y)-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(Infinity) });
  const foldedBack = varFold.value.re === 1 && varFold.value.im === 0;
  const exactBack = varExact.value.re.eq(1) && varExact.value.im.eq(0);
  if (foldedBack || exactBack || !Number.isNaN(varFold.value.re) || !varExact.value.re.isNaN() || !varFold.singular || !varExact.singular) {
    failed += 1;
    console.log("FAIL (x+∞)-∞", varFold.value, varFold.singular, formatExact(varExact.value), varExact.singular);
  }
  const finiteFold = evaluate(compileExpression("(1+2)-2", {}));
  if (finiteFold.re !== 1 || finiteFold.im !== 0) {
    failed += 1;
    console.log("FAIL finite cancellation", finiteFold);
  }
  const noisy = formatC(evaluate(compileExpression("2-1e10*i", {})));
  const tangent = formatC(evaluate(compileExpression("tan(pi/2)", {})));
  if (noisy.includes("2.000000") || !noisy.startsWith("2 − ") || tangent.includes("7")) {
    failed += 1;
    console.log("FAIL display rounding", noisy, tangent);
  }
  let mode: "float" | "exact" = "float";
  const queued: Array<"float" | "exact"> = [];
  const click = (next: "float" | "exact", busy: boolean) => {
    const step = modeRequest(mode, next, busy);
    if (step.queue) queued.push(next);
    else mode = step.current;
  };
  click("exact", false);
  click("float", false);
  if (mode !== "float") {
    failed += 1;
    console.log("FAIL two mode clicks in one turn", mode);
  }
  mode = "float";
  queued.length = 0;
  click("exact", true);
  click("float", true);
  for (const next of queued) click(next, false);
  if (mode !== "float" || queued.length !== 2) {
    failed += 1;
    console.log("FAIL queued mode clicks", mode, queued);
  }
  const outside = evaluateReport(compileExpression("x-y", { x: V("x"), y: V("y") }), {
    x: c(1),
    y: c(0, 80 * Math.PI),
  });
  if (outside.overflowed || !close(outside.value, c(1, -80 * Math.PI), 1e-6)) {
    failed += 1;
    console.log("FAIL scaled rotSub outside the old strip", outside);
  }
  const knownSub = domainSub(input(c(2, 0.5), "a"), input(c(1, 4), "b"));
  const knownStats = circuitStats(knownSub);
  if (knownStats.rpnLength !== BigInt(131) || !close(evaluate(knownSub), c(1, -3.5), 1e-8)) {
    failed += 1;
    console.log("FAIL in-strip sub should be unscaled rotSub", knownStats.rpnLength.toString(), evaluate(knownSub));
  }
  // No known range, so both stay scaled. Sub is K 565. Add builds k from b and is K 655.
  const varSubK = circuitStats(domainSub(V("x"), V("y"))).rpnLength;
  const varAddK = circuitStats(domainAdd(V("x"), V("y"))).rpnLength;
  if (varSubK !== BigInt(565) || varAddK !== BigInt(655)) {
    failed += 1;
    console.log("FAIL variable sub/add K", varSubK.toString(), varAddK.toString());
  }
  const specials = Math.sqrt(Math.exp(2 * Math.E) - 1);
  const specialPoints = [c(specials), c(-specials), c(0, specials), c(0, -specials)];
  for (const b of specialPoints) {
    const node = domainSub(input(c(1), "a"), V("y"));
    const got = evaluateReport(node, { y: b });
    const exact = exactToFloat(exactEvaluate(node, { y: b }));
    const want = c(1 - b.re, -b.im);
    if (!got.touchedLn0 || !close(got.value, want, 1e-8) || !close(exact, want, 1e-8)) {
      failed += 1;
      console.log("FAIL scaled sub at e^e", b, got.value, exact, want, got.touchedLn0);
    }
  }
  const literals = ["asinh(0.5*i)", "asinh(-2*i)", "asinh(-3+0.5*i)"];
  for (const source of literals) {
    const node = compileExpression(source, {});
    const got = evaluate(node);
    const ref = referenceExpression(source, {});
    const exact = exactToFloat(exactEvaluate(node));
    if (!ref || !close(got, ref, 1e-6) || !close(exact, ref, 1e-6)) {
      failed += 1;
      console.log("FAIL literal", source, got, exact, ref);
    }
  }
  const vanished = compileExpression("5-exp(-inf)", {});
  const vanishedFloat = evaluate(vanished);
  const vanishedExact = exactToFloat(exactEvaluate(vanished));
  if (!close(vanishedFloat, c(5), 1e-8) || !close(vanishedExact, c(5), 1e-8)) {
    failed += 1;
    console.log("FAIL 5-exp(-inf)", vanishedFloat, vanishedExact);
  }
  const quarter = evaluate(tExp(input({ re: Infinity, im: Math.PI / 2 }, "quarter")));
  const quarterExact = exactEvaluate(tExp(input({ re: Infinity, im: Math.PI / 2 }, "quarter")));
  if (quarter.re !== 0 || quarter.im !== Infinity || !quarterExact.re.isZero() || !quarterExact.im.isPos()) {
    failed += 1;
    console.log("FAIL exp(+inf + i pi/2)", quarter, quarterExact.re.toString(), quarterExact.im.toString());
  }
}

/** Block 39's seeded points. The isolate rebuild (block 43) uses them too. */
function differentialCases(): { source: string; env: { x: { re: number; im: number }; y: { re: number; im: number } } }[] {
  const cases: { source: string; env: { x: { re: number; im: number }; y: { re: number; im: number } } }[] = [];
  let seed = 11;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const exprs = ["x-y", "x+y", "asinh(x)", "arcsin(x)", "tan(x)", "hypot(x,y)", "avg(x,y)", "0-0"];
  for (let i = 0; i < 24; i += 1) {
    const source = exprs[i % exprs.length] ?? "x-y";
    const env = {
      x: c(rand() * 4 - 2, rand() * 2 - 1),
      y: c(rand() * 4 - 2, rand() * 2 - 1),
    };
    if (source === "tan(x)") env.x = c(rand(), 2 + rand() * 3);
    cases.push({ source, env });
  }
  return cases;
}

if (shardTurn(39)) {
  for (const { source, env } of differentialCases()) {
    try {
      const node = compileExpression(source, { x: V("x"), y: V("y") });
      const got = evaluate(node, env);
      const ref = referenceExpression(source, env);
      const exact = exactToFloat(exactEvaluate(node, env));
      if (!ref || ![got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite)) continue;
      if (!close(got, ref, 1e-4) || !close(exact, ref, 1e-4)) {
        failed += 1;
        console.log("FAIL differential", source, env, got, exact, ref);
      }
    } catch (err) {
      failed += 1;
      console.log("FAIL differential threw", source, err);
    }
    const raw = E(V("x"), V("y"));
    const got = evaluate(raw, env);
    const ref = eml(env.x, env.y);
    const exact = exactToFloat(exactEvaluate(raw, env));
    if ([got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite) && (!close(got, ref, 1e-6) || !close(exact, ref, 1e-6))) {
      failed += 1;
      console.log("FAIL raw eml", env, got, exact, ref);
    }
  }
}

function freshCircuit(root: Node): Node {
  let id = 8_000_000;
  const seen = new Map<Node, Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame || seen.has(frame.n)) continue;
    if (frame.n.type === "one") {
      seen.set(frame.n, { type: "one", id: id++ });
      continue;
    }
    if (frame.n.type === "var") {
      seen.set(frame.n, { type: "var", name: frame.n.name, id: id++ });
      continue;
    }
    if (frame.n.type === "input") {
      seen.set(frame.n, { type: "input", value: { re: frame.n.value.re, im: frame.n.value.im }, label: frame.n.label, id: id++ });
      continue;
    }
    if (!frame.seen) {
      stack.push({ n: frame.n, seen: true });
      if (frame.n.b) stack.push({ n: frame.n.b, seen: false });
      if (frame.n.a) stack.push({ n: frame.n.a, seen: false });
      continue;
    }
    const a = frame.n.a ? seen.get(frame.n.a) : undefined;
    const b = frame.n.b ? seen.get(frame.n.b) : undefined;
    if (!a || !b) continue;
    seen.set(frame.n, { type: "eml", a, b, id: id++ });
  }
  return seen.get(root) ?? { type: "one", id: id++ };
}

function sharesStructure(a: Node, b: Node): boolean {
  const left = new Set<Node>();
  const stack: Node[] = [a];
  const seen = new Set<Node>();
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    left.add(n);
    if (n.type === "eml") stack.push(n.a, n.b);
  }
  const right: Node[] = [b];
  const seenRight = new Set<Node>();
  while (right.length) {
    const n = right.pop();
    if (!n || seenRight.has(n)) continue;
    seenRight.add(n);
    if (left.has(n)) return true;
    if (n.type === "eml") right.push(n.a, n.b);
  }
  return false;
}

function samePoint(a: { re: number; im: number }, b: { re: number; im: number }): boolean {
  if (Number.isNaN(a.re) || Number.isNaN(a.im) || Number.isNaN(b.re) || Number.isNaN(b.im)) {
    return Number.isNaN(a.re) && Number.isNaN(a.im) && Number.isNaN(b.re) && Number.isNaN(b.im);
  }
  return Object.is(a.re, b.re) && Object.is(a.im, b.im);
}

/** Block 40's samples. The isolate rebuild (block 43) uses them too. */
const freshSamples = [
  "2-1e10*i",
  "1-800",
  "(1+2^-52)-1",
  "(2^53+1)-2^53",
  "sqrt(2)^2-2",
  "tan(1+800*i)",
  "0*(-1)",
  "1/(0*(-1))",
  "exp(inf)-exp(inf)",
  "inf-(1/0)",
  "asinh(0)",
  "asinh(-1e155)",
  "10^400/7",
  "3+1e16*i",
  "1e40+i",
  "1e300+i",
  "(1+1e-15)-1",
];

if (shardTurn(40)) {
  for (const source of freshSamples) {
    const node = compileExpression(source, {});
    const copy = freshCircuit(node);
    if (copy === node || sharesStructure(node, copy)) {
      failed += 1;
      console.log("FAIL fresh circuit returned the cached node", source);
    }
    const live = evaluate(node);
    const again = evaluate(copy);
    if (!samePoint(live, again)) {
      failed += 1;
      console.log("FAIL fresh float", source, live, again);
    }
    const exactLive = exactEvaluate(node);
    const exactAgain = exactEvaluate(copy);
    const exactSame =
      exactLive.re.isNaN() && exactAgain.re.isNaN()
        ? exactLive.im.isNaN() && exactAgain.im.isNaN()
        : exactLive.re.eq(exactAgain.re) && exactLive.im.eq(exactAgain.im);
    if (!exactSame) {
      failed += 1;
      console.log("FAIL fresh exact", source, formatExact(exactLive), formatExact(exactAgain));
    }
    if (isPure(node)) {
      const tokens = rpnTokens(node, 100_000);
      if (tokens) {
        const pressed = nodeFromRpn(tokens);
        if (!samePoint(evaluate(pressed), live)) {
          failed += 1;
          console.log("FAIL press string", source);
        }
      }
    }
  }
  const shown = formatExact(exactEvaluate(compileExpression("10^400/7", {}), {}, { maxNodes: 400_000 }));
  if (shown.includes("0000000000") || !shown.includes("10^")) {
    failed += 1;
    console.log("FAIL 10^400/7 text", shown);
  }
  const neg = evaluate(tArsinh(V("x")), { x: c(-1e5) });
  const neg8 = evaluate(tArsinh(V("x")), { x: c(-1e8) });
  if (!close(neg, c(Math.asinh(-1e5)), 1e-8) || neg.im !== 0 && Math.abs(neg.im) > 1e-8) {
    failed += 1;
    console.log("FAIL variable asinh(-1e5)", neg);
  }
  if (!close(neg8, c(Math.asinh(-1e8)), 1e-8) || (neg8.im !== 0 && Math.abs(neg8.im) > 1e-8)) {
    failed += 1;
    console.log("FAIL variable asinh(-1e8)", neg8);
  }
  const signed = evaluate(compileExpression("0*(-1)", {}));
  const reciprocal = evaluate(compileExpression("1/(0*(-1))", {}));
  if (!Object.is(signed.re, -0) || reciprocal.re !== -Infinity) {
    failed += 1;
    console.log("FAIL signed zero", signed, reciprocal);
  }
  const gap = exactEvaluate(compileExpression("exp(inf)-exp(inf)", {}));
  if (!gap.re.isNaN() || !gap.im.isNaN()) {
    failed += 1;
    console.log("FAIL exact exp(inf)-exp(inf)", formatExact(gap));
  }
  const ulp = evaluate(compileExpression("(1+2^-52)-1", {}));
  if (!close(ulp, c(2 ** -52), 1e-9) || Math.abs(ulp.im) > 0) {
    failed += 1;
    console.log("FAIL (1+2^-52)-1", ulp);
  }
}

/** Block 41's points and seeded random sources. The isolate rebuild (block 43) uses them too. */
const wideSpan = [0, 1e-12, 1e-3, 0.5, 2, 80, 1e6, -1e5, 1e-300, 1e-15, 1e-9, 1e-5, 1e200, 1e300, -1e200];
function wideFuzzSources(): string[] {
  let seed = 11;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const atoms = ["0", "1", "2", "0.5", "-1", "e", "10", "1e-300", "1e-15", "1e-9", "1e-5", "1e200", "1e300", "-1e200"];
  const bins = ["+", "-", "*", "/"];
  const uns = ["sin", "cos", "exp", "sqrt", "asinh"];
  const nest = (depth: number): string => {
    const roll = rand();
    if (depth <= 0 || roll < 0.45) return atoms[Math.floor(rand() * atoms.length)] ?? "1";
    if (roll < 0.7) return `${uns[Math.floor(rand() * uns.length)] ?? "exp"}(${nest(depth - 1)})`;
    const op = bins[Math.floor(rand() * bins.length)] ?? "+";
    return `(${nest(depth - 1)}${op}${nest(depth - 1)})`;
  };
  return Array.from({ length: 30 }, () => nest(3));
}

if (shardTurn(41)) {
  for (const x of wideSpan) {
    for (const source of ["x-y", "asinh(x)"]) {
      const env = { x: c(x), y: c(x === 0 ? 800 : -x) };
      const node = compileExpression(source, { x: V("x"), y: V("y") });
      const copy = freshCircuit(node);
      if (!samePoint(evaluate(node, env), evaluate(copy, env))) {
        failed += 1;
        console.log("FAIL wide fresh", source, x);
      }
    }
  }
  for (const source of wideFuzzSources()) {
    try {
      const node = compileExpression(source, {});
      const got = evaluate(node);
      const copy = evaluate(freshCircuit(node));
      if (!samePoint(got, copy)) {
        failed += 1;
        console.log("FAIL fuzz fresh", source, got, copy);
      }
      const ref = referenceExpression(source, {});
      if (!ref) continue;
      const kind = (z: { re: number; im: number }) =>
        Number.isNaN(z.re) || Number.isNaN(z.im) ? "nan" : Number.isFinite(z.re) && Number.isFinite(z.im) ? "fin" : "inf";
      if (kind(got) !== kind(ref)) {
        failed += 1;
        console.log("FAIL fuzz class", source, got, ref);
      } else if (kind(got) === "fin" && !close(got, ref, 1e-5) && !((source.includes("1e200") || source.includes("1e300")) && evaluateReport(node).singular)) {
        failed += 1;
        console.log("FAIL fuzz", source, got, ref);
      }
    } catch (err) {
      failed += 1;
      console.log("FAIL fuzz threw", source, err);
    }
  }
}

type PackedNum = { k: "n"; v: number; s: 0 | 1 } | { k: "inf"; s: 0 | 1 } | { k: "nan" };

function packNum(n: number): PackedNum {
  if (Number.isNaN(n)) return { k: "nan" };
  if (n === Infinity) return { k: "inf", s: 0 };
  if (n === -Infinity) return { k: "inf", s: 1 };
  if (Object.is(n, -0)) return { k: "n", v: 0, s: 1 };
  return { k: "n", v: n, s: 0 };
}

function unpackNum(p: PackedNum): number {
  if (p.k === "nan") return Number.NaN;
  if (p.k === "inf") return p.s ? Number.NEGATIVE_INFINITY : Number.POSITIVE_INFINITY;
  if (p.s && p.v === 0) return -0;
  return p.v;
}

function exactKey(z: { re: { isNaN(): boolean; toString(): string }; im: { isNaN(): boolean; toString(): string } }): string {
  return `${z.re.isNaN() ? "nan" : z.re.toString()}\0${z.im.isNaN() ? "nan" : z.im.toString()}`;
}

type RebuildTok =
  | { id: number; op: "1" }
  | { id: number; op: "var"; name: string }
  | { id: number; op: "in"; re: PackedNum; im: PackedNum; label: string }
  | { id: number; op: "E"; a: number; b: number };

function dagTokens(root: Node): RebuildTok[] {
  const out: RebuildTok[] = [];
  const seen = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (seen.has(n)) continue;
    if (n.type !== "eml" || !n.a || !n.b) {
      seen.add(n);
      if (n.type === "one") out.push({ id: n.id, op: "1" });
      else if (n.type === "var") out.push({ id: n.id, op: "var", name: n.name });
      else if (n.type === "input") out.push({ id: n.id, op: "in", re: packNum(n.value.re), im: packNum(n.value.im), label: n.label });
      continue;
    }
    if (!frame.seen) {
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    seen.add(n);
    out.push({ id: n.id, op: "E", a: n.a.id, b: n.b.id });
  }
  return out;
}

if (shardTurn(42)) {
  const both = (name: string, source: string, re: number, im = 0, tol = 1e-6) => {
    const node = compileExpression(source, {});
    const got = evaluate(node);
    const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 400_000 }));
    if (!close(got, c(re, im), tol) || !close(exact, c(re, im), tol)) {
      failed += 1;
      console.log("FAIL", name, got, exact, "want", re, im);
    }
  };
  both("asin(3+4i)", "arcsin(3+4*i)", 0.6339838656391766, 2.305509031243477);
  both("asin(-3+4i)", "arcsin(-3+4*i)", -0.6339838656391766, 2.305509031243477);
  both("asin(1+800i)", "arcsin(1+800*i)", 0.0012499983724006398, 7.377760080100202, 1e-5);
  const asinVar = compileExpression("arcsin(x)", { x: V("x") });
  const asinVarGot = evaluate(asinVar, { x: c(3, 4) });
  const asinVarExact = exactToFloat(exactEvaluate(asinVar, { x: c(3, 4) }));
  if (!close(asinVarGot, c(0.6339838656391766, 2.305509031243477), 1e-6) || !close(asinVarExact, c(0.6339838656391766, 2.305509031243477), 1e-6)) {
    failed += 1;
    console.log("FAIL asin variable 3+4i", asinVarGot, asinVarExact);
  }
  both("asin above the cut", "arcsin(2+1e-18*i)", Math.PI / 2, Math.acosh(2), 1e-5);
  both("asin(1e6)", "arcsin(1e6)", Math.PI / 2, -Math.acosh(1e6), 1e-6);
  const asinTiny = evaluate(compileExpression("arcsin(1e-300)", {}));
  const asinTinyExact = exactEvaluate(compileExpression("arcsin(1e-300)", {}));
  if (!relClose(asinTiny, c(1e-300), 1e-9) || !exactClose(asinTinyExact, "1e-300", 0, 12)) {
    failed += 1;
    console.log("FAIL arcsin(1e-300)", asinTiny, asinTinyExact.re.toString());
  }
  both("asinh(i)", "asinh(i)", 0, Math.PI / 2, 1e-9);
  both("asinh(-i)", "asinh(-i)", 0, -Math.PI / 2, 1e-9);
  both("asinh(-1e6 i)", "asinh(-1e6*i)", -Math.acosh(1e6), -Math.PI / 2, 1e-6);
  both("artanh(2)", "artanh(2)", Math.log(3) / 2, -Math.PI / 2, 1e-6);
  both("sinh tiny imag", "sinh(1e-10*i)", 0, 1e-10, 1e-8);
  const atanhTiny = evaluate(compileExpression("artanh(1e-20)", {}));
  if (!relClose(atanhTiny, c(1e-20), 1e-6)) {
    failed += 1;
    console.log("FAIL artanh(1e-20)", atanhTiny);
  }
  const acosOne = evaluate(compileExpression("arccos(1)", {}));
  if (acosOne.re !== 0 || Object.is(acosOne.re, -0) || acosOne.im !== 0) {
    failed += 1;
    console.log("FAIL arccos(1)", acosOne);
  }
  both("arccos(-1)", "arccos(-1)", Math.PI, 0, 1e-8);
  both("arccos(1e8)", "arccos(1e8)", 0, Math.acosh(1e8), 1e-5);
  const subCancel = evaluate(compileExpression("1-(1-2^-52)", {}));
  const subOther = evaluate(compileExpression("(1-2^-52)-1", {}));
  const subSum = evaluate(compileExpression("1-(1+2^-52)", {}));
  const ulp = 2 ** -52;
  if (!relClose(subCancel, c(ulp), 1e-8) || !relClose(subOther, c(-ulp), 1e-8) || !relClose(subSum, c(-ulp), 1e-8)) {
    failed += 1;
    console.log("FAIL ulp cancellation", subCancel, subOther, subSum);
  }
  const tinySub = evaluate(compileExpression("3e-20-1e-20", {}));
  if (!relClose(tinySub, c(2e-20), 1e-6)) {
    failed += 1;
    console.log("FAIL tiny sub", tinySub);
  }
  for (const source of ["exp(-200)", "1e-31", "1e-300"]) {
    const shown = formatExact(exactEvaluate(compileExpression(source, {}), {}, { maxNodes: 200_000 }));
    if (shown === "0" || shown === "−0") {
      failed += 1;
      console.log("FAIL exact tiny snapped", source, shown);
    }
  }
  const wide = formatExact(exactEvaluate(compileExpression("2-1e16*i", {}), {}, { maxNodes: 200_000 }));
  if (!wide.includes("2") || !wide.includes("10^16")) {
    failed += 1;
    console.log("FAIL exact per-component", wide);
  }
  const loggedText = formatC(evaluate(compileExpression("ln(-0)", {})));
  if (loggedText === "undefined" || !loggedText.includes("∞") || !loggedText.includes("i")) {
    failed += 1;
    console.log("FAIL ln(-0) text", loggedText);
  }
  if (!formatC(c(1, 1e-16)).endsWith("≈")) {
    failed += 1;
    console.log("FAIL tidy mark", formatC(c(1, 1e-16)));
  }
  const gap = compileExpression("exp(exp(800))-exp(exp(800))", {});
  const gapFloat = evaluateReport(gap);
  const gapExact = exactReport(gap, {}, { maxNodes: 200_000 });
  if (!Number.isNaN(gapFloat.value.re) || !gapExact.value.re.isNaN()) {
    failed += 1;
    console.log("FAIL exp(exp(800)) difference", gapFloat.value, formatExact(gapExact.value));
  }
  const recip = evaluate(compileExpression("1/(0/-1)", {}));
  const recipSqrt = evaluate(compileExpression("1/sqrt(-0)", {}));
  if (recip.re !== -Infinity || recipSqrt.re !== -Infinity) {
    failed += 1;
    console.log("FAIL signed zero reciprocal", recip, recipSqrt);
  }
  const hugeDiv = evaluateReport(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 });
  if (hugeDiv.value.re !== Infinity) {
    failed += 1;
    console.log("FAIL (10^400+1)/7", hugeDiv.value, hugeDiv.singular);
  }
  const pole = evaluateReport(compileExpression("tan(pi/2)", {}));
  const bigSin = evaluateReport(compileExpression("sin(1e12)", {}));
  const safeSin = evaluateReport(compileExpression("sin(1+800*i)", {}));
  if (pole.singular !== SINGULAR_POLE || bigSin.singular !== SINGULAR_TRIG || safeSin.singular === SINGULAR_TRIG) {
    failed += 1;
    console.log("FAIL trig flags", pole.singular, bigSin.singular, safeSin.singular, safeSin.value);
  }
  const bigExact = exactReport(compileExpression("tan(1e100)", {}), {}, { maxNodes: 200_000 });
  const cosExact = exactReport(compileExpression("cos(1e100)", {}), {}, { maxNodes: 200_000 });
  if (bigExact.singular !== SINGULAR_TRIG || cosExact.singular !== SINGULAR_TRIG) {
    failed += 1;
    console.log("FAIL exact large trig", bigExact.singular, formatExact(bigExact.value), cosExact.singular, formatExact(cosExact.value));
  }
}

type IsolateCase = { source: string; env: Record<string, { re: number; im: number }> };

function compiles(source: string, vars: Record<string, Node>): boolean {
  try {
    compileExpression(source, vars);
    return true;
  } catch {
    return false;
  }
}

/**
 * Each case rebuilt from its DAG tokens in a fresh process must match the live
 * float and exact values. The cases are the ones blocks 37, 39, 40 and 41 test
 * (the sources that compile), built again here so that every shard checks all of
 * them, whichever blocks share its process.
 */
function isolateRebuild(cases: IsolateCase[]): void {
  const repoRoot = path.resolve(__dirname, "../..");
  const payload = cases.map((item, id) => {
    const node = compileExpression(item.source, { x: V("x"), y: V("y") });
    const env: Record<string, { re: PackedNum; im: PackedNum }> = {};
    for (const [name, value] of Object.entries(item.env)) env[name] = { re: packNum(value.re), im: packNum(value.im) };
    return { id, source: item.source, tokens: dagTokens(node), env, live: item.env };
  });
  const child = spawnSync(process.execPath, [tsxCli, path.join(repoRoot, "scripts/eml-rebuild.ts")], {
    input: JSON.stringify(payload.map(({ id, tokens, env }) => ({ id, tokens, env }))),
    encoding: "utf8",
    cwd: repoRoot,
    maxBuffer: 64 * 1024 * 1024,
    timeout: 180_000,
  });
  if (child.status !== 0 || !child.stdout) {
    failed += 1;
    console.log("FAIL isolate rebuild", child.status, child.stderr?.slice(0, 500), child.stdout?.slice(0, 200));
  } else {
    const results = JSON.parse(child.stdout) as Array<{
      id: number;
      error?: string;
      float?: { re: PackedNum; im: PackedNum };
      raw?: { re: PackedNum; im: PackedNum };
      exact?: string;
    }>;
    for (const result of results) {
      const item = payload[result.id];
      if (!item) {
        failed += 1;
        console.log("FAIL isolate id", result.id);
        continue;
      }
      if (result.error || !result.float || !result.raw || result.exact === undefined) {
        failed += 1;
        console.log("FAIL isolate", item.source, result.error);
        continue;
      }
      const node = compileExpression(item.source, { x: V("x"), y: V("y") });
      const live = evaluate(node, item.live, { maxNodes: 400_000 });
      const fresh = result.float;
      const raw = result.raw;
      if (!samePoint(live, { re: unpackNum(fresh.re), im: unpackNum(fresh.im) }) || !samePoint(live, { re: unpackNum(raw.re), im: unpackNum(raw.im) })) {
        failed += 1;
        console.log("FAIL isolate float", item.source, live, fresh, raw);
      }
      const exact = exactKey(exactEvaluate(node, item.live, { maxNodes: 400_000 }));
      if (exact !== result.exact) {
        failed += 1;
        console.log("FAIL isolate exact", item.source, exact, result.exact);
      }
    }
  }
}

if (shardTurn(43)) isolateRebuild(fuzzSources().filter((source) => compiles(source, {})).map((source) => ({ source, env: {} })));

if (shardTurn(69)) isolateRebuild(differentialCases().filter(({ source }) => compiles(source, { x: V("x"), y: V("y") })));

if (shardTurn(70)) isolateRebuild(freshSamples.map((source) => ({ source, env: {} })));

if (shardTurn(71)) isolateRebuild(wideSpan.flatMap((x) => ["x-y", "asinh(x)"].map((source) => ({ source, env: { x: c(x), y: c(x === 0 ? 800 : -x) } }))));

if (shardTurn(72)) isolateRebuild(wideFuzzSources().filter((source) => compiles(source, {})).map((source) => ({ source, env: {} })));

if (shardTurn(44)) failed += runPropertyChecks();

if (shardTurn(66)) failed += branchChecks();

// Wrong values that exact mode certified (lib/eml/check-certify.ts).
if (shardTurn(45)) failed += runCertifyChecks();

// Inverse-function regressions. Reference values are mpmath 1.3.0 at 30 digits.
// arcsin: principal value, counter-clockwise continuity on the real cut (as mpmath):
// arcsin(x > 1) = π/2 − i·arcosh(x), arcsin(x < −1) = −π/2 + i·arcosh(−x).
if (shardTurn(46)) {
  const bfRel = (got: { re: number; im: number }, want: { re: number; im: number }, tol: number) =>
    Number.isFinite(got.re) && Number.isFinite(got.im) && Math.hypot(got.re - want.re, got.im - want.im) <= tol * Math.max(Math.hypot(want.re, want.im), 1e-300);
  const asinCases: Array<[number, number, number, number]> = [
    [3, 4, 0.63398386563917672, 2.3055090312434769],
    [-3, 4, -0.63398386563917672, 2.3055090312434769],
    [3, -4, 0.63398386563917672, -2.3055090312434769],
    [-3, -4, -0.63398386563917672, -2.3055090312434769],
    [1, 800, 0.0012499983724006398, 7.3777600801002023],
    [0, 10, 0.0, 2.9982229502979697],
    [0, -10, 0.0, -2.9982229502979697],
    [0.5, 5, 0.097763379364927734, 2.3171322930349235],
    [2, 1e-18, 1.5707963267948966, 1.3169578969248167],
    [2, -1e-18, 1.5707963267948966, -1.3169578969248167],
    [-2, 1e-18, -1.5707963267948966, 1.3169578969248167],
    [-2, -1e-18, -1.5707963267948966, -1.3169578969248167],
    [2, 0, 1.5707963267948966, -1.3169578969248167],
    [-2, 0, -1.5707963267948966, 1.3169578969248167],
    [1.5, 0, 1.5707963267948966, -0.96242365011920689],
    [0.5, 0, 0.52359877559829887, 0.0],
    [1000000, 0, 1.5707963267948966, -14.508657738523969],
    [-1000000, 0, -1.5707963267948966, 14.508657738523969],
    [0, 1000000, 0.0, 14.508657738524469],
    [1000000000000, 0.5, 1.5707963267943966, 28.324168296488494],
    [1e-9, 0, 1.0000000000000001e-9, 0.0],
  ];
  for (const [re, im, wantRe, wantIm] of asinCases) {
    const want = c(wantRe, wantIm);
    const source = `arcsin((${re})+(${im})*i)`;
    const node = compileExpression(source, {});
    const got = evaluate(node, {}, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
    if (!bfRel(got, want, 1e-9) || !bfRel(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL arcsin literal", source, got, exact, want);
    }
  }
  // A variable has no proven range. Its value must still be right on both
  // sides of |Im x| = π; exact mode also keeps the side of a 10^(−18) offset.
  const variable = unaryNode("arcsin");
  const varCases: Array<[number, number, number, number, boolean]> = [
    [3, 4, 0.63398386563917672, 2.3055090312434769, true],
    [3, -4, 0.63398386563917672, -2.3055090312434769, true],
    [-3, 4, -0.63398386563917672, 2.3055090312434769, true],
    [1, 800, 0.0012499983724006398, 7.3777600801002023, true],
    [0, 10, 0.0, 2.9982229502979697, true],
    [0, -10, 0.0, -2.9982229502979697, true],
    [0.5, 5, 0.097763379364927734, 2.3171322930349235, true],
    [2, 0, 1.5707963267948966, -1.3169578969248167, true],
    [-2, 0, -1.5707963267948966, 1.3169578969248167, true],
    [1, 0, 1.5707963267948966, 0, true],
    [-1, 0, -1.5707963267948966, 0, true],
    [0.5, 0, 0.52359877559829887, 0.0, true],
    [0, 1000000, 0.0, 14.508657738524469, true],
    [-1000000, 0, -1.5707963267948966, 14.508657738523969, true],
    [0, -1000000, 0.0, -14.508657738524469, true],
    [2, 1e-18, 1.5707963267948966, 1.3169578969248167, false],
    [-2, -1e-18, -1.5707963267948966, -1.3169578969248167, false],
  ];
  for (const [re, im, wantRe, wantIm, floatToo] of varCases) {
    const want = c(wantRe, wantIm);
    const env = { x: c(re, im) };
    const got = evaluate(variable, env, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(variable, env, { maxNodes: 2_000_000 }));
    if ((floatToo && !bfRel(got, want, 1e-7)) || !bfRel(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL arcsin variable", re, im, got, exact, want);
    }
  }

  // arsinh and arccos follow arcsin's conventions (mpmath).
  const viaArcsin: Array<[string, number, number, number, number]> = [
    ["arsinh", 0, -1000000, -14.508657738523969, -1.5707963267948966],
    ["arsinh", 0, 1, 0.0, 1.5707963267948966],
    ["arsinh", 0, -1, 0.0, -1.5707963267948966],
    ["arsinh", 0, 2, 1.3169578969248167, 1.5707963267948966],
    ["arsinh", 0, -2, -1.3169578969248167, -1.5707963267948966],
    ["arsinh", 3, 4, 2.2999140408792696, 0.91761685335147866],
    ["arsinh", -3, -4, -2.2999140408792696, -0.91761685335147866],
    ["arsinh", -1000000, 0, -14.508657738524469, 0.0],
    ["arsinh", 1e-9, 0, 1.0000000000000001e-9, 0.0],
    ["arsinh", 1e-18, -2, 1.3169578969248167, -1.5707963267948966],
    ["arsinh", -1e-18, 2, -1.3169578969248167, 1.5707963267948966],
    ["arccos", -1, 0, 3.1415926535897932, 0.0],
    ["arccos", 1, 0, 0.0, 0.0],
    ["arccos", 2, 0, 0.0, 1.3169578969248167],
    ["arccos", -2, 0, 3.1415926535897932, -1.3169578969248167],
    ["arccos", 3, 4, 0.9368124611557199, -2.3055090312434769],
    ["arccos", 0, 10, 1.5707963267948966, -2.9982229502979697],
    ["arccos", 0.5, 0, 1.0471975511965977, 0.0],
    ["arccos", -2, -1e-18, 3.1415926535897932, 1.3169578969248167],
  ];
  for (const [fn, re, im, wantRe, wantIm] of viaArcsin) {
    const want = c(wantRe, wantIm);
    // ±i as typed. 0 + (−1)·i is another circuit; its float value is about 4·10^(−8) off.
    const source = re === 0 && (im === 1 || im === -1) ? `${fn}(${im < 0 ? "-" : ""}i)` : `${fn}((${re})+(${im})*i)`;
    const node = compileExpression(source, {});
    const got = evaluate(node, {}, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
    const tolF = want.re === 0 && want.im === 0 ? 0 : 1e-9;
    const okF = tolF === 0 ? Math.hypot(got.re, got.im) <= 1e-15 : bfRel(got, want, tolF);
    const okX = tolF === 0 ? Math.hypot(exact.re, exact.im) <= 1e-30 : bfRel(exact, want, 1e-14);
    if (!okF || !okX) {
      failed += 1;
      console.log("FAIL branch literal", source, got, exact, want);
    }
  }
  const asinhVar = unaryNode("arsinh");
  for (const [re, im, wantRe, wantIm] of [
    [0, 1, 0, 1.5707963267948966],
    [0, -1, 0, -1.5707963267948966],
    [0, 2, 1.3169578969248167, 1.5707963267948966],
    [0, -1000000, -14.508657738523969, -1.5707963267948966],
    [0, 1000000, 14.508657738523969, 1.5707963267948966],
    [1000000, 0, 14.508657738524469, 0],
  ] as Array<[number, number, number, number]>) {
    const env = { x: c(re, im) };
    const want = c(wantRe, wantIm);
    const got = evaluate(asinhVar, env, { maxNodes: 2_000_000 });
    const report = exactReport(asinhVar, env, { maxNodes: 2_000_000 });
    if (!bfRel(got, want, 1e-7) || report.singular || !bfRel(exactToFloat(report.value), want, 1e-14)) {
      failed += 1;
      console.log("FAIL arsinh variable", re, im, got, report.singular, exactToFloat(report.value), want);
    }
  }

  // Exact mode printed every |value| ≤ 10^(−30) as 0 (exactInteger's absolute 1e-30 test).
  const exactText: Array<[string, string]> = [
    ["1e-30", "1×10^−30"],
    ["-1e-40", "−1×10^−40"],
    ["2e-80+1e-80", "3×10^−80"],
    ["1e-90*3", "3×10^−90"],
    ["1e-29", "1×10^−29"],
    ["2", "2"],
    ["6*7", "42"],
  ];
  for (const [source, want] of exactText) {
    const text = formatExact(exactEvaluate(compileExpression(source, {}), {}));
    if (text !== want) {
      failed += 1;
      console.log("FAIL exact display", source, text, want);
    }
  }

  // Subtraction of two tiny operands lost the subtrahend (no lift before eml(ln a, exp b)).
  const tinySub: Array<[string, number, number]> = [
    ["1e-100-3e-100", -2e-100, 0],
    ["0-1e-90", -1e-90, 0],
    ["(1e-90*i)-(2e-90)", -2e-90, 1e-90],
    ["3e-20-1e-20", 2e-20, 0],
  ];
  for (const [source, wantRe, wantIm] of tinySub) {
    const node = compileExpression(source, {});
    const want = c(wantRe, wantIm);
    const got = evaluate(node, {});
    const exact = exactToFloat(exactEvaluate(node, {}));
    if (!bfRel(got, want, 1e-9) || !bfRel(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL tiny sub", source, got, exact, want);
    }
  }
}

if (shardTurn(47)) {
  // The float flag compares each component at the 12 displayed digits.
  // The exact reference raises its precision when a subtraction cancels, so a
  // float 0 is not certified by an exact 0. The −6.7×10^(−106) real part is a
  // real component, not dust, and stays.
  const kept = exactEvaluate(compileExpression("(2e-40*i)-(-6.7e-106)", {}));
  const keptNeg = exactEvaluate(compileExpression("(2e-40*i)-(6.7e-106)", {}));
  if (
    kept.re.isZero() ||
    kept.re.sub("6.7e-106").abs().div("6.7e-106").gt("1e-9") ||
    keptNeg.re.isZero() ||
    keptNeg.re.plus("6.7e-106").abs().div("6.7e-106").gt("1e-9")
  ) {
    failed += 1;
    console.log("FAIL tiny real part snapped", kept.re.toString(), keptNeg.re.toString());
  }
  const half = formatExact(exactEvaluate(compileExpression("0.5-1e-72", {})));
  if (half === "0.5" || !half.includes("999")) {
    failed += 1;
    console.log("FAIL exact 0.5-1e-72 display", half);
  }
  const hugeDiv = evaluateReport(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 });
  if (hugeDiv.singular === SINGULAR_LN0) {
    failed += 1;
    console.log("FAIL float overflow labelled ln 0", hugeDiv.singular, hugeDiv.value);
  }
  const hugeExact = formatExact(exactEvaluate(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 }));
  if (!hugeExact.includes("10^399") || hugeExact.includes("∞")) {
    failed += 1;
    console.log("FAIL exact (10^400+1)/7", hugeExact);
  }
  for (const source of ["tan(pi/2)", "tan(3*pi/2)"]) {
    const floatPole = evaluateReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
    const exactPole = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
    if (floatPole.singular !== SINGULAR_POLE || exactPole.singular !== SINGULAR_POLE) {
      failed += 1;
      console.log("FAIL pole", source, floatPole.singular, exactPole.singular, floatPole.value, formatExact(exactPole.value));
    }
  }
  const nearPole = exactEvaluate(compileExpression("tan(pi/2+1e-8)", {}), {}, { maxNodes: 400_000 });
  if (!nearPole.im.isZero() && nearPole.im.abs().gt("1e-40")) {
    failed += 1;
    console.log("FAIL exact tan near pole imag", nearPole.re.toString(), nearPole.im.toString());
  }
  const atanh = exactToFloat(exactEvaluate(compileExpression("artanh(2)", {})));
  if (Math.abs(atanh.re - Math.log(3) / 2) > 1e-9 || Math.abs(atanh.im + Math.PI / 2) > 1e-9) {
    failed += 1;
    console.log("FAIL artanh lower cut", atanh);
  }
  const flagged = (source: string) => {
    const node = compileExpression(source, {});
    const got = evaluateReport(node, {}, { maxNodes: 400_000 });
    const report = exactReport(node, {}, { maxNodes: 400_000 });
    return beyondFloatBound(got.value, exactToFloat(report.value)) || exactUnderflowsFloat(report.value);
  };
  for (const source of ["exp(1e-9*i)-1", "1e300+i", "tan(50000)", "exp(1e-6)-1", "cos(1e-200)-1"]) {
    if (!flagged(source)) {
      failed += 1;
      const node = compileExpression(source, {});
      const got = evaluate(node, {}, { maxNodes: 400_000 });
      const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 400_000 }));
      console.log("FAIL unflagged", source, got, exact, formatExact(exactEvaluate(node, {}, { maxNodes: 400_000 })));
    }
  }
  if (beyondFloatBound(c(1), c(1 + 1e-12)) !== false || beyondFloatBound(c(1), c(1 + 1e-11)) !== true) {
    failed += 1;
    console.log("FAIL displayed-digit tolerance");
  }
  // The same path the screen uses: parse the typed expression, pack it for the
  // worker, and read the text the worker would post.
  const shown = (source: string) => {
    const node = compileExpression(source, {});
    const packed = packCircuit(node);
    const rebuilt = unpackCircuit(packed.tokens, packed.root);
    return formatExact(exactReport(rebuilt, {}, { maxNodes: 80_000 }).value);
  };
  for (const [source, want] of [
    ["sin(10^-200)", "1×10^−200"],
    ["sin(1e-200)", "1×10^−200"],
    ["tan(1e-200)", "1×10^−200"],
    ["tanh(1e-200)", "1×10^−200"],
    ["arctan(1e-200)", "1×10^−200"],
    ["tan(1e-400)", "1×10^−400"],
    ["ln(1+1e-130)", "1×10^−130"],
    ["exp(1e-150)-1", "1×10^−150"],
    ["sqrt(1+1e-200)-1", "5×10^−201"],
    ["tan(10^(-20))", "1×10^−20"],
    ["tan(10^(-100))", "1×10^−100"],
  ] as Array<[string, string]>) {
    const text = shown(source);
    const direct = formatExact(exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 }).value);
    if (text !== want || direct !== want) {
      failed += 1;
      console.log("FAIL tiny trig text", source, text, direct, want);
    }
  }
  const tinyTan = compileExpression("tan(1e-200)", {});
  const tinyFloat = evaluateReport(tinyTan, {}, { maxNodes: 80_000 });
  const tinyExact = exactToFloat(exactReport(tinyTan, {}, { maxNodes: 80_000 }).value);
  if (beyondFloatBound(tinyFloat.value, tinyExact) || Math.abs(tinyExact.re - 1e-200) / 1e-200 > 1e-9) {
    failed += 1;
    console.log("FAIL tan(1e-200) should agree on the leading term", tinyFloat.value, tinyExact);
  }
  const cosGap = (source: string, want: string) => {
    const text = shown(source);
    const rel = exactEvaluate(compileExpression(source, {}), {}, { maxNodes: 80_000 });
    const off = rel.re.sub(want).abs().div(want.replace("-", ""));
    if (text.includes("i") || rel.re.isZero() || off.gt("1e-9")) {
      failed += 1;
      console.log("FAIL cos minus one", source, text, rel.re.toString());
    }
  };
  cosGap("cos(1e-100)-1", "-5e-201");
  cosGap("cos(1e-200)-1", "-5e-401");
  for (const source of ["arsinh(1e-18)", "arsinh(-1e-18)", "arcsin(1e-18*i)", "arcsin(-1e-18*i)", "arcsin(1e-12*i)"]) {
    const node = compileExpression(source, {});
    const packed = packCircuit(node);
    const rebuilt = unpackCircuit(packed.tokens, packed.root);
    const exact = exactReport(rebuilt, {}, { maxNodes: 200_000 });
    const got = evaluateReport(node, {}, { maxNodes: 200_000 });
    if (beyondFloatBound(got.value, exactToFloat(exact.value))) {
      failed += 1;
      console.log("FAIL spurious tiny component", source, got.value, formatExact(exact.value));
    }
  }
  const hugeSum = formatExact(exactEvaluate(compileExpression("1e308+2e308", {}), {}, { maxNodes: 80_000 }));
  if (!hugeSum.includes("3") || !hugeSum.includes("10^308")) {
    failed += 1;
    console.log("FAIL exact 1e308+2e308", hugeSum);
  }
  const atanNeg = compileExpression("arctan(-2*i)", {});
  const atanFloat = evaluate(atanNeg, {}, { maxNodes: 200_000 });
  const atanExact = exactToFloat(exactEvaluate(atanNeg, {}, { maxNodes: 200_000 }));
  if (Math.abs(atanFloat.re - atanExact.re) > 1e-9 || Math.abs(atanFloat.im - atanExact.im) > 1e-9 || atanFloat.re > 0) {
    failed += 1;
    console.log("FAIL arctan(-2i) cut", atanFloat, atanExact);
  }
  const farText = shown("tan(1e-5000)");
  if (farText !== "1×10^−5000") {
    failed += 1;
    console.log("FAIL tan(1e-5000)", farText);
  }
  const beyond = exactReport(unpackCircuit(...(() => {
    const packed = packCircuit(compileExpression("cos(1e-300)-1", {}));
    return [packed.tokens, packed.root] as const;
  })()), {}, { maxNodes: 80_000 });
  if (!beyond.unverified && formatExact(beyond.value) === "0") {
    failed += 1;
    console.log("FAIL cos(1e-300)-1 certified a zero", formatExact(beyond.value), beyond.unverified);
  }
  const poleNode = compileExpression("tan(pi/2)", {});
  const polePacked = packCircuit(poleNode);
  const poleRebuilt = unpackCircuit(polePacked.tokens, polePacked.root);
  const poleExact = exactReport(poleRebuilt, {}, { maxNodes: 80_000 });
  const poleFloat = evaluateReport(poleNode, {}, { maxNodes: 80_000 });
  if (poleExact.singular !== SINGULAR_POLE || poleFloat.singular !== SINGULAR_POLE) {
    failed += 1;
    console.log("FAIL packed tan pole", poleExact.singular, poleFloat.singular, formatExact(poleExact.value));
  }
}

// The screen's worker path: parse, pack, unpack, then the exact engine.
// Equivalent spellings, series corrections, dust, and the 480-digit cap.
function workerReport(source: string) {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
}
function closeTo(source: string, re: string, im = "0"): void {
  const report = workerReport(source);
  const wantRe = exactParts(re).re;
  const wantIm = exactParts(im).re;
  const badRe = wantRe.isZero() ? !report.value.re.isZero() : report.value.re.sub(wantRe).abs().div(wantRe.abs()).gt("1e-9");
  const badIm = wantIm.isZero() ? !report.value.im.isZero() : report.value.im.sub(wantIm).abs().div(wantIm.abs()).gt("1e-9");
  if (report.unverified || badRe || badIm) {
    failed += 1;
    console.log("FAIL worker value", source, report.unverified ? "unverified" : formatExact(report.value));
  }
}
function unresolved(source: string): void {
  const report = workerReport(source);
  if (!report.unverified) {
    failed += 1;
    console.log("FAIL certified", source, formatExact(report.value));
  }
}
// From p = 112 the negative imaginary part falls off 120 digits and the composed
// log would certify +π. The value is ln 2 − iπ, or the result stays unverified.
function lnBelow(source: string): void {
  const report = workerReport(source);
  if (report.unverified) return;
  const wantRe = exactParts("0.6931471805599453").re;
  const wantIm = exactParts(Math.PI).re.neg();
  const badRe = report.value.re.sub(wantRe).abs().div(wantRe.abs()).gt("1e-9");
  const badIm = report.value.im.isPos() || report.value.im.sub(wantIm).abs().div(wantIm.abs()).gt("1e-9");
  if (badRe || badIm) {
    failed += 1;
    console.log("FAIL ln below the cut", source, formatExact(report.value));
  }
}
// Scaled tiny adds stay on the raw add word only while the lifted imaginary parts
// and their sum sit in (−π, π]. These are the cases that leave that strip.
function bothModes(source: string, re: string, im: string): void {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  const rebuilt = unpackCircuit(packed.tokens, packed.root);
  const exact = exactReport(rebuilt, {}, { maxNodes: 200_000 });
  const floated = evaluate(rebuilt, {}, { maxNodes: 200_000 });
  const wantRe = exactParts(re).re;
  const wantIm = exactParts(im).re;
  const off = (got: Decimal, want: Decimal, tol: string) => {
    if (want.isZero()) return got.abs().gt("1e-12");
    return got.sub(want).abs().div(want.abs()).gt(tol);
  };
  const floatRe = exactParts(floated.re).re;
  const floatIm = exactParts(floated.im).re;
  if (
    exact.unverified ||
    off(exact.value.re, wantRe, "1e-9") ||
    off(exact.value.im, wantIm, "1e-9") ||
    off(floatRe, wantRe, "1e-8") ||
    off(floatIm, wantIm, "1e-8")
  ) {
    failed += 1;
    console.log("FAIL both modes", source, exact.unverified ? "unverified" : formatExact(exact.value), floated);
  }
}

if (shardTurn(48)) {
  for (const source of [
    "sin(2*10^(-200))",
    "sin(2*1e-200)",
    "sin(10^(-200)+10^(-200))",
    "sin(1e-200+1e-200)",
  ]) closeTo(source, "2e-200");
  for (const source of ["-1+exp(10^(-150))", "exp(10^(-150))-1", "-1+exp(1e-150)", "exp(1e-150)-1"]) closeTo(source, "1e-150");
  closeTo("sin(1e-40)-1e-40", "-1.666666666667e-121");
  closeTo("tan(1e-40)-1e-40", "3.333333333333e-121");
  closeTo("tan(10^(-40))-10^(-40)", "3.333333333333e-121");
  closeTo("tan(3*10^(-40))-3*10^(-40)", "9e-120");
  closeTo("tan(1e-50)-1e-50", "3.333333333333e-151");
}

if (shardTurn(67)) {
  closeTo("tanh(1e-45)-1e-45", "-3.333333333333e-136");
  closeTo("tanh(10^(-45))-10^(-45)", "-3.333333333333e-136");
  closeTo("tanh(3*10^(-45))-3*10^(-45)", "-9e-135");
  closeTo("arctan(1e-45)-1e-45", "-3.333333333333e-136");
  closeTo("arctan(10^(-45))-10^(-45)", "-3.333333333333e-136");
  closeTo("arctan(3*10^(-45))-3*10^(-45)", "-9e-135");
}

if (shardTurn(68)) {
  closeTo("cos(1e-50)-1", "-5e-101");
  closeTo("cos(10^(-50))-1", "-5e-101");
  closeTo("cos(3*10^(-50))-1", "-4.5e-100");
  closeTo("cos(1e-50)-1+5e-101", "4.166666666667e-202");
  closeTo("sin(1e-18+1e-120*i)", "1e-18", "1e-120");
  closeTo("ln(1+10^(-130))", "1e-130");
  closeTo("ln(1+1e-130)", "1e-130");
  closeTo("ln(1+3*10^(-130))", "3e-130");
  closeTo("log(1+10^(-130))", "1e-130");
  closeTo("log(1+1e-130)", "1e-130");
  closeTo("log(1+3*10^(-130))", "3e-130");
  closeTo("log(1+10^(-200))", "1e-200");
  closeTo("ln(1+10^(-300))", "1e-300");
  closeTo("ln(1+3*10^(-300))", "3e-300");
  closeTo("log(1+3*1e-300)", "3e-300");
}

if (shardTurn(64)) {
  lnBelow("ln(-2-10^(-110)*i)");
  lnBelow("ln(-2-10^(-112)*i)");
  lnBelow("ln(-2-10^(-115)*i)");
  lnBelow("ln(-2-10^(-130)*i)");
  bothModes("0.00005*i+0.00005*i", "0", "0.0001");
  bothModes("0.00006103*i+0.00006103*i", "0", "0.00012206");
  bothModes("sinh(0.00005*i)", "0", "0.00005");
  bothModes("tanh(1e-10*i)", "0", "1e-10");
  bothModes("tanh(1e-16*i)", "0", "1e-16");
  bothModes("cosh(0.00005*i)", "0.99999999875", "0");
  bothModes("3.1*i+0.04", "0.04", "3.1");
  bothModes("4*i+0.5*i", "0", "4.5");
  bothModes("-4*i+1", "1", "-4");
  bothModes("0.00005*i+4*i", "0", "4.00005");
  bothModes("6*i+(-6*i)", "0", "0");
  bothModes("(2+3*i)+(-1+0.2*i)", "1", "3.2");
  bothModes("(3.141592653589793*i)+(-0.0001*i)", "0", "3.141492653589793");
}

if (shardTurn(65)) {
  closeTo("(exp(1e-50)-1)-1e-50", "5e-101");
  closeTo("ln(1+1e-50)-1e-50", "-5e-101");
  closeTo("(sqrt(1+1e-50)-1)-5e-51", "-1.25e-101");
  closeTo("1e-120*(2+i)", "2e-120", "1e-120");
  closeTo("3*((1e-120*i)-(2e-120))", "-6e-120", "3e-120");
  closeTo("2*(1e-18+1e-125*i)", "2e-18", "2e-125");
  closeTo("exp(1e-432)-1", "1e-432");
  closeTo("tan(1e-5000)", "1e-5000");
  closeTo("exp(1e-1000)-1", "1e-1000");
  for (const source of ["exp(1e-433)-1", "tan(10^(-5000))", "exp(10^(-1000))-1", "sin(1e-300)-1e-300"]) unresolved(source);
  const shortcut = seriesShortcutNote(compileExpression("sin(1e-200)", {}));
  if (!shortcut || !shortcut.includes("series shortcut")) {
    failed += 1;
    console.log("FAIL series note", shortcut);
  }
  if (seriesShortcutNote(compileExpression("sin(1)", {})) !== null) {
    failed += 1;
    console.log("FAIL series note on sin(1)");
  }
  const under = agreementNote("ln(1+1e-130)", { re: 1e-130, im: 0 }, {}, "1×10^−130");
  if (under !== "float underflows") {
    failed += 1;
    console.log("FAIL float underflows note", under);
  }
  const atanValue = evaluate(compileExpression("arctan(-2*i)", {}), {}, { maxNodes: 200_000 });
  const atanNote = agreementNote("arctan(-2*i)", atanValue, {}, formatC(atanValue));
  if (atanNote !== "matches the usual value" || !(atanValue.re < 0)) {
    failed += 1;
    console.log("FAIL arctan usual value", atanNote, atanValue);
  }
  if (captionName("1×10^−5000", { re: 0, im: 0 }, "tan(1e-5000)") !== null) {
    failed += 1;
    console.log("FAIL caption zero beside a tiny exact text");
  }
  if (captionName("0", { re: 0, im: 0 }, "1-1") !== "0") {
    failed += 1;
    console.log("FAIL caption of a real zero");
  }
  const blocked = finiteLossMessage({ usable: false, notice: "couldn't verify", singular: null, mode: "float", text: "—" });
  const finite = finiteLossMessage({ usable: false, notice: null, singular: null, mode: "float", text: "—" });
  if (blocked !== null || finite !== "That left the finite numbers.") {
    failed += 1;
    console.log("FAIL double limit message", blocked, finite);
  }
  const byKey = new Map(table.minimality.map((row) => [`${row.value}@${row.k}`, row]));
  const zero = byKey.get("0@7");
  const neg15 = byKey.get("−1@15");
  const neg17 = byKey.get("−1@17");
  const two = byKey.get("2@19");
  // Proved by tools/minimality/decide.py --open (all 6918 programs with K <= 19 excluded).
  const ipi = byKey.get("+iπ on this cut (−iπ on the principal log)@21");
  if (
    ipi?.label !== "proven minimal" ||
    !ipi.note.includes("6918") ||
    zero?.label !== "proven minimal" ||
    !zero.note.includes("K ≤ 5") ||
    neg15?.label !== "proven minimal (uses ln 0)" ||
    neg17?.label !== "proven minimal without ln 0" ||
    two?.label !== "proven minimal" ||
    !two.note.includes("2056")
  ) {
    failed += 1;
    console.log("FAIL minimality labels", zero, neg15, neg17, two);
  }
}

if (shardTurn(49)) {
  // A same-process unpack reuses the nodes that still hold the float range.
  // The screen's worker is a fresh realm, so the tiny known value has to cross the wire.
  const sources = [
    "ln(1+10^(-130))",
    "log(1+10^(-130))",
    "log(1+10^(-200))",
    "ln(1+10^(-300))",
    "ln(1+3*10^(-300))",
  ];
  const jobs = sources.map((source) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root };
  });
  const fresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(jobs));
  if (fresh.status !== 0) {
    failed += 1;
    console.log("FAIL fresh exact process", fresh.status, fresh.stderr);
  } else {
    const rows = JSON.parse(fresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
    const want: Record<string, string> = {
      "ln(1+10^(-130))": "1×10^−130",
      "log(1+10^(-130))": "1×10^−130",
      "log(1+10^(-200))": "1×10^−200",
      "ln(1+10^(-300))": "1×10^−300",
      "ln(1+3*10^(-300))": "3×10^−300",
    };
    for (const row of rows) {
      if (row.unverified || row.text !== want[row.source]) {
        failed += 1;
        console.log("FAIL fresh ln", row.source, row.unverified ? "unverified" : row.text);
      }
    }
  }
}

if (shardTurn(50)) {
  // A float underflow is not the integer 0. Negation, sine, and 0 − b keep the tiny term.
  const tinyRows: Array<[string, string]> = [
    ["-10^(-400)", "−1×10^−400"],
    ["-exp(-1000)", "−5.075958897549×10^−435"],
    ["sin(-10^(-400))", "−1×10^−400"],
    ["(0-1)*10^(-400)", "−1×10^−400"],
    ["-(2*exp(-1000))", "−1.01519177951×10^−434"],
    ["0-10^(-400)", "−1×10^−400"],
    ["0-exp(-1000)", "−5.075958897549×10^−435"],
    ["0-exp(-1000+i)", "−2.742552296838×10^−435 − 4.271272132365×10^−435i"],
    ["0-(2*exp(-1000))", "−1.01519177951×10^−434"],
    ["0+exp(-1000)", "5.075958897549×10^−435"],
    ["-10^(-500)", "−1×10^−500"],
    ["0-1/10^400", "−1×10^−400"],
    ["0-1/10^433", "−1×10^−433"],
    ["0-(exp(-1000)/3)", "−1.691986299183×10^−435"],
    ["(1+10^-500)-1", "1×10^−500"],
    ["10^-500+1-1", "1×10^−500"],
    ["exp(-1000)+exp(-1000)", "1.01519177951×10^−434"],
    ["-(exp(-1000)+exp(-1000))", "−1.01519177951×10^−434"],
    ["ln(1+1/10^400)", "1×10^−400"],
    ["0-ln(1+10^(-400))", "−1×10^−400"],
    ["ln(1-10^(-400))", "−1×10^−400"],
    ["ln(1+10^(-400))", "1×10^−400"],
    ["-(10^(-30))", "−1×10^−30"],
    ["10^(-30)", "1×10^−30"],
    ["-10^(-130)", "−1×10^−130"],
    ["10^(-130)", "1×10^−130"],
    ["10^(-400)", "1×10^−400"],
    ["-0", "−0"],
  ];
  const tinyNodes = tinyRows.map(([source]) => compileExpression(source, {}));
  for (const [i, [source, want]] of tinyRows.entries()) {
    const report = exactReport(tinyNodes[i], {}, { maxNodes: 400_000 });
    const text = formatExact(report.value).replace(/\u200b/g, "");
    const zero = text === "0" || text === "−0";
    const note = agreementNote(source, evaluateReport(tinyNodes[i], {}, { maxNodes: 400_000 }).value, {}, text);
    const vouched = note === "matches the usual value" && source !== "-0" && source !== "10^(-30)" && source !== "-(10^(-30))" && source !== "10^(-130)" && source !== "-10^(-130)";
    if (report.unverified || text !== want || (zero && source !== "-0") || vouched) {
      failed += 1;
      console.log("FAIL tiny underflow", source, report.unverified ? "unverified" : text, note);
    } else {
      console.log("tiny", source, text);
    }
  }
  const barePow = compileExpression("10^(-400)", {});
  const bareExp = compileExpression("exp(-1000)", {});
  if (rangeOf(barePow).int !== undefined || knownValue(barePow) !== null || knownValue(bareExp) !== null) {
    failed += 1;
    console.log("FAIL underflow tagged as exact 0", rangeOf(barePow).int, knownValue(barePow), knownValue(bareExp));
  }
  const signed = evaluate(compileExpression("-0", {}));
  if (!Object.is(signed.re, -0) || signed.im !== 0) {
    failed += 1;
    console.log("FAIL typed -0", signed);
  }
  // A logarithm the circuit collapses past the cap must not certify 0.
  const lostRows = ["ln(1-10^(-500))", "ln(1+10^(-500))", "ln(1+exp(-1000))", "ln(1-exp(-1000))"];
  // Past-cap 0 − power may print the value or say it could not verify. A confident 0 fails.
  const eitherRows: Array<[string, string]> = [
    ["0-10^(-433)", "−1×10^−433"],
    ["0-10^(-500)", "−1×10^−500"],
  ];
  const eitherNodes = eitherRows.map(([source]) => compileExpression(source, {}));
  for (const [i, [source, want]] of eitherRows.entries()) {
    const report = exactReport(eitherNodes[i], {}, { maxNodes: 400_000 });
    const text = formatExact(report.value).replace(/\u200b/g, "");
    if (report.unverified) console.log("either", source, "couldn't verify");
    else if (text === want) console.log("either", source, text);
    else {
      failed += 1;
      console.log("FAIL past-cap sub", source, text);
    }
  }
  const lostNodes = lostRows.map((source) => compileExpression(source, {}));
  for (const [i, source] of lostRows.entries()) {
    const report = exactReport(lostNodes[i], {}, { maxNodes: 400_000 });
    const text = formatExact(report.value).replace(/\u200b/g, "");
    const collapsed = text === "0" || text === "−0";
    if (!report.unverified || !collapsed) {
      failed += 1;
      console.log("FAIL lost tiny", source, report.unverified ? "unverified" : text);
    } else {
      console.log("lost", source, "couldn't verify");
    }
  }
  const foldedPow = exactReport(compileExpression("10^(-500)-10^(-500)", {}), {}, { maxNodes: 400_000 });
  const foldedText = formatExact(foldedPow.value).replace(/\u200b/g, "");
  if (foldedPow.unverified || foldedText !== "0") {
    failed += 1;
    console.log("FAIL identical past-cap cancel", foldedPow.unverified ? "unverified" : foldedText);
  }
  // Exact zeros. A cap mark must not turn these into "couldn't verify".
  const zeroRows = [
    "0*10^-500",
    "10^-500*0",
    "ln(1)*10^-500",
    "(0-10^-433)+10^-433",
    "(exp(-1000)+exp(-1000))-2*exp(-1000)",
    "(0-10^-500)*0",
  ];
  const zeroNodes = zeroRows.map((source) => compileExpression(source, {}));
  for (const [i, source] of zeroRows.entries()) {
    const report = exactReport(zeroNodes[i], {}, { maxNodes: 400_000 });
    const text = formatExact(report.value).replace(/\u200b/g, "");
    if (report.unverified || text !== "0") {
      failed += 1;
      console.log("FAIL exact tiny zero", source, report.unverified ? "unverified" : text);
    } else {
      console.log("zero", source, text);
    }
  }
  const tinyJobs = [
    ...tinyRows.flatMap(([source, want], i) => {
      // JSON has no −0, so the typed −0 control stays in this process.
      if (source === "-0") return [];
      const packed = packCircuit(tinyNodes[i]);
      return [{ source, tokens: packed.tokens, root: packed.root, unverified: false, want, either: false }];
    }),
    ...lostRows.map((source, i) => {
      const packed = packCircuit(lostNodes[i]);
      return { source, tokens: packed.tokens, root: packed.root, unverified: true, want: "0", either: false };
    }),
    ...zeroRows.map((source, i) => {
      const packed = packCircuit(zeroNodes[i]);
      return { source, tokens: packed.tokens, root: packed.root, unverified: false, want: "0", either: false };
    }),
    ...eitherRows.map(([source, want], i) => {
      const packed = packCircuit(eitherNodes[i]);
      return { source, tokens: packed.tokens, root: packed.root, unverified: false, want, either: true };
    }),
  ];
  const tinyFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(tinyJobs), 300_000);
  if (tinyFresh.status !== 0) {
    failed += 1;
    console.log("FAIL fresh tiny underflow", tinyFresh.status, tinyFresh.stderr);
  } else {
    const rows = JSON.parse(tinyFresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
    for (const row of rows) {
      const job = tinyJobs.find((item) => item.source === row.source);
      const text = row.text.replace(/\u200b/g, "");
      if (!job) continue;
      if (job.either) {
        if (row.unverified || text === job.want) continue;
        failed += 1;
        console.log("FAIL fresh past-cap sub", row.source, text);
      } else if (job.unverified) {
        const collapsed = text === "0" || text === "−0";
        if (!row.unverified || !collapsed) {
          failed += 1;
          console.log("FAIL fresh lost tiny", row.source, row.unverified ? "unverified" : text);
        }
      } else if (row.unverified || text !== job.want) {
        failed += 1;
        console.log("FAIL fresh tiny", row.source, row.unverified ? "unverified" : text);
      }
    }
  }
}

// Identities that are exactly 0. A rounding residue, including one that
// holds still while the precision climbs, must come out 0 or unverified.
// A nearby difference, and a sum that does not cancel, stays a certified
// value. Both the packed worker and a fresh process.
const tinyCancelRows = [
  "exp(ln(1e-400))-1e-400",
  "1e-400*1.5/1.5-1e-400",
  "(1e-400)/2*2-(1e-400)",
  "1e-400/0.5/2-1e-400",
  "1e-400*(2^0.5)^2-2e-400",
  "1e-450*e/e-1e-450",
  "1e-500*e/e-1e-500",
  "1e-600*e/e-1e-600",
  "1e-200*(2^0.5)^2-2*1e-200",
  "1e-100*1.5/1.5-1e-100",
  "1e-50*1.5/1.5-1e-50",
  "1e-150*1.5/1.5-1e-150",
  "1e-320*pi/pi-1e-320",
  "1e-320*e/e-1e-320",
  "1e-320*3/3-1e-320",
  "exp(ln(1e-320))-1e-320",
  "1e-318*pi/pi-1e-318",
];
const tinyKeptRows: Array<[string, string]> = [
  ["1e-400-1e-400*(1+1e-50)", "−1×10^−450"],
  ["(1e-400)*3/3-(1e-400)*(1+1e-50)", "−1×10^−450"],
  ["1e-400*(1+1e-100)-1e-400", "1×10^−500"],
  ["1e-400*pi+1e-400", "4.14159265359×10^−400"],
  ["exp(-1000)-exp(-1001)", "3.20861797491×10^−435"],
];
function packedTinyReport(source: string) {
  const packed = packCircuit(compileExpression(source, {}));
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 400_000 });
}
const tinyShownText = (report: ReturnType<typeof exactReport>) => formatExact(report.value).replace(/\u200b/g, "");
function honestZero(report: ReturnType<typeof exactReport>) {
  if (report.unverified) return true;
  const text = tinyShownText(report);
  return text === "0" || text === "−0";
}

if (shardTurn(51)) {
  for (const source of tinyCancelRows) {
    const report = packedTinyReport(source);
    if (!honestZero(report)) {
      failed += 1;
      console.log("FAIL certified tiny cancel", source, tinyShownText(report));
    } else {
      console.log("cancel", source, report.unverified ? "couldn't verify" : tinyShownText(report));
    }
  }
}

if (shardTurn(61)) {
  for (const [source, want] of tinyKeptRows) {
    const report = packedTinyReport(source);
    const text = tinyShownText(report);
    if (report.unverified || text !== want) {
      failed += 1;
      console.log("FAIL tiny kept value", source, report.unverified ? "unverified" : text);
    } else {
      console.log("kept", source, text);
    }
  }
}

if (shardTurn(62)) {
  const cancelJobs = [...tinyCancelRows, ...tinyKeptRows.map(([source]) => source)].map((source) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root };
  });
  const cancelFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(cancelJobs), 300_000);
  if (cancelFresh.status !== 0) {
    failed += 1;
    console.log("FAIL fresh tiny cancel", cancelFresh.status, cancelFresh.stderr?.slice(0, 400));
  } else {
    const rows = JSON.parse(cancelFresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
    rows.forEach((row, index) => {
      const text = row.text.replace(/\u200b/g, "");
      if (index < tinyCancelRows.length) {
        const ok = row.unverified || text === "0" || text === "−0";
        if (!ok) {
          failed += 1;
          console.log("FAIL fresh certified tiny cancel", row.source, text);
        }
        return;
      }
      const want = tinyKeptRows[index - tinyCancelRows.length]?.[1];
      if (!want || row.unverified || text !== want) {
        failed += 1;
        console.log("FAIL fresh tiny kept value", row.source, row.unverified ? "unverified" : text, want);
      }
    });
  }
}

if (shardTurn(52)) {
  // Marked infinities. mpmath dps 50: ln(0) is -inf and 0/0 raises ZeroDivisionError.
  // tan(pi/2) there is the finite -1.9788349012695708716820519525808990497221781173111e+51,
  // because a 50-digit pi/2 is not the symbolic pole. The self-differences below are undefined,
  // with a singular flag, in both modes. (1/0)-(1/0) is the same kind of control.
  // exp(ln(0)) is 0, so that difference stays the folded 0.
  // mpmath dps 420: (10^400-1)-10^400 = -1, (10^400+1)-10^400 = 1,
  // 10^400-(10^400-1) = 1, (10^400-10^300)/10^300 = 10^100-1.
  // At dps 50, 10^100-1 prints as 1.0000000000000000000000000000000000000000000000000e+100,
  // the same text as 10^100. The exact check uses 110 digits, where they differ.
  const budget = { maxNodes: 400_000 };
  const undef = (source: string) => {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    if (formatC(hw.value) !== "undefined" || hw.singular === null || formatExact(ex.value) !== "undefined" || ex.singular === null) {
      failed += 1;
      console.log("FAIL marked cancellation", source, hw.singular, hw.value, ex.singular, formatExact(ex.value));
    }
  };
  undef("(0/0)-(0/0)");
  undef("tan(pi/2)-tan(pi/2)");
  undef("tan(3*pi/2)-tan(3*pi/2)");
  undef("ln(ln(0))-ln(ln(0))");
  undef("ln(0)-ln(0)");
  undef("tan(pi/2)+(-tan(pi/2))");
  undef("(0/0)+(-(0/0))");
  undef("(1/0)-(1/0)");

  const finiteZero = (source: string) => {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    if (hw.value.re !== 0 || hw.value.im !== 0 || hw.singular !== null || ex.singular !== null || !ex.value.re.isZero() || !ex.value.im.isZero()) {
      failed += 1;
      console.log("FAIL finite cancellation", source, hw.singular, hw.value, ex.singular, formatExact(ex.value));
    }
  };
  finiteZero("exp(ln(0))-exp(ln(0))");
  const zeroGates = circuitStats(compileExpression("0", {})).dagGates;
  const sinDiff = compileExpression("sin(1)-sin(1)", {});
  const sinGates = circuitStats(compileExpression("sin(1)", {})).dagGates;
  if (circuitStats(sinDiff).dagGates !== zeroGates || sinGates <= zeroGates) {
    failed += 1;
    console.log("FAIL sin(1)-sin(1) was not the folded zero", circuitStats(sinDiff).dagGates, sinGates, zeroGates);
  }
  finiteZero("sin(1)-sin(1)");
  const near = "tan(1.5707963267948966)-tan(1.5707963267948966)";
  const nearNode = compileExpression(near, {});
  if (circuitStats(nearNode).dagGates !== zeroGates) {
    failed += 1;
    console.log("FAIL nearby tan fold", circuitStats(nearNode).dagGates, zeroGates);
  }
  finiteZero(near);

  const expectInt = (source: string, wantNum: number, wantText: string) => {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    const text = formatExact(ex.value).replace(/\u200b/g, "");
    if (hw.value.re !== wantNum || hw.value.im !== 0 || hw.singular !== null || ex.singular !== null || text !== wantText) {
      failed += 1;
      console.log("FAIL huge exact difference", source, hw.value, hw.singular, text, ex.singular);
    }
  };
  expectInt("(10^400-1)-10^400", -1, "−1");
  expectInt("(10^400+1)-10^400", 1, "1");
  expectInt("10^400-(10^400-1)", 1, "1");

  // mpmath dps 50. A finite non-integer beside 10^400 cancels back to itself.
  // i = 0 + i, −i = 0 − i, 0.5 = 0.5,
  // pi = 3.1415926535897932384626433832795028841971693993751,
  // sqrt(2) = 1.4142135623730950488016887242096980785696718753769.
  const beside = (source: string, re: string, im = "0") => {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    if (
      hw.singular !== null ||
      ex.singular !== null ||
      !close(hw.value, c(Number(re), Number(im)), 1e-12) ||
      !exactClose(ex.value, re, im, 40)
    ) {
      failed += 1;
      console.log("FAIL huge plus small part", source, hw.value, hw.singular, formatExact(ex.value), ex.singular);
    }
  };
  beside("(10^400+i)-10^400", "0", "1");
  beside("(10^400+pi)-10^400", "3.1415926535897932384626433832795028841971693993751");
  beside("(10^400+sqrt(2))-10^400", "1.4142135623730950488016887242096980785696718753769");
  beside("(10^400+0.5)-10^400", "0.5");
  beside("(10^400+(-i))-10^400", "0", "-1");

  const gap = exactReport(compileExpression("10^400-10^300", {}), {}, budget);
  const gapText = "9".repeat(100) + "0".repeat(300);
  if (exactClose(gap.value, "1e400", 0, 110) || !exactClose(gap.value, gapText, 0, 110)) {
    failed += 1;
    console.log("FAIL exact 10^400-10^300 dropped 10^300", formatExact(gap.value));
  }
  const quotNode = compileExpression("(10^400-10^300)/10^300", {});
  const quotHw = evaluateReport(quotNode, {}, budget);
  const quotEx = exactReport(quotNode, {}, budget);
  const nines = "9".repeat(100);
  const quotText = formatExact(quotEx.value).replace(/\u200b/g, "");
  if (
    !Number.isFinite(quotHw.value.re) ||
    Math.abs(quotHw.value.re - 1e100) / 1e100 > 1e-12 ||
    quotHw.value.im !== 0 ||
    quotHw.singular !== null ||
    quotEx.singular !== null ||
    quotText !== nines ||
    !exactClose(quotEx.value, nines, 0, 110) ||
    exactClose(quotEx.value, "1e100", 0, 110)
  ) {
    failed += 1;
    console.log("FAIL (10^400-10^300)/10^300", quotHw.value, quotHw.singular, quotText, quotEx.singular);
  }

  // mpmath: (10^400+3)-(10^400+1) = 2, (10^400+1)-(10^400+2) = -1,
  // ((10^400+3)+(10^400+1))-2*10^400 = 4,
  // (10^400+10^300)-(10^400-10^300) = 2*10^300,
  // (10^401+1)-(10^400+1) = 9*10^400.
  const two300 = `2${"0".repeat(300)}`;
  const nine400 = `9${"0".repeat(400)}`;
  const gap400 = `${"9".repeat(100)}${"0".repeat(300)}`;
  const expectDiff = (source: string, re: number, text: string) => {
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    const got = formatExact(ex.value).replace(/\u200b/g, "");
    if (hw.singular !== null || ex.singular !== null || !close(hw.value, c(re, 0), 1e-12) || got !== text) {
      failed += 1;
      console.log("FAIL distinct huge difference", source, hw.value, hw.singular, got, ex.singular);
    }
  };
  expectDiff("(10^400+3)-(10^400+1)", 2, "2");
  expectDiff("(10^400+1)-(10^400+2)", -1, "−1");
  expectDiff("((10^400+3)+(10^400+1))-2*10^400", 4, "4");
  const wideDiff = "(10^400+10^300)-(10^400-10^300)";
  const wideNode = compileExpression(wideDiff, {});
  const wideHw = evaluateReport(wideNode, {}, budget);
  const wideEx = exactReport(wideNode, {}, budget);
  if (
    wideHw.singular !== null ||
    wideEx.singular !== null ||
    !close(wideHw.value, c(2e300, 0), 1e-12) ||
    formatExact(wideEx.value).replace(/\u200b/g, "") !== "2×10^300" ||
    !exactClose(wideEx.value, two300, 0, 110)
  ) {
    failed += 1;
    console.log("FAIL 2*10^300 gap", wideHw.value, wideHw.singular, formatExact(wideEx.value), wideEx.singular);
  }
  const nineNode = compileExpression("(10^401+1)-(10^400+1)", {});
  const nineHw = evaluateReport(nineNode, {}, budget);
  const nineEx = exactReport(nineNode, {}, budget);
  if (
    nineHw.value.re !== Infinity ||
    nineHw.value.im !== 0 ||
    nineEx.singular !== null ||
    formatExact(nineEx.value).replace(/\u200b/g, "") !== "9×10^400" ||
    !exactClose(nineEx.value, nine400, 0, 110)
  ) {
    failed += 1;
    console.log("FAIL 9*10^400", nineHw.value, nineHw.singular, formatExact(nineEx.value), nineEx.singular);
  }

  const carried = (source: string) => {
    const packed = packCircuit(compileExpression(source, {}));
    return packed.tokens.flatMap((tok) => ("int" in tok && tok.int ? [tok.int] : []));
  };
  const expectCarried = (source: string, digits: string) => {
    if (!carried(source).includes(digits)) {
      failed += 1;
      console.log("FAIL integer missing on the wire", source);
    }
  };
  expectCarried("(10^401+1)-(10^400+1)", nine400);
  expectCarried("(10^400-10^300)/10^300", nines);
  expectCarried("10^400-10^300", gap400);
  expectCarried(wideDiff, two300);
  expectCarried("(10^400+1)/7", `${"1"}${"0".repeat(399)}1`);

  // A fresh process has an empty mark table. Same-process unpack reuses interned leaves.
  const wireRows: { source: string; re: string; im?: string; digits?: number; text?: string }[] = [
    { source: "(10^400-1)-10^400", re: "-1", text: "−1" },
    { source: "(10^400+1)-10^400", re: "1", text: "1" },
    { source: "10^400-(10^400-1)", re: "1", text: "1" },
    { source: "(10^400+i)-10^400", re: "0", im: "1" },
    { source: "(10^400+pi)-10^400", re: "3.1415926535897932384626433832795028841971693993751" },
    { source: "(10^400+sqrt(2))-10^400", re: "1.4142135623730950488016887242096980785696718753769" },
    { source: "(10^400+0.5)-10^400", re: "0.5", text: "0.5" },
    { source: "(10^400+(-i))-10^400", re: "0", im: "-1" },
    { source: "(10^400+3)-(10^400+1)", re: "2", text: "2" },
    { source: "(10^400+1)-(10^400+2)", re: "-1", text: "−1" },
    { source: "((10^400+3)+(10^400+1))-2*10^400", re: "4", text: "4" },
    { source: wideDiff, re: two300, digits: 110, text: "2×10^300" },
    { source: "(10^401+1)-(10^400+1)", re: nine400, digits: 110, text: "9×10^400" },
    { source: "(10^400-10^300)/10^300", re: nines, digits: 110, text: nines },
    { source: "10^400-10^300", re: gap400, digits: 110 },
    { source: "(10^400+1)/7", re: "1.428571428571428571428571e+399", digits: 20 },
  ];
  const wireJobs = wireRows.map((row) => {
    const packed = packCircuit(compileExpression(row.source, {}));
    return { source: row.source, tokens: packed.tokens, root: packed.root, re: row.re, im: row.im, digits: row.digits };
  });
  const wire = runTsx("scripts/fresh-exact.ts", JSON.stringify(wireJobs));
  if (wire.status !== 0) {
    failed += 1;
    console.log("FAIL fresh huge integer", wire.status, wire.stderr);
  } else {
    const rows = JSON.parse(wire.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; close?: boolean }>;
    for (const row of rows) {
      const want = wireRows.find((item) => item.source === row.source);
      const text = row.text.replace(/\u200b/g, "");
      if (row.unverified || row.singular !== null || row.close !== true || (want?.text !== undefined && text !== want.text)) {
        failed += 1;
        console.log("FAIL fresh huge", row.source, row.unverified ? "unverified" : text, row.singular, row.close);
      }
    }
  }

  // Identical nodes cancel to 0. mpmath at 1,200 digits is 0.
  // Two huge-carried terms whose small parts are not both exact integers are unverified, never a value.
  // (10^400+1)+(10^400+1) is the integer 2×10^400+2. A 1,200-digit compare sees the units digit.
  // The parser has no juxtaposition, so 2(10^400+pi) is written 2*(10^400+pi).
  const twoPlus = `2${"0".repeat(399)}2`;
  const cancelRows = [
    "(10^400+pi)+(-(10^400+pi))",
    "(10^400+i)+(-(10^400+i))",
    "(10^400+sqrt(2))+(-(10^400+sqrt(2)))",
    "(10^400+e)+(-(10^400+e))",
    "(10^400+0.5)+(-(10^400+0.5))",
    "(10^400+pi)-(10^400+pi)",
    "(10^400+i)-(10^400+i)",
    "(10^400+sqrt(2))-(10^400+sqrt(2))",
    "(10^400+e)-(10^400+e)",
  ];
  const flagRows = [
    "(10^400+pi)+(-(10^400+e))",
    "(10^400+pi)-(10^400+1)",
    "(10^400+1)-(10^400+i)",
    "(10^400+i)-(10^400+(-i))",
    "(10^400+sqrt(2))-(10^400+0.5)",
    "(10^400+pi)-(10^400+e)",
    "2*(10^400+pi)-2*10^400",
    "(10^400+i)-(10^400-i)",
    "-(10^400+pi)+10^400",
    "(10^400+1)+(-(10^400+i))",
    "(10^400+pi)+(-(10^400+1))",
    "(10^400+3)+(-(10^400+pi))",
    "(10^400+e)-(10^400+0.5)",
    "(10^400+i)+(10^400+i)",
    "(10^400+i)+(10^400+(-i))",
  ];
  const bareRows = ["10^400+pi", "10^400+i", "10^400-0.5"];
  const hugeJobs: { source: string; tokens: ReturnType<typeof packCircuit>["tokens"]; root: number; re?: string; digits?: number }[] = [];
  const timeCancel = (source: string) => {
    const started = performance.now();
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    const ms = performance.now() - started;
    const text = formatExact(ex.value).replace(/\u200b/g, "");
    const ok =
      ms < 200 &&
      hw.unverified !== true &&
      ex.unverified !== true &&
      hw.singular === null &&
      ex.singular === null &&
      close(hw.value, c(0, 0), 1e-12) &&
      text === "0" &&
      exactClose(ex.value, "0", "0", 1200);
    if (!ok) {
      failed += 1;
      console.log("FAIL identical cancel", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : text);
    } else {
      console.log("cancel", source, "exact 0", `${ms.toFixed(1)}ms`);
    }
    const packed = packCircuit(node);
    hugeJobs.push({ source, tokens: packed.tokens, root: packed.root, re: "0", digits: 1200 });
  };
  for (const source of cancelRows) timeCancel(source);
  const timeFlag = (source: string) => {
    const started = performance.now();
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    const ms = performance.now() - started;
    if (ms >= 200 || hw.unverified !== true || ex.unverified !== true) {
      failed += 1;
      console.log("FAIL unverified huge pair", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : formatExact(ex.value));
    } else {
      console.log("flag", source, "unverified", `${ms.toFixed(1)}ms`);
    }
    const packed = packCircuit(node);
    hugeJobs.push({ source, tokens: packed.tokens, root: packed.root });
  };
  for (const source of flagRows) timeFlag(source);
  const timeBare = (source: string) => {
    const started = performance.now();
    const node = compileExpression(source, {});
    const hw = evaluateReport(node, {}, budget);
    const ex = exactReport(node, {}, budget);
    const ms = performance.now() - started;
    const text = formatExact(ex.value).replace(/\u200b/g, "");
    const floatDropped = hw.unverified !== true && Number.isFinite(hw.value.re) && Number.isFinite(hw.value.im);
    if (ms >= 200 || ex.unverified !== true || floatDropped) {
      failed += 1;
      console.log("FAIL bare huge sum", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : text);
    } else {
      console.log("bare", source, "unverified", `${ms.toFixed(1)}ms`);
    }
    const packed = packCircuit(node);
    hugeJobs.push({ source, tokens: packed.tokens, root: packed.root });
  };
  for (const source of bareRows) timeBare(source);
  const intSource = "(10^400+1)+(10^400+1)";
  const intStarted = performance.now();
  const intNode = compileExpression(intSource, {});
  const intHw = evaluateReport(intNode, {}, budget);
  const intEx = exactReport(intNode, {}, budget);
  const intMs = performance.now() - intStarted;
  const intText = formatExact(intEx.value).replace(/\u200b/g, "");
  if (
    intMs >= 200 ||
    intHw.unverified === true ||
    intEx.unverified === true ||
    intHw.value.re !== Infinity ||
    intHw.value.im !== 0 ||
    intEx.singular !== null ||
    intText !== twoPlus ||
    !exactClose(intEx.value, twoPlus, "0", 1200) ||
    exactClose(intEx.value, `2${"0".repeat(400)}`, "0", 1200)
  ) {
    failed += 1;
    console.log("FAIL exact 2*10^400+2", `${intMs.toFixed(1)}ms`, intHw.value, intHw.unverified, intEx.unverified ? "unverified" : intText.slice(0, 12), intEx.singular);
  } else {
    console.log("int", intSource, "2×10^400+2", `${intMs.toFixed(1)}ms`);
  }
  const intPacked = packCircuit(intNode);
  hugeJobs.push({ source: intSource, tokens: intPacked.tokens, root: intPacked.root, re: twoPlus, digits: 1200 });
  const hugeWire = runTsx("scripts/fresh-exact.ts", JSON.stringify(hugeJobs));
  if (hugeWire.status !== 0) {
    failed += 1;
    console.log("FAIL fresh huge pairs", hugeWire.status, hugeWire.stderr);
  } else {
    const rows = JSON.parse(hugeWire.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; close?: boolean; ms: number }>;
    for (const row of rows) {
      const text = row.text.replace(/\u200b/g, "");
      const wantFlag = flagRows.includes(row.source) || bareRows.includes(row.source);
      const freshOk = wantFlag
        ? row.unverified === true && row.ms < 200
        : row.unverified !== true && row.singular === null && row.close === true && row.ms < 200 && (row.source === intSource ? text === twoPlus : text === "0");
      if (!freshOk) {
        failed += 1;
        console.log("FAIL fresh huge pair", row.source, `${row.ms}ms`, row.unverified ? "unverified" : text, row.singular, row.close);
      } else {
        console.log("fresh", row.source, wantFlag ? "unverified" : text === twoPlus ? "2×10^400+2" : "exact 0", `${row.ms}ms`);
      }
    }
  }
}

if (shardTurn(53)) {
  // Outside review, section A. Each row fails while its claim holds.
  // A1: an angle within the snap tolerance of 0 is not the axis. sin(6.103e-120) is not 0,
  // so the doubled tiny imaginary sum keeps both halves (or says it could not verify).
  const tinyTwice = exactReport(compileExpression("6.103e-120*i + 6.103e-120*i", {}));
  const tinyTwiceText = formatExact(tinyTwice.value);
  if (!tinyTwice.unverified && tinyTwiceText !== "1.2206×10^−119i") {
    failed += 1;
    console.log("FAIL review A1 tiny imaginary sum", tinyTwiceText);
  } else {
    console.log("review A1 tiny imaginary sum", tinyTwice.unverified ? "couldn't verify" : tinyTwiceText);
  }
  // exp of a tiny imaginary angle. Float gives 1 + 6.1e-120i, so an exact 1 with no note drops a component.
  const tinyTurn = exactReport(compileExpression("exp(6.103515625e-120*i)", {}));
  const tinyTurnText = formatExact(tinyTurn.value);
  if (!tinyTurn.unverified && !tinyTurn.singular && tinyTurn.value.im.isZero()) {
    failed += 1;
    console.log("FAIL review A1 tiny turn", tinyTurnText);
  } else {
    console.log("review A1 tiny turn", tinyTurn.unverified ? "couldn't verify" : tinyTurnText, tinyTurn.singular ?? "");
  }
  // A tiny real part beside an imaginary one. The real part is a known 10^(−130) or
  // 10^(−136), so 0.5i or 1.5i alone drops it. Direct here, and packed in a fresh process
  // below in both orders, so cache hits and misses are both covered.
  const tinyBesideRows: Array<[string, string]> = [
    ["((1+10^(-130))-1)+i/2", "1×10^−130 + 0.5i"],
    ["(i*(1+10^-130)-i)*i+i/2", "−1×10^−130 + 0.5i"],
    ["((1+10^(-136))-1)+i*3/2", "1×10^−136 + 1.5i"],
  ];
  for (const [source, want] of tinyBesideRows) {
    const report = exactReport(compileExpression(source, {}));
    const text = report.unverified ? "unverified" : formatExact(report.value);
    if (text !== want && text !== "unverified") {
      failed += 1;
      console.log("FAIL tiny real beside imaginary", source, text);
    } else {
      console.log("tiny real beside imaginary", source, text);
    }
  }
  const besideJobs = tinyBesideRows.map(([source]) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root, again: true as const };
  });
  for (const jobs of [besideJobs, [...besideJobs].reverse()]) {
    const run = runTsx("scripts/fresh-exact.ts", JSON.stringify(jobs));
    if (run.status !== 0) {
      failed += 1;
      console.log("FAIL fresh tiny real beside imaginary", run.status, run.stderr?.slice(0, 400));
      continue;
    }
    for (const row of JSON.parse(run.stdout) as Array<{ source: string; text: string; unverified: boolean; again?: string }>) {
      const want = tinyBesideRows.find(([source]) => source === row.source)?.[1];
      const first = row.unverified ? "unverified" : row.text;
      const ok = (text: string | undefined) => text === want || text === "unverified";
      if (!ok(first) || !ok(row.again)) {
        failed += 1;
        console.log("FAIL fresh tiny real beside imaginary", row.source, first, row.again);
      }
    }
  }
  // A2: a word built with no lowering notes, evaluated twice on the same node in a
  // fresh process. The second pass reads the var-free cache and must still find the
  // cancellation that the first pass recovered.
  const lossSource = "exp(10^(-115))-1";
  const lossWord = rpnTokens(compileExpression(lossSource, {}), 100_000);
  // A4: the worker receives a packed circuit. Its singular note must match the main thread.
  const noteRows: Array<[string, Record<string, { re: number; im: number }>]> = [
    ["asinh(x)", { x: c(1e-13) }],
    ["x+y", { x: c(1e-20), y: c(1e-20) }],
  ];
  const noteMain = noteRows.map(([source, env]) => exactReport(compileExpression(source, { x: V("x"), y: V("y") }), env).singular);
  const reviewJobs = [
    ...(lossWord ? [{ source: lossSource, word: lossWord, again: true }] : []),
    ...noteRows.map(([source, env]) => {
      const packed = packCircuit(compileExpression(source, { x: V("x"), y: V("y") }));
      return { source, tokens: packed.tokens, root: packed.root, env };
    }),
  ];
  const reviewFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(reviewJobs));
  if (!lossWord || reviewFresh.status !== 0) {
    failed += 1;
    console.log("FAIL review A fresh run", lossWord ? lossWord.length : "no word", reviewFresh.status, reviewFresh.stderr?.slice(0, 400));
  } else {
    const rows = JSON.parse(reviewFresh.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; again?: string }>;
    const [loss, ...notes] = rows;
    const shown = (text: string, unverified: boolean) => (unverified ? "unverified" : text);
    const first = loss ? shown(loss.text, loss.unverified) : "missing";
    const second = loss?.again ?? "missing";
    const honest = (text: string) => text === "1×10^−115" || text === "unverified";
    if (!honest(first) || !honest(second)) {
      failed += 1;
      console.log("FAIL review A2 cached word", lossSource, "first", first, "second", second);
    } else {
      console.log("review A2 cached word", lossSource, first, second);
    }
    notes.forEach((row, index) => {
      const want = noteMain[index] ?? null;
      if (row.singular !== want) {
        failed += 1;
        console.log("FAIL review A4 worker note", row.source, "worker", row.singular, "main", want);
      } else {
        console.log("review A4 worker note", row.source, row.singular);
      }
    });
  }
}

// Release refusals: a large trig argument below the root, a part cancelled to 0
// beside a nonzero part after a value below the precision, a finite overflow
// operand, inf·0, and the tiny sinh/artanh shortcut are refused, not certified.
const releaseRefused = ["-cos(1e119)", "cos(1e119)+1", "cos(1e125)*cos(1e130)", "tan(1e140)+1", "((1+exp(-299.3))-1)+i/2", "(exp(exp(-300))-1)+i/2", "((1+exp(-300))-1)*i+1/2", "((1+10^-500)-1)+i/2", "i*((1+10^-500)-1)+1/2", "(10^400+i)*2", "2*(10^400+pi)", "(10^400+i)/7", "exp(((1+10^-500)-1)*i)", "(exp(800)+1)-exp(800)", "exp(800)*0", "sinh(1e-7)-1e-7", "artanh(1e-7)-1e-7", "cos(10^119)+1", "cos(2^400)+1", "sin(1e22)+1", "arcsin(1e-300)-1e-300", "tanh(130)", "tanh(200)", "tanh(354)", "sinh(5e-7)-5e-7", "sinh(1e-7*i)-1e-7*i", "(10^400-(2-2*i))^-1", "(1+(10^400+pi))-2", "(1+(10^400+pi))*2", "((cos(10^-50))+((10^400)+(pi)))-(((e)^0.5)+(((1+10^-200))+((-1+1*i))))", "tanh(10^300)", "tanh(10^20)", "tanh(-10^300)", "tanh(exp(800))", "asin((-1)/(10^-200))", "asinh(1/10^-200)", "acosh(asinh(10^400))", "exp(-10^20)", "(cosh(10^50))^(-2)", "1/cosh(10^50)"];
function releaseRefusal(source: string): void {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  const seen = [exactReport(node), exactReport(node), exactReport(unpackCircuit(packed.tokens, packed.root))];
  if (seen.some((report) => !report.unverified)) {
    failed += 1;
    console.log("FAIL release refusal", source, seen.map((report) => formatExact(report.value)).join(" | "));
  } else console.log("release refusal", source);
}
// A large real product passes through its reciprocal; that tiny real cannot reach the
// zero imaginary part, so these stay certified (v1.0.1 refused every one of them).
// atanh of a real above 1 is −iπ/2, and arctan of iy with y < −1 is −π/2 + …i,
// however the argument was built (mpmath's atanh and atan).
// A point just below the negative real axis keeps its side through a composition
// (mpmath at 600 digits); past 480 digits that side cannot be read, so it is refused.
const releaseKept: [string, string][] = [["1e-320*e/e-1e-320*(1+1e-100)", "−1×10^−420"], ["1e-320*(1+1e-100)-1e-320", "1×10^−420"], ["exp(-1000)+1", "1"], ["1e-400*pi+1e-400", "4.14159265359×10^−400"], ["((1+10^(-136))-1)+i*3/2", "1×10^−136 + 1.5i"], ["exp(800)-exp(800)", "0"], ["0^0", "1"], ["(1-1)^0", "1"], ["0^(1-1)", "1"], ["2^0", "1"], ["ln(0)^0", "unverified"], ["10^400/7", "1.428571428571×10^399"], ["10^400*2", "2×10^400"], ["10^400*i", "1×10^400i"], ["-(10^400)/3", "−3.333333333333×10^399"], ["10^300*10^100", "1×10^400"], ["atanh(1.694^3)", "0.208689790346 − 1.570796326795i"], ["atanh(-(1.5^3))", "−0.305454541161 + 1.570796326795i"], ["atanh(1.694^3)*atanh(32)", "−2.460877420177 − 0.376912529663i"], ["atan((-i-i)*asinh(9))", "−1.570796326795 − 0.174556001875i"], ["atan(-i*(1.5^3))", "−1.570796326795 − 0.305454541161i"], ["atan(i*(1.5^3))", "1.570796326795 + 0.305454541161i"], ["(10^108-i)*sin(atanh(-i))", "−0.868670961486 − 8.68670961486×10^107i"], ["(10^106-i)*sin(atanh(-i))", "−0.868670961486 − 8.68670961486×10^105i"], ["(10^300-(2-2*i))^-1", "1×10^−300 − 2×10^−600i"], ["1/(10^300-(2-2*i))", "1×10^−300 − 2×10^−600i"], ["(10^300+2)^-1", "1×10^−300"], ["((1+1/10^130)-1)+i/2", "1×10^−130 + 0.5i"], ["((1+1/10^130)-1)*i+1/2", "0.5 + 1×10^−130i"], ["((1+1/10^300)-1)+i/2", "unverified"], ["acos(1+10^-16)", "0.000000014142i"], ["((i)*(6))-(acos((1+10^-16)))", "5.999999985858i"], ["acos(1-10^-200)", "1.414213562373×10^−100"], ["acos(-1-10^-200)", "3.14159265359 − 1.414213562373×10^−100i"], ["acos(2/2)", "0"], ["acos(cos(0))", "0"], ["acos(-(2/2))", "3.14159265359"], ["atanh(2/exp(300))", "1.029640044482×10^−130"], ["atanh(((-3)-(-5))/(sqrt(exp(600))))", "1.029640044482×10^−130"], ["sin(2/exp(300))", "1.029640044482×10^−130"], ["sin(2/exp(200))", "2.767793053473×10^−87"], ["sinh(10^300*i)", "−0.98575042516i"], ["cosh(10^20*i)", "0.763970404442"], ["ln(0)-ln(0)", "undefined"], ["0/0", "undefined"], ["1+exp(-10^20)", "1"], ["ln(ln(-5-i*10^-300))", "1.261257534955 − 1.097357207506i"], ["sqrt(acosh(-2-i*10^-120))", "1.536785569226 − 1.022131101599i"], ["acos(atanh(-5-i*10^-120))", "1.679425334464 + 1.238394314276i"], ["(-1/2-i*10^-120)^(1+i)", "−8.90036048882 + 7.393003249711i"], ["ln(-2-i*10^-300)-(2+3*i)^(-5)", "0.692818599089 − 3.143200548164i"], ["ln(ln(-5-i*10^-450))", "unverified"], ["sqrt(-4-i*10^-200)", "2.5×10^−201 − 2i"], ["(-8-i*10^-300)^(1/3)", "1 − 1.732050807569i"]];
function releaseKeptValue(source: string, want: string): void {
  const report = exactReport(compileExpression(source, {}));
  const got = report.unverified ? "unverified" : formatExact(report.value);
  if (got !== want) {
    failed += 1;
    console.log("FAIL release kept", source, got, "want", want);
  } else console.log("release kept", source, got);
}

if (shardTurn(54)) {
  // Parser messages say what to type: implicit products, a function without
  // parentheses, an unknown function, and a doubled operator.
  const messages: [string, string][] = [
    ["2pi", "Put * between “2” and “pi”."],
    ["2(3)", "Put * between “2” and “(”."],
    ["sin 1", "Write sin with parentheses, as sin(1)."],
    ["abs(-2)", "Unknown function “abs”."],
    ["2^^3", "A value is missing before “^”."],
    ["foo", "Unknown name “foo”. Use x, y, pi, e, i, or inf."],
  ];
  for (const [source, want] of messages) {
    let got = "compiled";
    try {
      compileExpression(source, {});
    } catch (err) {
      got = err instanceof EmlError ? err.message : String(err);
    }
    if (got !== want) {
      failed += 1;
      console.log("FAIL parser message", source, got, "want", want);
    } else console.log("parser message", source, got);
  }

  // A subtree shared through both inputs at every level: its cancellation records
  // are kept once, so 40 levels finish quickly instead of doubling per level.
  {
    let deep = E(ONE, ONE);
    for (let level = 0; level < 40; level += 1) deep = E(deep, deep);
    const started = Date.now();
    exactReport(deep, {}, { maxNodes: 80_000 });
    const took = Date.now() - started;
    if (took > 5000) {
      failed += 1;
      console.log("FAIL deep shared circuit", took, "ms");
    } else console.log("deep shared circuit", took, "ms");
  }
}

// The release rows run as four blocks so that no one block sets the CI shard floor.
if (shardTurn(57)) for (const source of releaseRefused.slice(0, 20)) releaseRefusal(source);

if (shardTurn(58)) for (const source of releaseRefused.slice(20)) releaseRefusal(source);

if (shardTurn(59)) for (const [source, want] of releaseKept.slice(0, 27)) releaseKeptValue(source, want);

if (shardTurn(60)) for (const [source, want] of releaseKept.slice(27)) releaseKeptValue(source, want);

// A repeat evaluation in one process (the exact worker is reused across jobs) must
// match an evaluation with the pure cache off: same text, same note, same verdict.
// Large trig arguments: each certified a wrong value on a repeat before (cos(1e119) → −0.98499,
// true −0.37226; cos(1e125/1e130/1e200) → 1; sin(1e150/1e300) → −0; tan(1e140) → −2.306, true −3.307).
const repeatBigTrig = [
  "cos(1e119)", "cos(1e125)", "cos(1e130)", "cos(1e200)", "sin(1e150)", "sin(1e300)", "tan(1e140)",
  "sin(10^22)", "tan(10^22)", "cos(10^7)", "cos(2^60)",
  "sin(1e23)", "cos(1e23)", "tan(1e23)", "sin(1e60)", "cos(1e60)", "tan(1e60)", "sin(1e250)", "cos(1e250)", "tan(1e300)",
];
const repeatRows = ["1-cos(sqrt(1/10^130))", "6*i+(-6*i)", "cos(1e100)", "sin(1e22)", "tan(1e100)", "tan(1e22)", "cos(1e7)", "tan(pi/2)", ...repeatBigTrig];
const warmRows = ["1e100", "1e22", "1e7", "1e119", "1e300", "sqrt(1/10^130)", "6*i", "pi/2"];
const repeatVerdict = (report: ReturnType<typeof exactReport>) =>
  `${report.unverified ? "unverified" : formatExact(report.value)} [${report.singular ?? ""}]`;
/** Each repeat row evaluated with the pure cache off: the reference for the repeat blocks. */
function repeatColdVerdicts(): string[] {
  const saved = process.env.EML_NOCACHE;
  process.env.EML_NOCACHE = "1";
  const cold = repeatRows.map((source) => repeatVerdict(exactReport(compileExpression(source, {}))));
  if (saved === undefined) delete process.env.EML_NOCACHE;
  else process.env.EML_NOCACHE = saved;
  return cold;
}

if (shardTurn(55)) {
  const cold = repeatColdVerdicts();
  repeatBigTrig.forEach((source) => {
    const want = cold[repeatRows.indexOf(source)];
    if (!want?.includes("argument too large to reduce")) {
      failed += 1;
      console.log("FAIL large trig argument not flagged", source, want);
    }
  });
  for (const source of warmRows) exactReport(compileExpression(source, {}));
  repeatRows.forEach((source, index) => {
    const node = compileExpression(source, {});
    const first = repeatVerdict(exactReport(node));
    const second = repeatVerdict(exactReport(node));
    const packed = packCircuit(node);
    const trip = repeatVerdict(exactReport(unpackCircuit(packed.tokens, packed.root)));
    if (first !== cold[index] || second !== cold[index] || trip !== cold[index]) {
      failed += 1;
      console.log("FAIL repeat evaluation", source, "cold", cold[index], "first", first, "second", second, "round trip", trip);
    } else {
      console.log("repeat evaluation", source, cold[index]);
    }
  });
}

if (shardTurn(63)) {
  const cold = repeatColdVerdicts();
  // The same rows in one shared fresh child after earlier jobs, each evaluated twice.
  const shared = [...warmRows, ...repeatRows].map((source) => {
    const packed = packCircuit(compileExpression(source, {}));
    return { source, tokens: packed.tokens, root: packed.root, again: true as const };
  });
  const run = runTsx("scripts/fresh-exact.ts", JSON.stringify(shared));
  if (run.status !== 0) {
    failed += 1;
    console.log("FAIL shared child repeat", run.status, run.stderr?.slice(0, 400));
  } else {
    const rows = JSON.parse(run.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; again?: string; againSingular?: string | null }>;
    for (const row of rows.slice(warmRows.length)) {
      const want = cold[repeatRows.indexOf(row.source)];
      const first = `${row.unverified ? "unverified" : row.text} [${row.singular ?? ""}]`;
      const second = `${row.again} [${row.againSingular ?? ""}]`;
      if (first !== want || second !== want) {
        failed += 1;
        console.log("FAIL shared child repeat", row.source, "cold", want, "first", first, "second", second);
      }
    }
  }
}

if (shardTurn(56)) {
  // A scaled add rebuilds its operands, so the add note's term is not a gate.
  // 2x + 1 near x = −1/2 kept no low-precision flag; x + 1 near −1 had one.
  // 10^(−300)·x + 1 printed 6.35×10^(−13) for 10^(−12) with no note.
  const vars = { x: V("x") };
  const lowRows: Array<[string, number]> = [["x+1", -1 + 1e-12], ["2*x+1", -0.5 + 1e-13], ["1e-300*x+1", -1e300 * (1 - 1e-12)]];
  for (const [source, x] of lowRows) {
    const report = evaluateReport(compileExpression(source, vars), { x: c(x) });
    if (report.singular !== SINGULAR_PRECISION) {
      failed += 1;
      console.log("FAIL add precision note", source, report.value, report.singular);
    } else console.log("add precision note", source);
  }
  const plain = evaluateReport(compileExpression("2*x+1", vars), { x: c(3) });
  if (plain.singular !== null || Math.abs(plain.value.re - 7) > 1e-12) {
    failed += 1;
    console.log("FAIL add precision note away from 0", plain);
  }
  // A preview past 20000 presses shows a prefix. The x in sin(sin(x)) is past it.
  const nested = pressPreviewForNode(compileExpression("sin(sin(x))", vars));
  if (!nested || nested.copyable || !nested.usesVariables || nested.preview.includes("x")) {
    failed += 1;
    console.log("FAIL long press preview names its variables", nested && { ...nested, full: nested.full.slice(0, 40), presses: nested.presses.toString() });
  }
  let tower: Node = ONE;
  for (let i = 0; i < 16; i += 1) tower = E(tower, tower);
  const constant = pressPreviewForNode(tower);
  if (!constant || constant.usesVariables) {
    failed += 1;
    console.log("FAIL long constant press preview", constant?.presses.toString());
  }
}

if (shardTurn(73)) {
  // A part made of a square or product of tiny inputs is not certified as 0. cosh(10^(−100))
  // is 1 + 5×10^(−201), which rounds to 1 at 120 digits, so cosh(10^(−100))^i certified 1.
  // A part that a raised reading shows and keeps is certified; past 480 digits it is refused.
  // A part that does not depend on the tiny inputs (a real function of a real) stays 0.
  const squareRows: Array<[string, string]> = [
    ["cosh(10^(-100))^i", "1 + 5×10^−201i"],
    ["cos(10^(-100))^i", "1 − 5×10^−201i"],
    ["cosh(10^(-100)*(1+i))", "1 + 1×10^−200i"],
    ["(1+2*10^(-120)*i)^(i/3)", "1 + 6.666666666667×10^−241i"],
    ["((1+10^(-110))-1)+i/2", "1×10^−110 + 0.5i"],
    ["cos(10^(-300))", "1"],
    ["cos(10^(-300))^2", "1"],
    ["tanh((1/3)*10^(-100)*i)", "3.333333333333×10^−101i"],
    ["cos(1+10^(-200)*i)", "0.540302305868 − 8.414709848079×10^−201i"],
  ];
  for (const [source, want] of squareRows) {
    const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
    const got = formatExact(report.value);
    if (report.unverified || got !== want) {
      failed += 1;
      console.log("FAIL squared tiny part", source, got, report.unverified ? "unverified" : "certified", "want", want);
    } else console.log("squared tiny part", source, got);
  }
  // True parts 2×10^(−500) i and 5×10^(−601) i: past the cap, so not certified.
  // A refused huge sum inside atanh or atan is refused, not undefined (it was √0/√0).
  for (const source of ["cos(2*10^(-250))^(-i)", "cosh(10^(-300))^i", "atanh(exp(-50)-10^400)", "atan(10^400-6+i)", "atan(10^400+i)"]) {
    const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
    if (!report.unverified || report.singular !== null) {
      failed += 1;
      console.log("FAIL refused tiny or huge part", source, formatExact(report.value), report.singular);
    } else console.log("refused", source);
  }
}

closeBlockTimer();
if (shardCount > 1) console.log(`shard ${shardIndex}/${shardCount}`);
if (shardTurn(74)) {
  // The 671-press word for ln(1+10^(−130)) was listed as able to show an exact 0
  // depending on the cache. Built from its presses, alone, after the named
  // expression, and through the worker's wire, it is 10^(−130) every time.
  const named = compileExpression("ln(1+10^-130)", {});
  const words = rpnTokens(named, Number(circuitStats(named).rpnLength));
  const texts: string[] = [];
  if (words) {
    const read = (node: Node) => {
      const report = exactReport(node, {}, { maxNodes: 80_000 });
      return report.unverified ? "unverified" : formatExact(report.value);
    };
    texts.push(read(isolateCircuit(() => nodeFromRpn(words))));
    texts.push(read(named));
    texts.push(read(nodeFromRpn(words)));
    const packed = packCircuit(nodeFromRpn(words));
    texts.push(read(isolateCircuit(() => unpackCircuit(packed.tokens, packed.root))));
  }
  if (!words || words.length !== 671 || texts.some((text) => text !== "1×10^−130")) {
    failed += 1;
    console.log("FAIL press word of ln(1+10^-130)", words?.length, texts);
  }
}

if (shardTurn(75)) {
  // The calculator builds the key captions in slices from keyCostEntries, with
  // other circuits built in between. The table must not depend on that.
  const four = { node: compileExpression("2*2", {}) };
  const tables = [
    { stack: [four], want: "add=K 89 sub=K 81 mul=K 87 div=K 87 pow=K 95 log=K 99 avg=K 133 hypot=K 233" },
    { stack: [four, four], want: "add=K 123 sub=K 7 mul=K 121 div=K 121 pow=K 129 log=K 133 avg=K 167 hypot=K 301" },
  ];
  for (const { stack, want } of tables) {
    const whole = keyCosts(stack, "0.5", "2");
    const sliced: Record<string, string> = {};
    for (const [id, caption] of keyCostEntries(stack, "0.5", "2")) {
      sliced[id] = caption;
      compileExpression("3+5", {});
    }
    const binary = ["add", "sub", "mul", "div", "pow", "log", "avg", "hypot"].map((id) => `${id}=${sliced[id]}`).join(" ");
    if (JSON.stringify(whole) !== JSON.stringify(sliced) || binary !== want) {
      failed += 1;
      console.log("FAIL key captions", stack.length, binary);
    }
  }
}

if (shardTurn(76)) {
  // A submit compiles in the turn after the event (components/submitTurn.ts),
  // so key captions and other circuits can be built in between. Compiling
  // starts its own isolateCircuit, and what the screen reads from the node
  // must not depend on what was built before or after it.
  const summary = (node: Node) => {
    const stats = circuitStats(node);
    const packed = packCircuit(node);
    const report = evaluateReport(node, {}, { maxNodes: 80_000 });
    return JSON.stringify([
      stats.rpnLength.toString(), stats.dagGates, stats.depth, programNumberText(node),
      packed.tokens.length, packed.root, formatC(report.value), report.singular, report.unverified ?? false,
    ]);
  };
  const four = { node: compileExpression("2*2", {}) };
  for (const source of ["tan(10^(-5000))", "x+y", "ln(-1)"]) {
    const alone = summary(compileSubmission(source, "0.5", "2").node);
    for (const [id] of keyCostEntries([four], "0.5", "2")) if (id === "add") break;
    const late = compileSubmission(source, "0.5", "2");
    for (const entry of keyCostEntries([four, { node: late.node }], "0.5", "2")) void entry;
    const after = summary(late.node);
    if (alone !== after) {
      failed += 1;
      console.log("FAIL submit compiled between other circuits", source, alone, after);
    }
  }
  const bound = compileSubmission("x*y", "0.5", "2").numbers;
  if (!close(bound.x, c(0.5, 0), 1e-12) || !close(bound.y, c(2, 0), 1e-12) || "y" in compileSubmission("x+1", "0.5", "").numbers) {
    failed += 1;
    console.log("FAIL submit x and y", JSON.stringify(bound));
  }
  let missing = "";
  try {
    compileSubmission("x+y", "0.5", " ");
  } catch (err) {
    missing = err instanceof EmlError ? err.message : String(err);
  }
  if (missing !== "Give y a value.") {
    failed += 1;
    console.log("FAIL submit empty y", missing);
  }
}

if (shardTurn(83)) {
  // a − (a + 0) is +0. A 16-digit literal ending in 0 is (its prefix)·10 + 0, so
  // 1234567890123456*10 − 12345678901234560 folded to −(0) = −0, and ln of it was
  // a certified −∞ + iπ where ln(2*10 − 20) is −∞.
  const rows: [string, string][] = [
    ["1234567890123456*10-12345678901234560", "0"],
    ["ln(1234567890123456*10-12345678901234560)", "−∞"],
    ["1/(1234567890123456*10-12345678901234560)", "∞"],
    ["12345678901234567890*10-123456789012345678900", "0"],
    ["123456789012345678900-12345678901234567890*10", "0"],
    ["12345678901234567891-12345678901234567890", "1"],
  ];
  for (const [source, want] of rows) {
    const report = workerReport(source);
    const got = report.unverified ? "unverified" : formatExact(report.value);
    const floated = formatC(evaluate(compileExpression(source, {})));
    if (got !== want || floated !== want) {
      failed += 1;
      console.log("FAIL sum complement zero", source, got, floated, "want", want);
    }
  }
}

if (failed) {
  console.log(`\n${failed} failed`);
  process.exit(1);
}
console.log("all passed");
