import { readFileSync, rmSync, writeFileSync } from "node:fs";
import DecimalValue from "decimal.js";
import { spawnSync } from "node:child_process";
import { runPropertyChecks } from "./check-properties";
import path from "node:path";
import { c, casinh, cdiv, cexp, close, clog, cmul, csin, ctan, eml } from "./complex";
import { applyModeSwitch, commitHistory, compareVerdict, exactProgressNote, fillNotice, withholdZeroName, drainQueue, exactScreen, finiteLossMessage, modeRequest, underflowDisclosure, undoHistory } from "./history";
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
import { domainAdd, domainSub, naiveSub, rangeOf, rotSubCircuit } from "./lowering";
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
import { agreementNote, compileExpression, referenceExpression, referenceLostTerm } from "./parse";
import { packCircuit, unpackCircuit } from "./wire";
import { SHORT_PROGRAMS, applyProgram, nodeFromCompact, programK, programNode } from "./programs";
import table from "./best-known.json";

let failed = 0;
/**
 * CI shards (v1.1): --shard=core|isolate|props (or EML_CHECK_SHARD) runs one third of the suite; unset or
 * "all" runs everything, as before. Every top-level block belongs to exactly one shard, so
 * the three shards together run each check once. "isolate" holds the blocks that collect
 * isolateCases plus the isolate rebuild child; "props" holds runPropertyChecks and the two
 * big float/exact agreement blocks. Top-level statements outside blocks are cheap and run in
 * every shard.
 */
const SHARDS = ["core", "isolate", "props"] as const;
const SHARD = process.argv.find((arg) => arg.startsWith("--shard="))?.slice("--shard=".length) || process.env.EML_CHECK_SHARD || "all";
if (SHARD !== "all" && !(SHARDS as readonly string[]).includes(SHARD)) {
  console.log(`FAIL unknown EML_CHECK_SHARD ${JSON.stringify(SHARD)} (use ${SHARDS.join(", ")} or all)`);
  process.exit(1);
}
function inShard(name: (typeof SHARDS)[number]): boolean {
  return SHARD === "all" || SHARD === name;
}
const isolateCases: { source: string; env: Record<string, { re: number; im: number }> }[] = [];

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
if (inShard("core")) {
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
if (inShard("core")) {
  const at = exactReport(compileExpression("atan(1/0)", {}));
  if (at.value.im.isFinite() || at.singular === null) {
    failed += 1;
    console.log("FAIL atan(inf) circuit", formatExact(at.value), at.singular);
  }
}
if (recognize(c(1e-9)) === "0" || recognize(c(0.999999996973)) === "1") {
  failed += 1;
  console.log("FAIL recognize", recognize(c(1e-9)), recognize(c(0.999999996973)));
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
if (inShard("core")) {
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

if (inShard("core")) {
  const pole = evaluate(compileExpression("tan(pi/2)", {}));
  if (Number.isFinite(pole.re) && Math.abs(pole.re) < 1e6) {
    failed += 1;
    console.log("FAIL tan(pi/2) stayed small", pole);
  }
}
check("arcsin(2)", evaluate(compileExpression("arcsin(2)", {})), c(Math.PI / 2, -1.3169578969248166), 1e-6);
check("arccos(2)", evaluate(compileExpression("arccos(2)", {})), c(0, 1.3169578969248166), 1e-6);
if (inShard("core")) {
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
checkRecord("-ipi-strict", 55, 0, storedPi.neg(), false);
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
if (inShard("core")) {
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
if (inShard("core")) {
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
if (inShard("core")) {
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
const searched = searchConstants(21).hits;
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
const k33At40 = exactValueAt(k33Node, 40);
// v1.1 (Ben): the real part is either not resolved (0) or the stable residue 5.72402265941754e−116
// (mpmath, 400 digits); the imaginary part is −π. Either way the word is not −iπ.
const k33Residue = exactParts("5.72402265941754e-116").re;
const k33ReOk = k33At40.re.isZero() || k33At40.re.sub(k33Residue).abs().lte(k33Residue.mul("1e-9"));
const k33ImOk = k33At40.im.sub(exactParts(-Math.PI).re).abs().lte("1e-12");
if (!k33ReOk || !k33ImOk) {
  failed += 1;
  console.log("FAIL K33 word value", k33At40.re.toString(), k33At40.im.toString());
}
if (acceptsConstantProgram(k33Node, 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL K33 word accepted as −iπ");
}
if (acceptsConstantProgram(k35Node, 0, -Math.PI)) {
  failed += 1;
  console.log("FAIL K35 −iπ impostor was accepted");
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
if (inShard("core")) {
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
if (inShard("core")) {
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
if (inShard("core")) {
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
if (inShard("core")) {
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
if (inShard("core")) {
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
if (inShard("core")) {
  // Float64 cannot recover a real 2 beside an imaginary 10^16 through exp and ln:
  // one ulp of the angle is already larger than 2. Exact mode still has both.
  const scaledImag = evaluate(compileExpression("2-1e16*i", {}));
  if (!Number.isFinite(scaledImag.im) || Math.abs(scaledImag.im + 1e16) / 1e16 > 1e-6) {
    failed += 1;
    console.log("FAIL 2-1e16i float imaginary part", scaledImag);
  }
}
check("implicit i", evaluate(compileExpression("2-1e16i", {})), evaluate(compileExpression("2-1e16*i", {})), 0);
if (inShard("core")) {
  const inf = evaluate(compileExpression("inf", {}));
  if (inf.re !== Infinity || inf.im !== 0) {
    failed += 1;
    console.log("FAIL inf", inf);
  }
}
check("tan(1+800i) juxtaposition", evaluate(compileExpression("tan(1+800i)", {})), c(0, 1), 1e-6);
if (inShard("core")) {
  const exact = exactReport(compileExpression("2-1e16*i", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 2, "-1e16", 12)) {
    failed += 1;
    console.log("FAIL exact 2-1e16i", formatExact(exact.value));
  }
}
if (inShard("core")) {
  const exact = exactReport(compileExpression("10000000000000001-10000000000000000", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 20)) {
    failed += 1;
    console.log("FAIL exact big integer sub", formatExact(exact.value));
  }
}
check("big integer sub is not the zero program", evaluate(compileExpression("10000000000000001-10000000000000000", {})), c(1), 0);
if (inShard("core")) {
  const exact = exactReport(compileExpression("(2^53+1)-2^53", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 12)) {
    failed += 1;
    console.log("FAIL exact 2^53", formatExact(exact.value));
  }
}
if (inShard("core")) {
  const exact = exactReport(compileExpression("(1e16+1)-1e16", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, 1, 0, 12)) {
    failed += 1;
    console.log("FAIL exact 1e16+1-1e16", formatExact(exact.value));
  }
}
if (inShard("core")) {
  const exact = exactReport(compileExpression("(1+1e-20)-1", {}), {}, { maxNodes: 200_000 });
  if (!exactClose(exact.value, "1e-20", 0, 12)) {
    failed += 1;
    console.log("FAIL exact (1+1e-20)-1", formatExact(exact.value));
  }
}
if (inShard("core")) {
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
if (inShard("core")) {
  const exact = exactReport(compileExpression("(1e17+pi)-1e17", {}), {}, { maxNodes: 400_000 });
  if (!exactClose(exact.value, Math.PI, 0, 10)) {
    failed += 1;
    console.log("FAIL exact (1e17+pi)-1e17", formatExact(exact.value));
  }
}
if (inShard("core")) {
  const variable = tSub(literalNode("1"), V("x"));
  const exact = exactReport(variable, { x: c(1e20) }, { maxNodes: 400_000 });
  if (exact.value.re.plus("99999999999999999999").abs().gt("1e-6")) {
    failed += 1;
    console.log("FAIL variable 1-1e20", exact.value.re.toString());
  }
}
if (inShard("core")) {
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
if (inShard("core")) {
  const asinh = evaluate(tArsinh(V("x")), { x: c(1000) });
  if (!close(asinh, c(Math.asinh(1000)), 1e-9)) {
    failed += 1;
    console.log("FAIL variable asinh(1000)", asinh);
  }
}
if (inShard("core")) {
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
if (inShard("core")) {
  const summed = compileExpression(twentyK, {});
  const sum = evaluateReport(summed, {}, { maxNodes: 2_000_000 });
  if (!close(sum.value, c(20000), 1e-12) || sum.value.im !== 0) {
    failed += 1;
    console.log("FAIL 20000 ones", sum.value, sum.singular, rangeOf(summed).int?.toString(), provenInteger(summed)?.toString(), summed.type);
  }
}

if (inShard("core")) {
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
if (inShard("core")) {
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

if (inShard("core")) {
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

if (inShard("core")) {
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

if (inShard("core")) {
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

if (inShard("core")) {
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

if (inShard("core")) {
  const circuit = evaluate(compileExpression("1/(-0)", {}));
  const ref = referenceExpression("1/(-0)", {});
  if (circuit.re !== -Infinity || ref?.re !== -Infinity || circuit.im !== 0 || ref?.im !== 0) {
    failed += 1;
    console.log("FAIL 1/(-0) agreement", circuit, ref);
  }
}

if (inShard("core")) {
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
  const gap = compileExpression("inf-inf", {});
  const gapReport = evaluateReport(gap);
  const gapExact = exactReport(gap, {}, { maxNodes: 20_000 });
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

if (inShard("core")) {
  const wide = exactEvaluate(compileExpression("1e40+i", {}));
  if (wide.re.toExponential(2) !== "1.00e+40" || wide.im.minus(1).abs().gt("1e-6")) {
    failed += 1;
    console.log("FAIL exact 1e40+i drops the imaginary part", wide.re.toString(), wide.im.toString());
  }
}

if (inShard("core")) {
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

if (inShard("isolate")) {
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
  for (let i = 0; i < 20; i += 1) {
    const source = nest(2);
    try {
      const node = compileExpression(source, {});
      isolateCases.push({ source, env: {} });
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

if (inShard("core")) {
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
  // v1.1 (Ben): float scientific is 12 significant digits. bigfixer hotfix-2: tan(π/2) is the symbolic
  // pole, built as circuit/0, so float shows ∞ (with "near a pole"), not 2^52.
  if (noisy.includes("2.000000") || !noisy.startsWith("2 − ") || tangent !== "∞") {
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

if (inShard("isolate")) {
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
    try {
      const node = compileExpression(source, { x: V("x"), y: V("y") });
      isolateCases.push({ source, env });
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

if (inShard("isolate")) {
  const samples = [
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
  for (const source of samples) {
    const node = compileExpression(source, {});
    isolateCases.push({ source, env: {} });
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

if (inShard("isolate")) {
  let seed = 11;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const span = [0, 1e-12, 1e-3, 0.5, 2, 80, 1e6, -1e5, 1e-300, 1e-15, 1e-9, 1e-5, 1e200, 1e300, -1e200];
  for (const x of span) {
    for (const source of ["x-y", "asinh(x)"]) {
      const env = { x: c(x), y: c(x === 0 ? 800 : -x) };
      const node = compileExpression(source, { x: V("x"), y: V("y") });
      isolateCases.push({ source, env });
      const copy = freshCircuit(node);
      if (!samePoint(evaluate(node, env), evaluate(copy, env))) {
        failed += 1;
        console.log("FAIL wide fresh", source, x);
      }
    }
  }
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
  for (let i = 0; i < 30; i += 1) {
    const source = nest(3);
    try {
      const node = compileExpression(source, {});
      isolateCases.push({ source, env: {} });
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

if (inShard("core")) {
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

if (inShard("isolate")) {
  const repoRoot = path.resolve(__dirname, "../..");
  const payload = isolateCases.map((item, id) => {
    const node = compileExpression(item.source, { x: V("x"), y: V("y") });
    const env: Record<string, { re: PackedNum; im: PackedNum }> = {};
    for (const [name, value] of Object.entries(item.env)) env[name] = { re: packNum(value.re), im: packNum(value.im) };
    return { id, source: item.source, tokens: dagTokens(node), env, live: item.env };
  });
  // v1.1: portable spawn (the .bin shim is tsx.cmd on Windows).
  const child = spawnSync(process.execPath, [path.join(repoRoot, "node_modules/tsx/dist/cli.mjs"), path.join(repoRoot, "scripts/eml-rebuild.ts")], {
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

if (inShard("props")) failed += runPropertyChecks();

// Inverse-function regressions. Reference values are mpmath 1.3.0 at 30 digits.
// arcsin: principal value, counter-clockwise continuity on the real cut (as mpmath):
// arcsin(x > 1) = π/2 − i·arcosh(x), arcsin(x < −1) = −π/2 + i·arcosh(−x).
if (inShard("props")) {
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

if (inShard("props")) {
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

if (inShard("core")) {
  // The screen's worker path: parse, pack, unpack, then the exact engine.
  // Equivalent spellings, series corrections, dust, and the 480-digit cap.
  const workerReport = (source: string) => {
    const node = compileExpression(source, {});
    const packed = packCircuit(node);
    return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
  };
  const closeTo = (source: string, re: string, im = "0") => {
    const report = workerReport(source);
    const wantRe = exactParts(re).re;
    const wantIm = exactParts(im).re;
    const badRe = wantRe.isZero() ? !report.value.re.isZero() : report.value.re.sub(wantRe).abs().div(wantRe.abs()).gt("1e-9");
    const badIm = wantIm.isZero() ? !report.value.im.isZero() : report.value.im.sub(wantIm).abs().div(wantIm.abs()).gt("1e-9");
    if (report.unverified || badRe || badIm) {
      failed += 1;
      console.log("FAIL worker value", source, report.unverified ? "unverified" : formatExact(report.value));
    }
  };
  const unresolved = (source: string) => {
    const report = workerReport(source);
    if (!report.unverified) {
      failed += 1;
      console.log("FAIL certified", source, formatExact(report.value));
    }
  };
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
  closeTo("tanh(1e-45)-1e-45", "-3.333333333333e-136");
  closeTo("tanh(10^(-45))-10^(-45)", "-3.333333333333e-136");
  closeTo("tanh(3*10^(-45))-3*10^(-45)", "-9e-135");
  closeTo("arctan(1e-45)-1e-45", "-3.333333333333e-136");
  closeTo("arctan(10^(-45))-10^(-45)", "-3.333333333333e-136");
  closeTo("arctan(3*10^(-45))-3*10^(-45)", "-9e-135");
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
  // From p = 112 the negative imaginary part falls off 120 digits and the composed
  // log would certify +π. The value is ln 2 − iπ, or the result stays unverified.
  const lnBelow = (source: string) => {
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
  };
  lnBelow("ln(-2-10^(-110)*i)");
  lnBelow("ln(-2-10^(-112)*i)");
  lnBelow("ln(-2-10^(-115)*i)");
  lnBelow("ln(-2-10^(-130)*i)");
  // Scaled tiny adds stay on the raw add word only while the lifted imaginary parts
  // and their sum sit in (−π, π]. These are the cases that leave that strip.
  const bothModes = (source: string, re: string, im: string) => {
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
  };
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
  closeTo("(exp(1e-50)-1)-1e-50", "5e-101");
  closeTo("ln(1+1e-50)-1e-50", "-5e-101");
  closeTo("(sqrt(1+1e-50)-1)-5e-51", "-1.25e-101");
  closeTo("1e-120*(2+i)", "2e-120", "1e-120");
  closeTo("3*((1e-120*i)-(2e-120))", "-6e-120", "3e-120");
  closeTo("2*(1e-18+1e-125*i)", "2e-18", "2e-125");
  closeTo("exp(1e-432)-1", "1e-432");
  closeTo("tan(1e-5000)", "1e-5000");
  closeTo("exp(1e-1000)-1", "1e-1000");
  // v1.1: 10^(−k) now carries its exponent like 1e−k, so these two resolve.
  closeTo("tan(10^(-5000))", "1e-5000");
  closeTo("exp(10^(-1000))-1", "1e-1000");
  // v1.1: exp(x) − 1 has a two-term series for |x| ≤ 10^(−241), so 10^(−433) resolves.
  closeTo("exp(1e-433)-1", "1e-433");
  closeTo("exp(10^(-433))-1", "1e-433");
  closeTo("1-exp(1e-433)", "-1e-433");
  for (const source of ["sin(1e-300)-1e-300"]) unresolved(source);
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
  // v1.1 (reviewbot E3): no "matches the usual value" / "· 0" for a 0 the float lost or exact cancelled.
  {
    const e3: Array<[string, unknown, unknown]> = [];
    const lostRef = agreementNote("ln(1+1e-130)", { re: 0, im: 0 }, {}, "0");
    e3.push(["ln(1+1e-130) shown 0: no float agreement (reference lost the term)", lostRef, null]);
    e3.push(["lost-term detector: 1+1e-130", referenceLostTerm("ln(1+1e-130)", {}), true]);
    e3.push(["lost-term detector: 1e-130-1", referenceLostTerm("1e-130-1", {}), true]);
    e3.push(["lost-term detector: exp(-800)", referenceLostTerm("exp(-800)", {}), true]);
    e3.push(["lost-term detector: 1e-200*1e-200", referenceLostTerm("1e-200*1e-200", {}), true]);
    e3.push(["lost-term detector: 1-1 is exact", referenceLostTerm("1-1", {}), false]);
    e3.push(["lost-term detector: sin(1)+2", referenceLostTerm("sin(1)+2", {}), false]);
    e3.push(["1-1 still matches", agreementNote("1-1", { re: 0, im: 0 }, {}, "0"), "matches the usual value"]);
    e3.push(["cancelled 0 that matches: withheld", agreementNote("1-1", { re: 0, im: 0 }, {}, "0", { cancelledZero: true }), null]);
    e3.push(["not-certified 0: withheld", agreementNote("1-1", { re: 0, im: 0 }, {}, "0", { notCertified: true }), null]);
    const sinPi = agreementNote("sin(pi)", { re: 0, im: 0 }, {}, "0", { cancelledZero: true });
    e3.push(["sin(pi) cancelled 0 keeps the usual-value line", typeof sinPi === "string" && sinPi.startsWith("usual value"), true]);
    const base = { text: "0", unverified: false, notCertified: false, cancelledZero: false, differs: true };
    e3.push(["compare: plain differs", JSON.stringify(compareVerdict({ ...base, text: "1×10^−130" })), JSON.stringify({ beside: "1×10^−130" })]);
    e3.push(["compare: cancelled 0 is not a reference", compareVerdict({ ...base, cancelledZero: true }), null]);
    e3.push(["compare: not-certified 0 → couldn't verify", JSON.stringify(compareVerdict({ ...base, notCertified: true })), JSON.stringify({ notice: "couldn't verify" })]);
    e3.push(["compare: not-certified nonzero is labelled", JSON.stringify(compareVerdict({ ...base, text: "1", notCertified: true })), JSON.stringify({ beside: "1 (≈ not certified)" })]);
    e3.push(["compare: unverified", JSON.stringify(compareVerdict({ ...base, unverified: true, differs: false })), JSON.stringify({ notice: "couldn't verify" })]);
    e3.push(["compare: agrees", compareVerdict({ ...base, differs: false }), null]);
    e3.push(["fill: not certified notice", fillNotice({ notCertified: true }), "≈ not certified"]);
    e3.push(["fill: certified", fillNotice({ notCertified: false }), null]);
    e3.push(["· 0 withheld for a cancelled 0", withholdZeroName({ text: "0", cancelledZero: true, notCertified: false }), true]);
    e3.push(["· 0 kept for 1-1", withholdZeroName({ text: "0", cancelledZero: false, notCertified: false }), false]);
    const czOf = (src: string) => exactReport(compileExpression(src, {}), {}, { maxNodes: 80_000 }).cancelledZero === true;
    e3.push(["engine: ln(e)-1 is a cancelled 0", czOf("ln(e)-1"), true]);
    e3.push(["engine: 1-1 is a structural 0", czOf("1-1"), false]);
    e3.push(["engine: 2*ln(2)-ln(4) is a cancelled 0", czOf("2*ln(2)-ln(4)"), true]);
    // v1.1 (reviewbot E5): the half-sum a + (−a) at 1e−120 is the exact 0 a − a is, quickly.
    for (const src of ["avg(1e-120,-1e-120)", "1e-120+(-1e-120)", "avg(-1e-130,1e-130)", "avg(1e-20,-1e-20)", "half(1e-120+(-1e-120))"]) {
      const t5 = performance.now();
      const r5 = exactReport(compileExpression(src, {}), {}, { maxNodes: 80_000 });
      const ms = performance.now() - t5;
      e3.push([`E5 ${src} exact 0`, formatExact(r5.value) === "0" && r5.unverified !== true, true]);
      e3.push([`E5 ${src} under 2 s`, ms < 2000, true]);
    }
    {
      const r5 = exactReport(compileExpression("avg(1e-120,-2e-120)", {}), {}, { maxNodes: 80_000 });
      e3.push(["E5 avg(1e-120,-2e-120) is not folded", formatExact(r5.value), "−5×10^−121"]);
      const s5 = exactReport(compileExpression("-sin(1e-200)+sin(1e-200)", {}), {}, { maxNodes: 80_000 });
      e3.push(["E5 series-shortcut negation is not certified", s5.unverified === true, true]);
    }
    // v1.1 (reviewbot E6): progress per pass, and a deadline that no catch turns into a value.
    {
      const seen: number[] = [];
      exactReport(compileExpression("ln(1+10^(-130))", {}), {}, { maxNodes: 80_000, onProgress: ({ digits }) => seen.push(digits) });
      e3.push(["E6 progress starts at 120 digits", seen[0], 120]);
      e3.push(["E6 progress reports the raised pass", seen.some((d) => d > 120), true]);
      const t6 = performance.now();
      let timedOut = "";
      try {
        exactReport(compileExpression("avg(1e-120*i,-1e-120*i)", {}), {}, { maxNodes: 80_000, deadline: performance.now() + 50 });
      } catch (err) {
        timedOut = err instanceof Error ? err.message : String(err);
      }
      e3.push(["E6 deadline ends the job", timedOut, "Exact evaluation timed out."]);
      e3.push(["E6 deadline is cooperative (< 5 s)", performance.now() - t6 < 5000, true]);
      e3.push(["E6 progress note", exactProgressNote(240, 3400), "computing · 240 digits · 3 s"]);
      e3.push(["E6 progress note, first pass", exactProgressNote(120, 100), "computing · 120 digits"]);
    }
    // ln 0 folds (breakerbot hotfix-verify): in this process, compiled, float and exact, twice
    // (the second is a repeat compute). The fresh-process and word forms are in the overnight block.
    for (const src of ["ln(0)-ln(0)", "(1/0)-(1/0)", "ln(0)/ln(0)", "ln(0)+(-ln(0))", "-ln(0)+ln(0)", "ln(0)*0", "(ln(0)-1)-(ln(0)-1)"]) {
      const node = compileExpression(src, {});
      for (const pass of ["first", "repeat"]) {
        const f = evaluateReport(node, {}, { maxNodes: 200_000 });
        const x = exactReport(node, {}, { maxNodes: 80_000 });
        e3.push([`ln0 ${src} float ${pass}`, !Number.isFinite(f.value.re) || !Number.isFinite(f.value.im) ? f.singular !== null : false, true]);
        e3.push([`ln0 ${src} exact ${pass}`, formatExact(x.value) === "undefined" && x.singular !== null, true]);
      }
    }
    e3.push(["ln0 exp(ln(0))-exp(ln(0)) is still 0", formatExact(exactReport(compileExpression("exp(ln(0))-exp(ln(0))", {}), {}, { maxNodes: 80_000 }).value), "0"]);
    // v1.1 (reviewbot pre-review B1/B2; names shared with bigfixer's hotfix-2): maybeInfinite
    // sources are 0/0 and any division by a possible 0, tan at a symbolic pole, and ln 0. The
    // a − a and a + (−a) folds refuse a marked node: undefined with the flag in both modes.
    for (const src of ["(0/0)-(0/0)", "tan(pi/2)-tan(pi/2)", "tan(3*pi/2)-tan(3*pi/2)", "tan(pi/2+pi)-tan(pi/2+pi)", "tan(-pi/2)-tan(-pi/2)", "ln(ln(0))-ln(ln(0))", "tan(pi/2)+(-tan(pi/2))", "(0/0)+(-(0/0))", "ln(1-1)-ln(1-1)", "(ln(0)*0)-(ln(0)*0)", "(ln(0)-ln(0))+1"]) {
      const node = compileExpression(src, {});
      for (const pass of ["first", "repeat"]) {
        const f = evaluateReport(node, {}, { maxNodes: 200_000 });
        const x = exactReport(node, {}, { maxNodes: 80_000 });
        e3.push([`maybeInfinite ${src} float ${pass}`, !Number.isFinite(f.value.re) || !Number.isFinite(f.value.im) ? f.singular !== null : false, true]);
        e3.push([`maybeInfinite ${src} exact ${pass}`, formatExact(x.value) === "undefined" && x.singular !== null, true]);
      }
    }
    // Controls: no knownValue or range test, so these stay the instant 0 (the zero leaf).
    for (const src of ["sin(1)-sin(1)", "tan(1)-tan(1)", "tan(1.5707963267948966)-tan(1.5707963267948966)", "exp(ln(0))-exp(ln(0))", "tan(pi)-tan(pi)", "tan(pi/4)-tan(pi/4)"]) {
      const t0 = performance.now();
      const node = compileExpression(src, {});
      const x = exactReport(node, {}, { maxNodes: 80_000 });
      const ms = performance.now() - t0;
      e3.push([`maybeInfinite control ${src} exact 0`, formatExact(x.value) === "0" && !x.unverified && x.singular === null, true]);
      e3.push([`maybeInfinite control ${src} fast path (K ≤ 3, < 250 ms)`, circuitStats(node).dagGates <= 3 && ms < 250, true]);
    }
    {
      const lone = exactReport(compileExpression("tan(1.5707963267948966)", {}), {}, { maxNodes: 200_000 });
      e3.push(["maybeInfinite tan(1.5707963267948966) stays finite", formatExact(lone.value) !== "undefined", true]);
    }
    // Huge integers (reviewbot B3): the floatOverflowInt arms keep both terms in exact mode.
    for (const [src, want] of [["(10^400-1)-10^400", "−1"], ["(10^400+1)-10^400", "1"], ["(1+10^400)-10^400", "1"], ["10^400-(10^400-1)", "1"], ["(10^400-10^300)-10^400", "−1×10^300"], ["(10^400+10^300)-10^400", "1×10^300"], ["(10^400-10^300)/10^300", "9".repeat(100)]] as const) {
      const node = compileExpression(src, {});
      const x = exactReport(node, {}, { maxNodes: 80_000 });
      e3.push([`huge ${src}`, x.unverified ? "unverified" : formatExact(x.value).replace(/\u200b/g, ""), want]);
    }
    // v1.1 (Jimmy1 03:11): odd series for a tiny real, exact mode reads the polynomial from x.
    // 1/10^130 now carries its decade (tDiv), so arctan, tanh, tan, sin and arcsin take the series.
    // mpmath dps 600: f(x) − x at x = 10^(−130) is −x³/3 (arctan, tanh), +x³/3 (tan), ∓x³/6 (sin, arcsin).
    for (const [src, want] of [
      ["arctan(1/10^130)", "1×10^−130"], ["tanh(1/10^130)", "1×10^−130"], ["arcsin(1/10^130)", "1×10^−130"],
      ["tan(1/10^130)", "1×10^−130"], ["sin(1/10^130)", "1×10^−130"], ["arcsin(-1/10^130)", "−1×10^−130"],
      ["arctan(1/10^130)-1/10^130", "−3.33333333333×10^−391"], ["tanh(1/10^130)-1/10^130", "−3.33333333333×10^−391"],
      ["tan(1/10^130)-1/10^130", "3.33333333333×10^−391"], ["sin(1/10^130)-1/10^130", "−1.66666666667×10^−391"],
      ["arcsin(1/10^130)-1/10^130", "1.66666666667×10^−391"], ["arctan(-1/10^130)-(-1/10^130)", "3.33333333333×10^−391"],
      ["arctan(10^(-130))-10^(-130)", "−3.33333333333×10^−391"], ["arcsin(1/10^30)-1/10^30", "1.66666666667×10^−91"],
      ["arsinh(1/10^130)", "1×10^−130"], ["arsinh(10^(-130))", "1×10^−130"], ["arsinh(1/10^130)-1/10^130", "−1.66666666667×10^−391"],
    ] as const) {
      const x = exactReport(compileExpression(src, {}), {}, { maxNodes: 80_000 });
      e3.push([`tiny series ${src}`, x.unverified ? "unverified" : formatExact(x.value).replace(/\u200b/g, ""), want]);
      e3.push([`tiny series ${src} certified`, x.singular === null && !x.notCertified, true]);
    }
    for (const src of ["arctan(1/10^130)", "tanh(1/10^130)", "arcsin(1/10^130)"]) {
      const t0 = performance.now();
      const x = exactReport(compileExpression(src, {}), {}, { maxNodes: 80_000 });
      const ms = performance.now() - t0;
      e3.push([`tiny series ${src} under 500 ms (${ms.toFixed(0)} ms)`, ms < 500 && formatExact(x.value) === "1×10^−130", true]);
    }
    // A zero from the leading-term shortcut alone still cannot be verified.
    e3.push(["tiny series arctan(10^(-250))-10^(-250) unverified", exactReport(compileExpression("arctan(10^(-250))-10^(-250)", {}), {}, { maxNodes: 80_000 }).unverified === true, true]);
    // v1.1 (bigfixer's #11 review C): the mark goes through exp (unless Re → −∞ only), pow,
    // sqr, sqrt, sinh, cosh and a marked denominator. Each of these minus itself is ∞ − ∞.
    for (const src of ["exp(-ln(0))-exp(-ln(0))", "0^(-1)-0^(-1)", "pow(0,-1)-pow(0,-1)", "sqrt(ln(0))-sqrt(ln(0))", "ln(0)^2-ln(0)^2", "1/(0/0)-1/(0/0)", "sqrt(0/0)-sqrt(0/0)", "exp(0/0)-exp(0/0)", "sinh(ln(0))-sinh(ln(0))", "cosh(1/0)-cosh(1/0)", "(1/0)^2-(1/0)^2", "ln(0)*0", "exp(0*ln(0))"]) {
      const node = compileExpression(src, {});
      const f = evaluateReport(node, {}, { maxNodes: 200_000 });
      const x = exactReport(node, {}, { maxNodes: 80_000 });
      e3.push([`review C ${src} float`, !Number.isFinite(f.value.re) || !Number.isFinite(f.value.im) ? f.singular !== null : false, true]);
      e3.push([`review C ${src} exact`, formatExact(x.value) === "undefined" && x.singular !== null, true]);
    }
    // Values (exact mode): review C sign fixes, review A (huge + non-integer), review B2 (one node per huge value).
    for (const [src, want] of [["ln(0)*1", "−∞"], ["ln(0)^1", "−∞"], ["sqrt(ln(0))", "∞i"], ["1/ln(0)-1/ln(0)", "0"], ["exp(2*ln(0))-exp(2*ln(0))", "0"], ["exp(ln(0)-1)-exp(ln(0)-1)", "0"], ["(10^400+i)-10^400", "i"], ["(10^400+pi)-10^400", "3.14159265359"], ["(10^400+sqrt(2))-10^400", "1.41421356237"], ["(10^400+0.5)-10^400", "0.5"], ["(10^400-i)-10^400", "−i"], ["10^400-(10^400-pi)", "3.14159265359"], ["(10^400+3)-(10^400+1)", "2"], ["((10^400+3)+(10^400+1))-2*10^400", "4"], ["(10^400+1)-(10^400+2)", "−1"], ["(10^401+1)-(10^400+1)", "9×10^400"], ["(10^400+10^300)-(10^400-10^300)", "2×10^300"]] as const) {
      const x = exactReport(compileExpression(src, {}), {}, { maxNodes: 80_000 });
      e3.push([`review ${src}`, x.unverified ? "unverified" : formatExact(x.value).replace(/\u200b/g, ""), want]);
    }
    {
      const big = evaluateReport(compileExpression("10^400-1", {}), {}, { maxNodes: 200_000 });
      e3.push(["huge 10^400-1 float stays +∞", big.value.re === Infinity && big.singular !== null, true]);
    }
    for (const [name, got, want] of e3) {
      if (got !== want) {
        failed += 1;
        console.log("FAIL E3", name, got, "want", want);
      }
    }
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
  if (
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

if (inShard("core")) {
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
  // v1.1: portable (URL pathname is /C:/… on Windows, and npx is npx.cmd there).
  const rootDir = path.resolve(__dirname, "../..");
  const fresh = spawnSync(process.execPath, [path.join(rootDir, "node_modules/tsx/dist/cli.mjs"), "scripts/fresh-exact.ts"], {
    cwd: rootDir,
    input: JSON.stringify(jobs),
    encoding: "utf8",
    timeout: 180_000,
  });
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

if (inShard("core")) {
  // E1 (v1.1): a word of 1 and E has no build-time tags. Load the v1.0 words in a FRESH
  // process (cold: nothing compiled, empty range table) and in this one after compiling
  // (warm: hash-consed nodes keep their tags). Never a certified 0, and cold == warm.
  const root = path.resolve(__dirname, "../..");
  const cold = spawnSync(process.execPath, [path.join(root, "node_modules/tsx/dist/cli.mjs"), path.join(root, "scripts/e1-cold.ts"), path.join(root, "scripts/e1-words-v10.json")], {
    cwd: root,
    encoding: "utf8",
    timeout: 300_000,
    maxBuffer: 64 * 1024 * 1024,
  });
  const want: Record<string, string> = {
    "ln(1+10^(-100))": "1×10^−100",
    "ln(1+10^(-130))": "1×10^−130",
    "log(1+10^(-130))": "1×10^−130",
    "ln(1+10^(-200))": "1×10^−200",
    "ln(1+10^(-300))": "1×10^−300",
    "ln(1+3*10^(-300))": "3×10^−300",
    "ln(1+1e-130)": "1×10^−130",
  };
  let rows: Record<string, string> = {};
  try {
    rows = JSON.parse(cold.stdout.trim().split("\n").pop() ?? "{}");
  } catch {
    rows = {};
  }
  const words = JSON.parse(readFileSync(path.join(root, "scripts/e1-words-v10.json"), "utf8")) as Record<string, string>;
  if (words["ln(1+10^(-130))"]?.length !== 671) {
    failed += 1;
    console.log("FAIL E1 fixture: the ln(1+10^(-130)) word is not 671 presses");
  }
  for (const [source, text] of Object.entries(want)) {
    const got = rows[source];
    if (got !== text && !(got ?? "").startsWith("unverified")) {
      failed += 1;
      console.log("FAIL E1 cold word", source, got ?? cold.stderr.slice(0, 300));
    }
    compileExpression(source, {});
    const warm = formatExact(exactReport(nodeFromRpn(words[source].split("")), {}, { maxNodes: 200_000 }).value);
    if (got !== undefined && warm !== got.replace(" [not certified]", "")) {
      failed += 1;
      console.log("FAIL E1 warm differs from cold", source, warm, got);
    }
  }
}

// v1.1: breakerbot's overnight findings 1–5, 7, 8 (overnight-bugs.md). The page compiles and
// posts the wire; the exact worker never compiled anything. scripts/overnight-child.ts is that
// worker: each case is evaluated cold, then again on the warm pureCache (a repeat compute).
// Values are mpmath (dps 400 and 800). Finding 6 (a−b−b) is bigfixer's and is not here.
if (inShard("core")) {
  const root = path.resolve(__dirname, "../..");
  type Case = { finding: number; src: string; want: [string, string]; exactText?: string; word?: string; src2?: string; env?: Record<string, [number, number]>; digits?: boolean; flags?: boolean; undef?: boolean };
  const cases = JSON.parse(readFileSync(path.join(root, "scripts/overnight-cases.json"), "utf8")) as Case[];
  const items = cases.map((item) => {
    const env: Record<string, { re: number; im: number }> = {};
    for (const [name, [re, im]] of Object.entries(item.env ?? {})) env[name] = { re, im };
    const node = item.word ? nodeFromRpn(item.word.split("")) : compileExpression(item.src2 ?? item.src, Object.fromEntries(Object.keys(env).map((name) => [name, V(name)])));
    const packed = packCircuit(node);
    return { tokens: packed.tokens, root: packed.root, env };
  });
  const jobFile = path.join(root, "scripts/.overnight-job.json");
  writeFileSync(jobFile, JSON.stringify({ items }));
  const child = spawnSync(process.execPath, [path.join(root, "node_modules/tsx/dist/cli.mjs"), path.join(root, "scripts/overnight-child.ts"), jobFile], { cwd: root, encoding: "utf8", maxBuffer: 1 << 26 });
  rmSync(jobFile, { force: true });
  if (child.status !== 0) {
    failed += 1;
    console.log("FAIL overnight child", child.status, child.stderr?.slice(0, 400));
  } else {
    const runs = JSON.parse(child.stdout) as Array<Array<{ text?: string; unverified?: boolean; singular?: string | null; error?: string; floatRe?: number | null; floatIm?: number | null; floatSingular?: string | null }>>;
    const parse = (text: string): [Decimal, Decimal] | null => {
      const t = text.replace(/−/g, "-").replace(/×10\^/g, "e").replace(/\s+/g, "");
      const num = "[0-9.]+(?:e[+-]?\\d+)?";
      const pureIm = new RegExp(`^([+-]?)(${num})?i$`).exec(t);
      if (pureIm) return [new DecimalValue(0), new DecimalValue(`${pureIm[1] === "-" ? "-" : ""}${pureIm[2] ?? "1"}`)];
      const m = new RegExp(`^([+-]?${num})(?:([+-])(${num})?i)?$`).exec(t);
      if (!m) return null;
      return [new DecimalValue(m[1]), m[2] ? new DecimalValue(`${m[2] === "-" ? "-" : ""}${m[3] ?? "1"}`) : new DecimalValue(0)];
    };
    const near = (got: Decimal, want: string) => {
      const w = new DecimalValue(want);
      if (w.isZero()) return got.isZero();
      return !got.isZero() && got.sub(w).abs().lte(w.abs().mul("1e-9"));
    };
    cases.forEach((item, index) => {
      ["cold", "repeat"].forEach((label, pass) => {
        const run = runs[index]?.[pass];
        const name = `overnight F${item.finding} ${label} ${item.src}`;
        if (!run || run.error || run.text === undefined) {
          failed += 1;
          console.log("FAIL", name, run?.error);
          return;
        }
        if (item.flags) {
          // Finding 5: the flag must survive a repeat compute.
          const want = item.src.startsWith("tan(") && item.src.includes("pi") ? "near a pole" : "argument too large to reduce";
          if (run.singular !== want) {
            failed += 1;
            console.log("FAIL", name, run.singular);
          }
          return;
        }
        // ln 0 folds (breakerbot hotfix-verify): −∞ − (−∞) and friends are undefined with a
        // flag in BOTH modes, never a certified 0. JSON turns NaN/±∞ into null.
        if (item.undef) {
          const floatFinite = typeof run.floatRe === "number" && typeof run.floatIm === "number";
          if (run.text !== "undefined" || !run.singular || floatFinite || !run.floatSingular) {
            failed += 1;
            console.log("FAIL", name, run.text, run.singular, "float", run.floatRe, run.floatIm, run.floatSingular);
          }
          return;
        }
        // Finding 11: (10^400 − 10^300)/10^300 is 10^100 − 1, so every digit is compared.
        if (item.exactText !== undefined) {
          const text = run.text.replace(/\u200b/g, "");
          if (run.unverified || text !== item.exactText) {
            failed += 1;
            console.log("FAIL", name, run.unverified ? "unverified" : text.slice(0, 40), "want", item.exactText.slice(0, 40));
          }
          return;
        }
        const got = run.unverified ? null : parse(run.text);
        const good = got !== null && near(got[0], item.want[0]) && near(got[1], item.want[1]);
        // Finding 3: no long noise tail, so at most 12 significant digits shown.
        const short = !item.digits || run.text.replace(/×10\^.*$/, "").replace(/[^0-9]/g, "").replace(/^0+/, "").length <= 12;
        if (!good || !short) {
          failed += 1;
          console.log("FAIL", name, run.unverified ? "unverified" : run.text, "want", item.want);
        }
      });
    });
  }
}

if (inShard("core")) {
  // bigfixer hotfix-2 (PR #11 head fa5f9af), ported verbatim.
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
  // v1.1: node + the tsx cli, as the other spawn checks here; "npx" without a shell and a
  // URL pathname ("/C:/…") both fail on Windows (Ben's PC).
  const wireRoot = path.resolve(__dirname, "../..");
  const wire = spawnSync(process.execPath, [path.join(wireRoot, "node_modules/tsx/dist/cli.mjs"), "scripts/fresh-exact.ts"], {
    cwd: wireRoot,
    input: JSON.stringify(wireJobs),
    encoding: "utf8",
    timeout: 180_000,
  });
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
}

if (failed) {
  console.log(`\n${failed} failed`);
  process.exit(1);
}
console.log(SHARD === "all" ? "all passed" : `all passed (shard ${SHARD})`);
