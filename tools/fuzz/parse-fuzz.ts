/**
 * Input robustness fuzzer: random and mangled text into the expression field, the
 * x/y fields and the program field, through the same calls the calculator makes
 * (compileSubmission + entry, parseProgramInput + unrankProgram / nodeFromRpn).
 *
 * Every input must either work or fail with the calculator's own error: an
 * EmlError from the expression path, an EmlError or RangeError from the program
 * path. Anything else (a TypeError, a stack overflow, a decimal.js or BigInt
 * error) reaches the screen as an internal message, and an input that takes more
 * than --slow-ms is reported too. Exits 1 on any finding.
 *
 * Usage:
 *   npx tsx tools/fuzz/parse-fuzz.ts [--count 3000] [--seed 1] [--slow-ms 4000]
 */
import { entry } from "../../components/calculator/entry";
import { compileSubmission } from "../../components/submitTurn";
import { EmlError, nodeFromRpn } from "../../lib/eml/node";
import { parseProgramInput, unrankProgram } from "../../lib/eml/programIndex";

function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function flags(argv: string[]) {
  let count = 3000;
  let seed = 1;
  let slowMs = 4000;
  for (let i = 0; i < argv.length; i += 1) {
    if (argv[i] === "--count") count = Number(argv[++i]);
    else if (argv[i] === "--seed") seed = Number(argv[++i]);
    else if (argv[i] === "--slow-ms") slowMs = Number(argv[++i]);
  }
  return { count, seed, slowMs };
}

const { count, seed, slowMs } = flags(process.argv.slice(2));
const rand = mulberry32(seed);
const pick = <T,>(xs: readonly T[]): T => xs[Math.floor(rand() * xs.length)] as T;
const chance = (p: number) => rand() < p;

const ATOMS = [
  "0", "1", "2", "3", "10", "0.5", ".5", "1.5", "1e-5", "1e300", "1e-400", "2.5e+3", "1e-5000",
  "pi", "π", "e", "i", "x", "y", "2i", "3pi", "2πi", "0.1", "123456789012345678901234567890",
];
const UNARY = [
  "exp", "ln", "log", "sqrt", "sq", "sqr", "inv", "half", "minus", "sigma", "sigmoid", "sin", "cos", "tan",
  "asin", "acos", "atan", "arcsin", "arccos", "arctan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh",
  "arsinh", "arcosh", "artanh",
];
const BINARY_CALL = ["hypot", "avg", "pow", "log"];
const OPS = ["+", "-", "*", "/", "^", "**", "−", "×", "÷"];

function expr(depth: number): string {
  if (depth <= 0 || chance(0.25)) return pick(ATOMS);
  const r = rand();
  if (r < 0.3) return `${expr(depth - 1)}${pick(OPS)}${expr(depth - 1)}`;
  if (r < 0.5) return `${pick(UNARY)}(${expr(depth - 1)})`;
  if (r < 0.6) return `${pick(BINARY_CALL)}(${expr(depth - 1)},${expr(depth - 1)})`;
  if (r < 0.7) return `(${expr(depth - 1)})`;
  if (r < 0.78) return `-${expr(depth - 1)}`;
  if (r < 0.84) return `√${expr(depth - 1)}`;
  if (r < 0.9) return `${pick(ATOMS)}${expr(depth - 1)}`; // implicit product
  return `${pick(UNARY)} ${expr(depth - 1)}`; // a call without parentheses
}

const NOISE = [
  "(", ")", ",", ".", "e", "E", "^", "√", "−", "×", "÷", "π", "​", " ", "#", "x", "y", "i", "0", "9",
  "+", "-", "*", "/", "**", "1e", "e-", "..", "()", ",,", "sin", "√√", "%", "$", "∞", "NaN", "\t", "ﬁ",
];

function mangle(text: string): string {
  let s = text;
  const edits = 1 + Math.floor(rand() * 3);
  for (let k = 0; k < edits; k += 1) {
    const at = Math.floor(rand() * (s.length + 1));
    const r = rand();
    if (r < 0.4) s = s.slice(0, at) + pick(NOISE) + s.slice(at);
    else if (r < 0.7) s = s.slice(0, at) + s.slice(at + 1 + Math.floor(rand() * 3));
    else s = s.slice(0, at) + s.slice(at, at + 4).repeat(2) + s.slice(at + 4);
  }
  return s;
}

/** Inputs that stress sizes and nesting rather than spelling. */
function extreme(): string {
  switch (Math.floor(rand() * 12)) {
    case 0:
      return `${"(".repeat(200 + Math.floor(rand() * 3000))}1${")".repeat(200 + Math.floor(rand() * 3000))}`;
    case 1:
      return "9".repeat(50 + Math.floor(rand() * 5000));
    case 2:
      return `1e${pick(["999999999", "-999999999", "99999999999999999999", "+0", "-0"])}`;
    case 3:
      return Array.from({ length: 2 + Math.floor(rand() * 6) }, () => pick(["2", "x", "10", "e", "i"])).join("^");
    case 4:
      return Array.from({ length: 50 + Math.floor(rand() * 400) }, () => pick(["1", "x", "2"])).join(pick(["+", "*", "-"]));
    case 5:
      return `${pick(UNARY)}(`.repeat(5 + Math.floor(rand() * 60)) + "x" + ")".repeat(5 + Math.floor(rand() * 60));
    case 6:
      return `-`.repeat(1 + Math.floor(rand() * 500)) + "1";
    case 7:
      return `√`.repeat(1 + Math.floor(rand() * 300)) + "2";
    case 8:
      return `0.${"0".repeat(Math.floor(rand() * 2000))}1`;
    case 9:
      return `${pick(["10", "2", "e"])}^(${pick(["-", ""])}${pick(["1e9", "400", "5000", "99999", "1e5000"])})`;
    case 10:
      return `log(${pick(ATOMS)},${pick(ATOMS)})`;
    default:
      return pick(["", " ", "()", "(,)", "sin()", "pow(1)", "hypot(1,2,3)", "1,2", "x y", "e e", "ee", "1e", "1..2", "#5"]);
  }
}

const FIELD = ["2", "-1", "0", "1+i", "-0", "1e-300", "1e300", "i", "pi", "x", "", "(", "2^1e9", "1/0", "ln(0)"];

const PROGRAM = [
  "#0", "#1", "#110", `#${"9".repeat(30)}`, `#${"9".repeat(400)}`, "#", "# 5", "#-5", "-3", "110", "1 1 E",
  "11E", "1E", "E", "x", "xyE", "11xE1EE", "0b110", "0b", "0x1f", "0x", "0xzz", "1".repeat(2000), "10".repeat(400),
  "11E".repeat(300), `0x${"f".repeat(200)}`, `0b${"1".repeat(3000)}`, "１１E", "11e", "1 1 e", "11E​",
];

type Finding = { kind: string; input: string; detail: string };
const findings: Finding[] = [];
/** Long inputs are shortened in the report; FUZZ_FULL=1 prints them whole. */
const short = (s: string) =>
  process.env.FUZZ_FULL || s.length <= 160 ? s : `${s.slice(0, 100)}…${s.slice(-50)} (${s.length} chars)`;

function timed(kind: string, input: string, run: () => void, expected: (err: unknown) => boolean): void {
  const t0 = performance.now();
  try {
    run();
  } catch (err) {
    if (!expected(err)) {
      const name = err instanceof Error ? err.constructor.name : typeof err;
      const message = err instanceof Error ? err.message : String(err);
      findings.push({ kind, input, detail: `${name}: ${message.slice(0, 200)}` });
    }
  }
  const ms = performance.now() - t0;
  if (ms > slowMs) findings.push({ kind: `${kind} slow`, input, detail: `${Math.round(ms)} ms` });
}

const expressionErrors = (err: unknown) => err instanceof EmlError;
const programErrors = (err: unknown) => err instanceof EmlError || err instanceof RangeError;

const t0 = performance.now();
for (let n = 0; n < count; n += 1) {
  const r = rand();
  let text: string;
  if (r < 0.45) text = expr(1 + Math.floor(rand() * 4));
  else if (r < 0.8) text = mangle(expr(1 + Math.floor(rand() * 4)));
  else text = extreme();
  const xText = chance(0.8) ? pick(FIELD) : mangle(pick(FIELD));
  const yText = chance(0.8) ? pick(FIELD) : mangle(pick(FIELD));
  timed("expression", `${text}   [x=${xText} y=${yText}]`, () => {
    const { node, numbers } = compileSubmission(text, xText, yText);
    entry(node, text, "float", numbers);
  }, expressionErrors);
  if (n % 6 === 0) {
    const source = chance(0.6) ? pick(PROGRAM) : mangle(pick(PROGRAM));
    timed("program", source, () => {
      const parsed = parseProgramInput(source);
      if (parsed.kind === "index") unrankProgram(parsed.index);
      else nodeFromRpn(parsed.word.split(""));
    }, programErrors);
  }
}

const elapsed = Math.round(performance.now() - t0);
const byDetail = new Map<string, Finding[]>();
for (const f of findings) {
  const key = `${f.kind} | ${f.detail.replace(/\d+/g, "N")}`;
  byDetail.set(key, [...(byDetail.get(key) ?? []), f]);
}
console.log(`parse fuzz seed=${seed} count=${count} (${elapsed} ms): ${findings.length} findings in ${byDetail.size} groups`);
for (const [key, group] of byDetail) {
  console.log(`- ${key} ×${group.length}`);
  for (const f of group.slice(0, 3)) console.log(`    ${short(f.input)}   → ${f.detail}`);
}
if (findings.length > 0) process.exit(1);
