import Decimal from "decimal.js";
import { circuitStats, nodeFromRpn, V } from "./node";
import { exactClose, exactReport } from "./exact";
import { applyProgram, SHORT_PROGRAMS } from "./programs";
import {
  compilePresses,
  IMUL_LIMIT,
  POW_MAX,
  POW_MIN,
  PressCompileError,
  REAL_LIMIT,
  recipeExtra,
  UNCERTIFIED_ADD,
  UNCERTIFIED_SUB,
} from "./exprSeq";

const D = Decimal.clone({ precision: 90 });

/**
 * The expression compiler, checked on the exact engine.
 * A short recipe is used only where this file's grid has seen a certified value.
 * The three additions in UNCERTIFIED_ADD, and sub(−4, −4), print an unverified 0
 * from the short word, so the compiler emits the library's certified 0 instead.
 */
export function runExprChecks(): number {
  let failed = 0;
  let printed = 0;
  const fail = (message: string) => {
    failed += 1;
    if (printed < 16) {
      printed += 1;
      console.log("FAIL expr", message);
    }
  };

  const recipes: Array<[string, number, number]> = [
    ["add", 19, 17],
    ["sub", 11, 9],
    ["mul", 17, 15],
    ["div", 17, 15],
    ["pow", 25, 23],
    ["minus", 15, 14],
  ];
  for (const [id, keys, extra] of recipes) {
    const word = SHORT_PROGRAMS[id];
    if (!word || word.length !== keys || recipeExtra(id) !== extra) {
      fail(`recipe ${id} length ${word?.length} extra ${word ? recipeExtra(id) : "missing"}`);
    }
  }

  const counts: string[] = [];

  const expect = (
    source: string,
    re: string,
    im: string,
    via: string,
    presses: number | null,
    unverified = false,
  ) => {
    let seq;
    try {
      seq = compilePresses(source);
    } catch (err) {
      fail(`${source} threw ${err instanceof Error ? err.message : err}`);
      return;
    }
    const length = circuitStats(seq.node).rpnLength;
    if (seq.presses !== seq.word.length || BigInt(seq.presses) !== length || !/^[1E]+$/.test(seq.word)) {
      fail(`${source} length ${seq.presses} word ${seq.word.length} circuit ${length}`);
    }
    if (presses !== null && seq.presses !== presses) fail(`${source} claimed ${presses} emitted ${seq.presses}`);
    if (!seq.via.includes(via)) fail(`${source} via ${seq.via.join(",")} missing ${via}`);
    const report = exactReport(seq.node, {}, { maxNodes: 2_000_000 });
    const close = report.singular === null && exactClose(report.value, re, im, 40);
    const flag = report.unverified === true;
    if (!close || flag !== unverified) {
      fail(`${source} value close=${close} unverified=${flag} singular=${report.singular ?? "none"}`);
    }
    counts.push(`${source} ${seq.presses}`);
  };

  const hi = (value: Decimal.Value) => new D(value).toFixed(70);
  expect("3+4", "7", "0", "add:short", 85);
  expect("2*5", "10", "0", "mul:short", 83);
  expect("7-2", "5", "0", "sub:short", 97);
  expect("7−2", "5", "0", "sub:short", 97);
  expect("2^3", "8", "0", "pow:short", 71);
  expect("2^3-1", "7", "0", "sub:short", 81);
  expect("1/2", "0.5", "0", "div:short", 35);
  expect("-3", "-3", "0", "lit:-3:count", 37);
  expect("−3", "-3", "0", "lit:-3:count", 37);
  expect("0", "0", "0", "lit:0:table", 7);
  expect("3-5", "-2", "0", "sub:short", 87);
  expect("2*(-3)", "-6", "0", "mul:short", 71);
  expect("2*(−3)", "-6", "0", "mul:short", 71);
  expect("(1+1)*(2+3)", "10", "0", "mul:short", 99);
  expect("(1+2)*(3+4)", "21", "0", "mul:short", 137);
  expect("2^(3-1)", "4", "0", "pow:short", 81);
  expect("-(1+2)", "-3", "0", "minus:short", 51);

  const uncertifiedAdd = (a: number, b: number) => UNCERTIFIED_ADD.some(([x, y]) => x === a && y === b);
  const uncertifiedSub = (a: number, b: number) => UNCERTIFIED_SUB.some(([x, y]) => x === a && y === b);

  for (let a = -REAL_LIMIT; a <= REAL_LIMIT; a += 1) {
    for (let b = -REAL_LIMIT; b <= REAL_LIMIT; b += 1) {
      if (uncertifiedAdd(a, b)) expect(`(${a})+(${b})`, "0", "0", "add:fallback", 7, false);
      else expect(`(${a})+(${b})`, hi(a + b), "0", "add:short", null, false);
      if (uncertifiedSub(a, b)) expect(`(${a})-(${b})`, "0", "0", "sub:fallback", 7, false);
      else expect(`(${a})-(${b})`, hi(a - b), "0", "sub:short", null, false);
      expect(`(${a})*(${b})`, hi(a * b), "0", "mul:short", null, false);
      if (b !== 0) expect(`(${a})/(${b})`, hi(new D(a).div(b)), "0", "div:short", null, false);
    }
    expect(`-(${a}+0)`, hi(-a), "0", "minus:short", null, false);
    for (let exp = POW_MIN; exp <= POW_MAX; exp += 1) {
      if (a === 0 && exp <= 0) continue;
      expect(`(${a})^(${exp})`, hi(new D(a).pow(exp)), "0", "pow:short", null, false);
    }
  }

  for (let n = -6; n <= 6; n += 1) {
    for (let k = -6; k <= 6; k += 1) {
      expect(`(${n})*(${k}*i)`, "0", hi(n * k), "mul:short", null, false);
      expect(`(${k}*i)*(${n})`, "0", hi(n * k), "mul:short", null, false);
    }
  }

  expect("5-4*i", "5", "-4", "sub:fallback", 501);
  expect("5+4*i", "5", "4", "add:fallback", 591);
  expect("-(4*i)", "0", "-4", "minus:fallback", 141);
  for (let n = -REAL_LIMIT; n <= REAL_LIMIT; n += 1) {
    for (let k = -IMUL_LIMIT; k <= IMUL_LIMIT; k += 1) {
      if (k === 0) continue;
      expect(`(${n})-(${k}*i)`, hi(n), hi(-k), "sub:fallback", null, false);
      expect(`(${n})+(${k}*i)`, hi(n), hi(k), "add:fallback", null, false);
    }
  }
  for (let k = -IMUL_LIMIT; k <= IMUL_LIMIT; k += 1) {
    if (k === 0) continue;
    expect(`-(${k}*i)`, "0", hi(-k), "minus:fallback", null, false);
  }

  const shortWrong = (id: string, x: { re: number; im: number }, y: { re: number; im: number } | null, re: string, im: string) => {
    const node = y ? applyProgram(id, { x: V("x"), y: V("y") }) : applyProgram(id, { x: V("x") });
    const env: Record<string, { re: number; im: number }> = { x };
    if (y) env.y = y;
    const report = exactReport(node, env, { maxNodes: 200_000 });
    if (report.singular === null && exactClose(report.value, re, im, 12)) {
      fail(`short ${id} matched ${re}+${im}i where it must not`);
    }
  };
  shortWrong("sub", { re: 5, im: 0 }, { re: 0, im: 4 }, "5", "-4");
  shortWrong("add", { re: 5, im: 0 }, { re: 0, im: 4 }, "5", "4");
  shortWrong("minus", { re: 0, im: 4 }, null, "0", "-4");

  const minusFour = compilePresses("-4").word;
  let bare = "";
  for (const ch of SHORT_PROGRAMS.sub ?? "") bare += ch === "x" || ch === "y" ? minusFour : ch;
  const bareReport = exactReport(nodeFromRpn(bare.split("")), {}, { maxNodes: 500_000 });
  if (bareReport.unverified !== true || !exactClose(bareReport.value, "0", "0", 20)) {
    fail("short sub of the −4 word should print an unverified 0");
  }
  const guarded = compilePresses("(-4)-(-4)");
  if (guarded.via.includes("sub:short") || !guarded.via.includes("sub:fallback")) {
    fail(`(−4)−(−4) stayed on the short word: ${guarded.via.join(",")}`);
  }

  for (const [a, b] of UNCERTIFIED_ADD) {
    const left = compilePresses(String(a)).word;
    const right = compilePresses(String(b)).word;
    let word = "";
    for (const ch of SHORT_PROGRAMS.add ?? "") word += ch === "x" ? left : ch === "y" ? right : ch;
    const shortReport = exactReport(nodeFromRpn(word.split("")), {}, { maxNodes: 500_000 });
    if (shortReport.unverified !== true || !exactClose(shortReport.value, "0", "0", 20)) {
      fail(`short add of ${a} and ${b} should print an unverified 0`);
    }
    const compiled = compilePresses(`(${a})+(${b})`);
    const compiledReport = exactReport(compiled.node, {}, { maxNodes: 200_000 });
    if (
      compiled.via.includes("add:short") ||
      !compiled.via.includes("add:fallback") ||
      compiled.presses !== 7 ||
      compiled.presses !== compiled.word.length ||
      compiledReport.unverified === true ||
      compiledReport.singular !== null ||
      !exactClose(compiledReport.value, "0", "0", 40)
    ) {
      fail(`(${a})+(${b}) did not take the certified 0: ${compiled.presses} ${compiled.via.join(",")}`);
    }
  }

  const rejects = (source: string, needle: string) => {
    try {
      compilePresses(source);
      fail(`${source || "empty"} compiled`);
    } catch (err) {
      if (!(err instanceof PressCompileError) || !err.message.toLowerCase().includes(needle.toLowerCase())) {
        fail(`${source || "empty"} error ${err instanceof Error ? err.message : err}`);
      }
    }
  };
  rejects("sin(1)", "not supported");
  rejects("", "enter an expression");
  rejects("1/0", "division by zero");
  rejects("0^0", "indeterminate");
  rejects("0^-1", "negative power");
  rejects("1.5", "decimal");
  rejects("9+1", "outside the verified domain");
  rejects("2^(1/2)", "integer exponent");

  console.log(failed === 0 ? `expr presses ${counts.filter((_, index) => index < 17).join(" ")}` : `expr failed ${failed}`);
  return failed;
}
