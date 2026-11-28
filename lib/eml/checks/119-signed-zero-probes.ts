import { readFileSync } from "node:fs";
import { exactReport, formatExact } from "../exact";
import { SINGULAR_LN0, V, evaluateReport, nodeFromRpn, type Node } from "../node";
import { compileExpression } from "../parse";
import { reportUnpacked } from "../packed-eval";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * The signed-zero probe set, on the app path and the worker wire.
 * A product, power, or reciprocal whose signs are all certified follows IEEE.
 * A wrapper of an unverified factor stays unverified. The two paths agree.
 */

const envs: Record<string, { x: { re: number; im: number }; y: { re: number; im: number } }> = {
  a: { x: { re: -2 / 3, im: 0 }, y: { re: 0, im: 0 } },
  b: { x: { re: -2, im: 0 }, y: { re: 0, im: 0 } },
  c: { x: { re: 0, im: 0 }, y: { re: -0.5, im: 0 } },
  d: { x: { re: -0, im: 0 }, y: { re: 3, im: 0 } },
  e: { x: { re: -1, im: 0 }, y: { re: -0, im: 0 } },
  f: { x: { re: 2.5, im: 0 }, y: { re: 0, im: 0 } },
};

function sg(x: number): string {
  return Object.is(x, -0) ? "-0" : String(x);
}

function floatText(re: number, im: number): string {
  return `${sg(re)}|${sg(im)}`;
}

/** fam3: a negative base gets the full operator list; a positive base stops at ln. */
const FAM3_FULL = [
  "-2", "-2/3", "-ln(2)", "ln(1/3)", "ln(0.5)", "atan(-3)", "atan(-1)", "-sqrt(2)", "-pi", "-e",
  "-exp(1)", "exp(1)*(-1)", "1-pi", "1/3-1", "-1", "0-2", "sin(-1)", "sin(4)", "cos(2)", "cos(3)",
  "tan(-1)", "tan(2)", "-cosh(1)", "-atan(2)", "-1e-30", "-(10^(-500))", "0-10^(-500)", "-(10^300)",
  "2-3", "-(2^0.5)", "ln(0.1)", "-ln(ln(10))", "asin(-0.5)", "-sinh(1)", "sinh(-1)", "tanh(-1)",
  "-sqrt(1/3)", "ln(2)-pi", "e-pi", "-(1/e)", "1/(-e)", "-cos(1)", "cos(1)-1", "sin(1)-1",
  "-(sin(1))", "sin(-0.5)", "exp(-1)-1", "atan(-1/3)", "-1/3",
];
const FAM3_SHORT = [
  "2", "2/3", "ln(2)", "pi", "e", "exp(1)", "sqrt(2)", "cos(1)", "sin(1)", "atan(3)", "cosh(1)",
  "1e-30", "10^(-500)", "tan(1)", "exp(-1)", "atan(1)", "ln(3)", "sinh(1)", "tanh(1)", "1/3",
  "asin(0.5)", "sin(2)", "cos(0.5)", "cos(-1)", "1-cos(1)", "e-2", "pi-3",
];

export function fam3Lines(): string[] {
  const out: string[] = [];
  const push = (b: string, full: boolean) => {
    const p = `(${b})`;
    out.push(
      `${p}*0`,
      `0*${p}`,
      `1/(${p}*0)`,
      `1/(0*${p})`,
      `ln(${p}*0)`,
      `ln(0*${p})`,
    );
    if (!full) return;
    out.push(
      `-(${p}*0)`,
      `(${p}*0)*0`,
      `0*(${p}*0)`,
      `sqrt(${p}*0)`,
      `exp(${p}*0)`,
      `(${p}*0)^3`,
      `(${p}*0)/1`,
      `0/${p}`,
      `${p}/(0)`,
    );
  };
  for (const b of FAM3_FULL) push(b, true);
  for (const b of FAM3_SHORT) push(b, false);
  const vars = [
    "x*0", "0*x", "1/(x*0)", "1/(0*x)", "ln(x*0)", "ln(0*x)", "-(x*0)", "(x*0)*0",
    "x*0*y", "y*x*0", "0*(x*y)", "(x*0)/y", "x/y*0", "0*x*0", "sqrt(x*0)", "exp(x*0)", "(x*0)^3",
  ];
  for (const env of ["a", "b", "c", "d", "e", "f"]) for (const src of vars) out.push(`${src} @ ${env}`);
  return out;
}

const FAM2_BASES = [
  "atan(-3)", "-atan(3)", "sin(-1)", "cos(2)", "ln(1/3)", "-ln(3)", "1/(-3/2)", "(-1/2)/2",
  "(-3/2)/(1/3)", "2/(-0.5)", "(1+(-3/2))/2", "(1/3)/(-1/2)", "exp(-1)*(-1)", "-0.25", "-1/4",
  "-0.5/2", "(-1)/4", "-1*(1/3)", "-(1/3)", "(-2)/3", "-ln(2)/2", "(-ln(2))/2", "(-ln(2))*(1/2)",
  "(-ln(2))*2", "(-1/2)*(1/2)", "(-e)/2", "-e/2", "-e*2", "(-2)*e", "(-1/2)*e", "(-2)/e",
  "-1/(2*e)", "1/3-1", "1/3-2/3", "1/2-1", "e-3", "pi-4", "1-pi", "-(pi)", "sqrt(2)-2", "2-pi",
  "(1-3)/2", "-(1/2)", "(-1)*(-1/2)*(-1)", "-4/2", "(-3)/(1/3)", "(-1/2)^1", "(-1/3)^3",
  "(-3/2)^2*(-1)", "tan(-1)", "sinh(-1)", "asin(-1/2)", "acos(2)",
];

export function fam2Lines(): string[] {
  const out: string[] = [];
  for (const b of FAM2_BASES) {
    const p = `(${b})`;
    out.push(
      `${p}*0`,
      `0*${p}`,
      `1/(${p}*0)`,
      `1/(0*${p})`,
      `ln(${p}*0)`,
      `ln(0*${p})`,
      `-(${p}*0)`,
      `1/(-(${p}*0))`,
      `(${p}*0)^-1`,
      `(${p}*0)/${p}`,
    );
  }
  return out;
}

const EXPR_BASES = [
  "1/3-1", "-2/3", "(-2/3)", "-1/2", "-3/2", "-5/2", "-1/3", "-5/3", "-e", "-ln(2)", "-2.5",
  "-2", "-1", "-3", "-0", "-pi", "-0.5", "-ln(3)", "-1/e", "-e^2", "2/3-1", "1/2-1", "-4",
  "-2*pi", "1-pi", "e-3", "-sqrt(2)", "-ln(2)/2", "(1/3-1)*3", "-(2/3)", "-1-2/3", "3/2",
  "1/3", "2", "ln(2)", "e", "i", "-i", "1-i", "0", "1", "-64", "-(1/e)", "2*(-1/3)", "(-1/3)*2",
  "-ln(2)*2", "(-ln(2))*(-1)",
];

export function exprLines(): string[] {
  const out: string[] = [];
  for (const b of EXPR_BASES) {
    const p = `(${b})`;
    out.push(
      `${p}*0`,
      `0*${p}`,
      `1/(${p}*0)`,
      `1/(0*${p})`,
      `ln(${p}*0)`,
      `ln(0*${p})`,
      `exp(${p}*0)`,
      `sqrt(${p}*0)`,
      `(${p}*0)^2`,
      `(${p}*0)^0.5`,
      `2^(${p}*0)`,
      `(${p}*0)^-1`,
      `0^(${p}*0)`,
      `(${p}*0)*(${p}*0)`,
      `${p}*0*0`,
      `${p}*(0*0)`,
      `(${p}*0)+1`,
      `(${p}*0)-1`,
      `1-(${p}*0)`,
      `${p}/(${p}*0)`,
      `0/(${p}*0)`,
      `atan(${p}*0)`,
      `cos(${p}*0)`,
      `1/sqrt(${p}*0)`,
      `ln(1/(${p}*0))`,
      `-(${p}*0)`,
      `(${p}*0)*i`,
      `i/(${p}*0)`,
      `(${p}*0)*(-1)`,
      `(-1)*(${p}*0)`,
      `ln(-(${p}*0))`,
      `0*0*${p}`,
      `(0*${p})*(0*${p})`,
      `2/(${p}*0)`,
      `(-2)/(${p}*0)`,
      `1/((${p}*0)*(${p}*0))`,
      `1/(0-${p}*0)`,
      `exp(1/(${p}*0))`,
      `(${p}*0)/${p}`,
      `atan(1/(${p}*0))`,
      `1/(0*${p}*${p})`,
      `1/(0*(${p}*${p}))`,
      `ln(${p}*0)*0`,
      `(${p}*0)^(${p}*0)`,
    );
  }
  const vars = [
    "x*0", "0*x", "x*y", "y*x", "1/(x*y)", "1/(y*x)", "1/(x*0)", "1/(0*x)", "ln(x*y)", "ln(y*x)",
    "ln(x*0)", "ln(0*x)", "exp(x*y)", "sqrt(x*y)", "(x*y)^2", "(x*y)^0.5", "x/y", "y/x", "1/(x/y)",
    "(x/3-1)*y", "1/((x/3-1)*y)", "ln((x/3-1)*y)", "(x-1)*y", "1/((x-1)*y)", "1/(x-x)", "x/(x*y)",
    "(x*y)/x", "1/(x*y)+1", "ln(x*y)*y", "-(x*y)", "1/(-x*y)", "ln(-x*y)", "(-x)*y", "1/((-x)*y)",
    "1/(-(x*y))", "1/(-x*0)", "1/((-2)*y)", "1/(-2*y)", "ln(-2*y)", "ln((-2)*y)", "1/(y*-2)",
    "ln(y*-2)", "ln(y*(-1/3))", "1/(y*(1/3-1))",
  ];
  for (const env of ["a", "b", "c", "d", "e", "f"]) for (const src of vars) out.push(`${src} @ ${env}`);
  out.push(
    "1/(-0)", "1/(0*(-1))", "2/(-0)", "(-2)/(-0)", "(-0.5)/(-0)", "1/sqrt(-0)", "0*(1/(-0))",
    "i/(-0)", "1/(-2*0)+1", "1/(-0)+1", "ln(-0)", "ln(-2*0)", "ln(-1*0)", "ln(0*(-2))", "1/(-2*0)",
    "1/(0*(-2))", "(-2)*0", "0*(-2)", "-2*0", "ln(-0.5*0)", "1/(-0.5*0)", "1/(-1*0)", "1/(-ln(2)*0)",
    "-ln(2)*0", "1/(0*(-pi))", "0*(1/(-0))", "1/(1/(-0))", "1/(1/(-2*0))", "1/(1/((1/3-1)*0))",
    "(1/(-2*0))*0", "0*(1/(-2*0))", "exp(1/(-2*0))", "exp(1/((1/3-1)*0))", "(-2/3)*0", "0*(-2/3)",
    "-0", "0*-1", "-1*0", "0*(-0)", "(-0)*(-0)", "(-0)*(-2)", "-2*-0", "(-2)*(-0)", "1/((-2)*(-0))",
    "1/(0/(-2))", "1/(0/(-2/3))", "0/(-2)", "0/(-2/3)", "1/(0/(-1/2))", "0/(1/3-1)", "1/(0/(1/3-1))",
    "1/(0^1*(-2))",
  );
  return out;
}

export const Z2 = [
  "(-0)+(-0)", "(0*(-2.5))+(0*(-2.5))", "(0*(-2))+(0*(-2))", "(0*(-2.5))+0", "0+(0*(-2.5))",
  "(0*(-2.5))-0", "(0*(-2.5))-(0*2.5)", "(0*(-2.5))+(0*(-2/3))", "(0*(-2.5))+((-ln(2)/2)*0)",
  "(-ln(2)/2)*0*(2.5)", "(-ln(2)/2)*0*((2.5)-(-e^2))", "(0*(-2.5))+((-ln(2)/2)*0*((2.5)-(-e^2)))",
  "(-2/3)*(0)", "((-2/3)*(0))*((e)*0*(-3/2))", "(e)*0*(-3/2)", "-(((-2/3)*(0))*((e)*0*(-3/2)))",
  "((e)*0*(-3/2))*((-2/3)*(0))", "(-0)*(-0)", "(0*(-2))*(0*(-2))", "(0*(-2.5))*(0*(-2.5))",
  "(0*(-2))*(0*2)", "(0*2)*(0*(-2))", "(-0)-0", "0-(0*2)", "0-(0*(-2))", "(0*(-2))-(0*(-2))",
];

export const DIS = [
  "atan(((-ln(2))*(-1))*0)", "(pi)*0*(-0.5)", "(0*(-2.5))+((-ln(2)/2)*0*((2.5)-(-e^2)))",
  "atan(0*((-2)*0*(-1/2)))", "(((0)*0*(-3/2))*0*(atan(-2/3)))+((-ln(2)/2)*0)",
  "-(((-2/3)*(0))*((e)*0*(-3/2)))", "((((-0))*(-e))*0)+((-3)*0)", "atan(1/(ln(0)))",
  "atan(0*((-e)*0*(-2/3)))", "((0*(-2.5))*((0)*0))+(-0)",
  "(((-ln(2)/2)*0*(-0))+((0)*((1/3-1))))*0", "(-2.5)*0*(((-3/2)*(3))*0*((0)^(3)))",
  "(-((2.5)-(pi)))*0*(-2.5)", "(((-5/2)*(-3))+((2)/(-1/e)))*(0*((-0.5)*0))",
  "(((-1)*0*(-1))+((-2.5)*0*(ln(2))))/(-e)",
];

function fzLines(): string[] {
  try {
    const raw = readFileSync(new URL("./probes/fz-diff.json", import.meta.url), "utf8");
    const parsed = JSON.parse(raw) as unknown;
    return Array.isArray(parsed) ? parsed.filter((s): s is string => typeof s === "string") : [];
  } catch {
    return [];
  }
}

function sweepWords(): string[] {
  const words: string[] = [];
  const gen = (prefix: string, ones: number, es: number, maxE: number) => {
    if (es === maxE && ones - es === 1 && ones === maxE + 1) {
      words.push(prefix);
      return;
    }
    const depth = ones - es;
    if (ones < maxE + 1) gen(prefix + "1", ones + 1, es, maxE);
    if (depth >= 2 && es < maxE) gen(prefix + "E", ones, es + 1, maxE);
  };
  // The reviewer's sweep generates every 1E word through ten E's, plus every
  // stored word that is only 1 and E. Ten E's is C_10 ≈ 17k words; six is the
  // same recurrence through a size that still finishes with the expression probes.
  for (let k = 0; k <= 6; k++) gen("", 0, 0, k);
  try {
    const best = JSON.parse(readFileSync(new URL("../best-known.json", import.meta.url), "utf8")) as {
      programs: Record<string, string>;
    };
    for (const word of Object.values(best.programs)) if (/^[1E]+$/.test(word)) words.push(word);
  } catch {
    // Generated words still run when the record file is missing.
  }
  return words;
}

type Got = { float: string; exact: string; fs: string | null; es: string | null; unverF: boolean; unverE: boolean };

function runExpr(line: string): { app: Got; wire: Got } {
  const [src, envKey] = line.split(" @ ");
  const vars: Record<string, Node> = envKey ? { x: V("x"), y: V("y") } : {};
  const env = envKey ? envs[envKey] ?? {} : {};
  const node = compileExpression(src ?? line, vars);
  const app = readNode(node, env);
  const packed = packCircuit(node);
  const unpacked = reportUnpacked(packed.tokens, packed.root, 80_000, env);
  const wireExact = unpacked.report;
  const wireFloat = evaluateReport(unpacked.node, env);
  const wire: Got = {
    float: wireFloat.unverified ? "unverified" : floatText(wireFloat.value.re, wireFloat.value.im),
    exact: wireExact.unverified ? "unverified" : formatExact(wireExact.value),
    fs: wireFloat.singular,
    es: wireExact.singular,
    unverF: wireFloat.unverified === true,
    unverE: wireExact.unverified === true,
  };
  return { app, wire };
}

function readNode(node: Node, env: Record<string, { re: number; im: number }>): Got {
  const floated = evaluateReport(node, env);
  const exact = exactReport(node, env, { maxNodes: 80_000 });
  return {
    float: floated.unverified ? "unverified" : floatText(floated.value.re, floated.value.im),
    exact: exact.unverified ? "unverified" : formatExact(exact.value),
    fs: floated.singular,
    es: exact.singular,
    unverF: floated.unverified === true,
    unverE: exact.unverified === true,
  };
}

const checkModule: CheckModule = {
  id: 119,
  weight: 8000,
  run(ctx) {
    const groups: Array<[string, string[]]> = [
      ["fam3", fam3Lines()],
      ["fam2", fam2Lines()],
      ["exprs", exprLines()],
      ["z2", Z2],
      ["dis", DIS],
      ["fz", fzLines()],
    ];
    for (const [name, lines] of groups) {
      for (const line of lines) {
        let got: { app: Got; wire: Got };
        try {
          got = runExpr(line);
        } catch (err) {
          ctx.fail("FAIL probe threw", name, line, err instanceof Error ? err.message.slice(0, 120) : String(err));
          continue;
        }
        if (got.app.exact !== got.wire.exact || got.app.es !== got.wire.es || got.app.float !== got.wire.float || got.app.fs !== got.wire.fs) {
          ctx.fail("FAIL probe wire", name, line, got.app, got.wire);
        }
      }
    }

    // The two certificates that were wrong, and the IEEE products that were refused.
    const locked: Array<[string, string, string | null]> = [
      ["-(((-2/3)*0)*((e*0)*(-3/2)))", "-0|0", null],
      ["(((0)*0*(-3/2))*0*(atan(-2/3)))+((-ln(2)/2)*0)", "0|0", null],
      ["((-2/3)*0)*((-2/3)*0)", "0|0", null],
      ["((-2/3)*0)^-1", "-Infinity|0", SINGULAR_LN0],
      ["i/((1/3-1)*0)", "0|-Infinity", SINGULAR_LN0],
      ["0*cos(1)", "0|0", null],
      ["0*cos(2)", "-0|0", null],
    ];
    for (const [source, float, note] of locked) {
      const { app, wire } = runExpr(source);
      if (app.unverF || app.unverE || app.float !== float || app.fs !== note || app.es !== note) {
        ctx.fail("FAIL probe lock", source, app);
      }
      if (wire.float !== app.float || wire.exact !== app.exact) ctx.fail("FAIL probe lock wire", source, wire);
    }

    for (const word of sweepWords()) {
      let node: Node;
      try {
        node = nodeFromRpn(word.split(""));
      } catch {
        continue;
      }
      const app = readNode(node, {});
      const packed = packCircuit(node);
      const unpacked = reportUnpacked(packed.tokens, packed.root, 80_000, {});
      const wire = unpacked.report;
      const wireExact = wire.unverified ? "unverified" : formatExact(wire.value);
      const floated = evaluateReport(unpacked.node, {});
      const wireFloat = floated.unverified ? "unverified" : floatText(floated.value.re, floated.value.im);
      if (app.exact !== wireExact || app.es !== wire.singular || app.float !== wireFloat || app.fs !== floated.singular) {
        ctx.fail("FAIL sweep wire", word, app.exact, wireExact, app.float, wireFloat);
      }
    }
  },
};

export default checkModule;
