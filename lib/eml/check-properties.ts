import { spawnSync } from "node:child_process";
import path from "node:path";
import Decimal from "decimal.js";
import { c, type C } from "./complex";
import { beyondFloatBound, exactEvaluate, exactReport, exactToFloat, formatExact } from "./exact";
import { unaryNode } from "./library";
import { circuitStats, evaluate, evaluateReport, type Node } from "./node";
import { compileExpression } from "./parse";

/**
 * Classes of input, not single repros.
 * A circuit is a function of its expression: the same source builds the same
 * gates after other expressions, and a tiny real sum or difference either
 * agrees with the exact value or carries a float flag.
 * check.ts runs branchChecks as a block of its own.
 */
export function runPropertyChecks(): number {
  let failed = 0;
  const repoRoot = path.resolve(__dirname, "../..");
  // node + tsx's cli.mjs, not node_modules/.bin/tsx: that shim does not spawn on Windows.
  const cold = spawnSync(
    process.execPath,
    [
      path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs"),
      "-e",
      `import { compileExpression } from "./lib/eml/parse";
import { circuitStats, evaluate } from "./lib/eml/node";
const n = compileExpression("arcsin(2)", {});
const s = circuitStats(n);
const v = evaluate(n);
console.log(JSON.stringify({ dag: s.dagGates, depth: s.depth, tree: s.treeGates.toString(), re: v.re, im: v.im }));`,
    ],
    { encoding: "utf8", cwd: repoRoot },
  );
  if (cold.status !== 0 || !cold.stdout.trim()) {
    failed += 1;
    console.log("FAIL cold arcsin", cold.status, cold.stderr?.slice(0, 400));
    return failed;
  }
  const expected = JSON.parse(cold.stdout.trim()) as { dag: number; depth: number; tree: string; re: number; im: number };
  const noise = ["1e-5", "4", "0.5", "3", "2", "pi", "1e-8", "sqrt(2)"];
  let seed = 17;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const order = noise.slice().sort(() => rand() - 0.5);
  for (const source of order) compileExpression(source, {});
  const again = compileExpression("arcsin(2)", {});
  const stats = circuitStats(again);
  const value = evaluate(again);
  const same =
    stats.dagGates === expected.dag &&
    stats.depth === expected.depth &&
    stats.treeGates.toString() === expected.tree &&
    Object.is(value.re, expected.re) &&
    Object.is(value.im, expected.im);
  if (!same) {
    failed += 1;
    console.log("FAIL history-independent arcsin(2)", order, { dag: stats.dagGates, depth: stats.depth, tree: stats.treeGates.toString(), re: value.re, im: value.im }, expected);
  }

  const magnitudes = [1e-4, 1e-8, 1e-20, 1e-40, 1e-100, 1e-300];
  for (const mag of magnitudes) {
    for (const op of ["+", "-"] as const) {
      const aText = ((rand() < 0.5 ? -1 : 1) * mag * (0.25 + rand())).toExponential(6);
      const bText = ((rand() < 0.5 ? -1 : 1) * mag * (0.25 + rand())).toExponential(6);
      const source = `(${aText})${op}(${bText})`;
      try {
        const node = compileExpression(source, {});
        const report = evaluateReport(node, {}, { maxNodes: 200_000 });
        const exact = exactEvaluate(node, {}, { maxNodes: 200_000 });
        const want = op === "+" ? new Decimal(aText).plus(bText) : new Decimal(aText).minus(bText);
        const scale = Decimal.max(want.abs(), new Decimal("1e-320"));
        if (!exact.im.eq(0) || exact.re.sub(want).abs().div(scale).gt("1e-9")) {
          failed += 1;
          console.log("FAIL tiny exact", source, exact.re.toString(), want.toString());
        }
        const floated = exactToFloat(exact);
        const flagged = Boolean(report.singular || report.overflowed || report.underflowed) || beyondFloatBound(report.value, floated);
        const floatScale = Math.max(Math.abs(want.toNumber()), 1e-320);
        const floatErr = Math.hypot(report.value.re - want.toNumber(), report.value.im);
        if (floatErr > 1e-4 * floatScale && !flagged) {
          failed += 1;
          console.log("FAIL tiny float unflagged", source, report.value, floated, want.toString());
        }
      } catch (err) {
        failed += 1;
        console.log("FAIL tiny threw", source, err instanceof Error ? err.message : err);
      }
    }
  }
  return failed;
}

/** Relative error. A zero target uses an absolute tolerance of `tol`. */
function relClose(got: C, want: C, tol: number): boolean {
  if (!Number.isFinite(got.re) || !Number.isFinite(got.im)) return false;
  const err = Math.hypot(got.re - want.re, got.im - want.im);
  if (want.re === 0 && want.im === 0) return err <= 1e-15;
  const scale = Math.max(Math.hypot(want.re, want.im), 1e-300);
  return err <= tol * scale;
}

/**
 * Principal branch, one convention in both modes (mpmath):
 * arcsin(x) = π/2 − i·arcosh(x) for real x > 1, and the odd value for x < −1.
 * arccos = π/2 − arcsin, and arsinh(z) = −i·arcsin(i·z).
 * The table is the inverse-function regression set. A variable just off the cut is not
 * given a float special case: the 17 points below must raise the float flag.
 */
export function branchChecks(): number {
  let failed = 0;
  const asinLiteral: Array<[number, number, number, number]> = [
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
  for (const [re, im, wantRe, wantIm] of asinLiteral) {
    const want = c(wantRe, wantIm);
    const source = `arcsin((${re})+(${im})*i)`;
    const node = compileExpression(source, {});
    const got = evaluate(node, {}, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
    if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL arcsin literal", source, got, exact, want);
    }
  }

  const variable = unaryNode("arcsin");
  const asinVar: Array<[number, number, number, number, boolean]> = [
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
  for (const [re, im, wantRe, wantIm, floatToo] of asinVar) {
    const want = c(wantRe, wantIm);
    const env = { x: c(re, im) };
    const got = evaluate(variable, env, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(variable, env, { maxNodes: 2_000_000 }));
    const floatOk = !floatToo || relClose(got, want, 1e-7);
    if (!floatOk || !relClose(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL arcsin variable", re, im, got, exact, want);
    }
    if (!floatToo && !beyondFloatBound(got, exact)) {
      failed += 1;
      console.log("FAIL arcsin near-cut unflagged", re, im, got, exact);
    }
  }

  const via: Array<[string, number, number, number, number]> = [
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
  for (const [fn, re, im, wantRe, wantIm] of via) {
    const want = c(wantRe, wantIm);
    const source = re === 0 && (im === 1 || im === -1) ? `${fn}(${im < 0 ? "-" : ""}i)` : `${fn}((${re})+(${im})*i)`;
    const node = compileExpression(source, {});
    const got = evaluate(node, {}, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
    if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-14)) {
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
    if (!relClose(got, want, 1e-7) || report.singular || !relClose(exactToFloat(report.value), want, 1e-14)) {
      failed += 1;
      console.log("FAIL arsinh variable", re, im, got, report.singular, exactToFloat(report.value), want);
    }
  }

  for (const [source, want] of [
    ["1e-30", "1×10^−30"],
    ["-1e-40", "−1×10^−40"],
    ["2e-80+1e-80", "3×10^−80"],
    ["1e-90*3", "3×10^−90"],
    ["1e-29", "1×10^−29"],
    ["2", "2"],
    ["6*7", "42"],
  ] as Array<[string, string]>) {
    const text = formatExact(exactEvaluate(compileExpression(source, {}), {}));
    if (text !== want) {
      failed += 1;
      console.log("FAIL exact display", source, text, want);
    }
  }

  for (const [source, wantRe, wantIm] of [
    ["1e-100-3e-100", -2e-100, 0],
    ["0-1e-90", -1e-90, 0],
    ["(1e-90*i)-(2e-90)", -2e-90, 1e-90],
    ["3e-20-1e-20", 2e-20, 0],
  ] as Array<[string, number, number]>) {
    const node = compileExpression(source, {});
    const want = c(wantRe, wantIm);
    const got = evaluate(node, {});
    const exact = exactToFloat(exactEvaluate(node, {}));
    // A pure-imaginary minuend leaves a real 0 − tiny. Float drops that real part.
    // Exact keeps it, and the float-vs-exact flag has to catch the drop.
    const floatOk = relClose(got, want, 1e-9) || beyondFloatBound(got, exact);
    if (!floatOk || !relClose(exact, want, 1e-14)) {
      failed += 1;
      console.log("FAIL tiny sub table", source, got, exact, want);
    }
  }

  // The off-cut side, |x| > 1 and |eps/x| ≤ 10^(−15). Float keeps the cut value.
  // These 17 are not given a special case. The flag has to name the disagreement.
  const nearCut: Array<[string, number, number]> = [
    ["arcsin", 2, 2e-16],
    ["arcsin", -2, -2e-16],
    ["arcsin", 4, 4e-16],
    ["arcsin", -4, -4e-16],
    ["arcsin", 10, 1e-15],
    ["arcsin", -10, -1e-15],
    ["arccos", 2, 2e-16],
    ["arccos", -2, -2e-16],
    ["arccos", 4, 4e-16],
    ["arccos", -4, -4e-16],
    ["arccos", 10, 1e-15],
    ["arccos", -10, -1e-15],
    ["arsinh", -2e-16, 2],
    ["arsinh", 2e-16, -2],
    ["arsinh", -4e-16, 4],
    ["arsinh", 4e-16, -4],
    ["arsinh", -1e-15, 10],
  ];
  const built = new Map<string, Node>();
  for (const [name, re, im] of nearCut) {
    let node = built.get(name);
    if (!node) {
      node = unaryNode(name);
      built.set(name, node);
    }
    const env = { x: c(re, im) };
    const got = evaluate(node, env, { maxNodes: 2_000_000 });
    const exact = exactToFloat(exactEvaluate(node, env, { maxNodes: 2_000_000 }));
    const side =
      name === "arsinh"
        ? Math.sign(exact.re) === Math.sign(re) && Math.abs(exact.re) > 0.1
        : Math.sign(exact.im) === (name === "arccos" ? -Math.sign(im) : Math.sign(im)) && Math.abs(exact.im) > 0.1;
    if (!side || !beyondFloatBound(got, exact)) {
      failed += 1;
      console.log("FAIL near-cut flag", name, re, im, got, exact, side);
    }
  }

  // The three functions are one branch: arccos = π/2 − arcsin and arsinh(z) = −i·arcsin(i z).
  const samples = [c(0.3, 0), c(0.3, 0.2), c(-0.4, 0.5), c(2, 1), c(-3, -1)];
  const asinOf = unaryNode("arcsin");
  const acosOf = unaryNode("arccos");
  const asinhOf = unaryNode("arsinh");
  for (const z of samples) {
    const asin = exactToFloat(exactEvaluate(asinOf, { x: z }, { maxNodes: 2_000_000 }));
    const acos = exactToFloat(exactEvaluate(acosOf, { x: z }, { maxNodes: 2_000_000 }));
    const wantAcos = c(Math.PI / 2 - asin.re, -asin.im);
    if (!relClose(acos, wantAcos, 1e-9)) {
      failed += 1;
      console.log("FAIL arccos identity", z, acos, wantAcos);
    }
    const iz = c(-z.im, z.re);
    const asinIz = exactToFloat(exactEvaluate(asinOf, { x: iz }, { maxNodes: 2_000_000 }));
    const asinh = exactToFloat(exactEvaluate(asinhOf, { x: z }, { maxNodes: 2_000_000 }));
    const wantAsinh = c(asinIz.im, -asinIz.re);
    if (!relClose(asinh, wantAsinh, 1e-9)) {
      failed += 1;
      console.log("FAIL arsinh identity", z, asinh, wantAsinh);
    }
  }
  return failed;
}
