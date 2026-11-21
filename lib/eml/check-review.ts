import Decimal from "decimal.js";
import { exactReport, formatExact } from "./exact";
import { evaluateReport } from "./node";
import { compileExpression } from "./parse";
import { packCircuit, unpackCircuit } from "./wire";

/**
 * Regressions from the outside review of 2026-11-21 (review-verify-B.md).
 * References are mpmath at 80 digits, written to 45. Every row runs the
 * screen's worker path: parse, pack, unpack, then the exact engine.
 */
const R = Decimal.clone({ precision: 200 });

function workerReport(source: string) {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
}

/** A zero part must be exactly zero; a nonzero part must agree to `digits` significant digits. */
function agrees(got: Decimal, want: string, digits: number): boolean {
  const w = new R(want);
  const g = new R(got.toString());
  if (w.isZero()) return g.isZero();
  return g.sub(w).abs().div(w.abs()).lte(new R(10).pow(-digits));
}

function exactRows(label: string, rows: Array<[string, string, string]>, digits = 40): number {
  let failed = 0;
  for (const [source, re, im] of rows) {
    const report = workerReport(source);
    if (report.unverified || !agrees(report.value.re, re, digits) || !agrees(report.value.im, im, digits)) {
      failed += 1;
      console.log(`FAIL ${label}`, source, report.unverified ? "unverified" : formatExact(report.value), "want", re, im);
    }
  }
  return failed;
}

/** B1/B2 (R2): sinh, artanh, and arcsin series are exact to 40 digits or marked, never a certified wrong value. */
function seriesChecks(): number {
  let failed = exactRows("review series", [
    ["sinh(5e-7)-5e-7", "2.08333333333335937500000000015500992063492117e-20", "0"],
    ["sinh(1e-7)-1e-7", "1.6666666666666675000000000000001984126984127e-22", "0"],
    ["sinh(1e-7)", "1.0000000000000016666666666666675e-7", "0"],
    ["artanh(5e-7)-5e-7", "4.1666666666672916666666667782738095238312252e-20", "0"],
    ["artanh(1e-7)-1e-7", "3.3333333333333533333333333334761904761904773e-22", "0"],
    ["sinh(1e-7*i)-1e-7*i", "0", "-1.66666666666666583333333333333353174603174603e-22"],
    ["artanh(3e-7*i)", "0", "2.99999999999991000000000000485999999999968757e-7"],
    ["arcsin(1e-5)", "1.00000000001666666666741666666671130952381256e-5", "0"],
    ["(arcsin(1e-5)-1e-5-(1e-15)/6)*1e25", "7.50000000044642857145895337301811023178228031e-2", "0"],
    ["arcsin(5e-5*i)", "0", "4.99999999791666666901041666317894345831492589e-5"],
    ["arcsin(1e11)", "1.5707963267948966192313216916397514420985847", "-2.60215832034944478336151131229861828516876165e+1"],
    ["arcsin(-1e11*i)", "0", "-2.60215832034944478336151631229861828516876165e+1"],
    ["arcsin(3e12-2e12*i)", "9.82793723247329067985710593263186724556049051e-1", "-2.96066429752192618856598732910567566575493401e+1"],
    ["(arcsin(1e11)+i*ln(2e11))*1e23", "1.5707963267948966192313216916397514420985847e+23", "2.50000000000000000000009375000000000000000001"],
    ["sinh(0)", "0", "0"],
    ["artanh(0)", "0", "0"],
  ]);
  // Past the cap the lead term is all there is: the zero is a series zero and stays unverified.
  for (const source of ["sinh(1e-300)-1e-300", "artanh(1e-300)-1e-300", "arcsin(1e-300)-1e-300"]) {
    const report = workerReport(source);
    if (!report.unverified) {
      failed += 1;
      console.log("FAIL review series certified", source, formatExact(report.value));
    }
  }
  // The float screen keeps its digits below the old 10^(−6) shortcut.
  for (const [source, want] of [["sinh(1e-7)", Math.sinh(1e-7)], ["artanh(5e-7)", Math.atanh(5e-7)], ["arcsin(1e-5)", Math.asin(1e-5)]] as const) {
    const got = evaluateReport(compileExpression(source, {})).value;
    if (!(Math.abs(got.re - want) <= 1e-14 * Math.abs(want)) || got.im !== 0) {
      failed += 1;
      console.log("FAIL review series float", source, got.re, got.im, "want", want);
    }
  }
  return failed;
}

/** R3: tanh and sigmoid tails. Float mode no longer forms ∞/∞; exact mode keeps its digits. */
function tailChecks(): number {
  let failed = exactRows("review tails", [
    ["tanh(20)", "9.99999999999999991503291489416822045438558191e-1", "0"],
    ["tanh(2+3*i)", "9.6538587902213312427848026939456068587972965e-1", "-9.88437503832249372031403430350121097961813353e-3"],
    ["sigmoid(-800)", "3.66787458417768721345549565426079821546963423e-348", "0"],
    ["sigmoid(-3)", "4.74258731775667808788481517717522013861794324e-2", "0"],
  ]);
  const floatRows: Array<[string, number]> = [
    ["tanh(354)", 1],
    ["tanh(355)", 1],
    ["tanh(800)", 1],
    ["tanh(-800)", -1],
    ["tanh(1)", Math.tanh(1)],
    ["tanh(20)", Math.tanh(20)],
    ["sigmoid(-710)", 0],
    ["sigmoid(-800)", 0],
    ["sigmoid(-30)", 1 / (1 + Math.exp(30))],
    ["sigmoid(800)", 1],
  ];
  for (const [source, want] of floatRows) {
    const report = evaluateReport(compileExpression(source, {}));
    const got = report.value;
    const tol = want === 0 ? 1e-300 : 1e-13 * Math.abs(want);
    if (!(Math.abs(got.re - want) <= tol) || got.im !== 0 || report.overflowed || Math.abs(got.re) > 1) {
      failed += 1;
      console.log("FAIL review tails float", source, got.re, got.im, report.overflowed ? "overflowed" : "", "want", want);
    }
  }
  return failed;
}

/** Called by check.ts after the main blocks. */
export function runReviewChecks(): number {
  return seriesChecks() + tailChecks();
}
