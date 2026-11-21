import Decimal from "decimal.js";
import { exactReport, formatExact } from "./exact";
import { compileExpression } from "./parse";
import { packCircuit, unpackCircuit } from "./wire";

/**
 * Values that exact mode certified wrong, and their siblings.
 * Every row runs the worker's path (parse, pack, unpack, exact report with the
 * worker's node budget), twice, so the second run reads the pure cache.
 * References are mpmath at 250 digits.
 */
const R = Decimal.clone({ precision: 200 });

function workerReport(source: string) {
  const packed = packCircuit(compileExpression(source, {}));
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
}

/** Agrees to 30 significant digits. A zero reference part must be an exact zero. */
function agrees(got: Decimal, want: string): boolean {
  const ref = new R(want);
  const value = new R(got.toString());
  if (ref.isZero()) return value.isZero();
  if (!value.isFinite()) return false;
  return value.sub(ref).abs().lte(ref.abs().mul("1e-30"));
}

/**
 * Tiny sums and differences behind a 10^k lift. A subnormal operand was lifted
 * only to 10^307, a pure imaginary that the lift pushed past π fell back to a
 * word that rounds a 10^(−200) term to 0, and a cancellation of 96 to 112
 * decades inside the lift was not seen by the exact engine.
 */
const tinyRows: Array<[string, string, string]> = [
  ["1e-320*(1+1e-100)-1e-320", "1e-420", "0"],
  ["(1+1e-100)*1e-320-1e-320", "1e-420", "0"],
  ["2e-320*(1+1e-100)-2e-320", "2e-420", "0"],
  ["1e-320*(1+1e-110)-1e-320", "1e-430", "0"],
  ["1e-320*(1+1e-100)+(-1e-320)", "1e-420", "0"],
  ["5e-322*(1+1e-60)-5e-322", "5e-382", "0"],
  ["1e-300*(1+1e-110)-1e-300", "1e-410", "0"],
  ["1e-5*(1+1e-110)-1e-5", "1e-115", "0"],
  ["1e-320*i*(1+1e-100)-1e-320*i", "0", "1e-420"],
  ["5e-300*i-4e-300*i", "0", "1e-300"],
  ["5e-200*i-4e-200*i", "0", "1e-200"],
  ["5e-200*i+3e-200*i", "0", "8e-200"],
  ["5e-200*i+(-4e-200*i)", "0", "1e-200"],
  ["5e-320*i+3e-320*i", "0", "8e-320"],
];

function certifyChecks(): number {
  let failed = 0;
  for (const [source, re, im] of tinyRows) {
    for (const run of ["first", "cached"]) {
      const report = workerReport(source);
      const text = formatExact(report.value);
      const ok = report.unverified !== true && report.singular === null && agrees(report.value.re, re) && agrees(report.value.im, im);
      if (!ok) {
        failed += 1;
        console.log("FAIL certify tiny", run, source, report.unverified ? "unverified" : text, report.value.re.toString(), report.value.im.toString());
      } else {
        console.log("certify tiny", run, source, text);
      }
    }
  }
  return failed;
}

/** Called by check.ts after the property checks. */
export function runCertifyChecks(): number {
  return certifyChecks();
}
