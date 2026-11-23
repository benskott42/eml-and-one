/**
 * Fixes ported from main's exact engine (1.0.1, 1.0.2) onto v1.1's.
 * See docs/port-main-engine.md. Every value here was checked against mpmath.
 */
import { exactReport, formatExact } from "./exact";
import { compileExpression } from "./parse";

function shown(source: string): string {
  const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
  if (report.unverified) return "unverified";
  if (report.notCertified) return "not certified";
  return formatExact(report.value).replace(/​/g, "");
}

export function runPortChecks(): number {
  let failed = 0;
  const rows: Array<[string, string, string]> = [
    // 1.0.2 (90c3eb9): the remembered-huge-sum marker is found anywhere in the circuit.
    ["(10^400+i)*2", "unverified", "the product drops the small part"],
    ["2*(10^400+pi)", "unverified", "the product drops the small part"],
    ["(10^400+2*i)-10^400", "2i", "the remembered sum still recovers its small part"],
    // 1.0.1: 0 times a finite value past float range is exactly 0 (it was −∞).
    ["exp(800)*0", "0", "exp(800) is finite"],
    ["0*exp(800)", "0", "exp(800) is finite"],
    ["ln(0)*0", "undefined", "a real pole times 0 stays undefined"],
    // 1.0.1 (6704f98, 2c5db2f): a lifted tiny sum sizes its cancellation (was 1.00000003×10^−420).
    ["1e-320*(1+1e-100)-1e-320", "1×10^−420", "mpmath: 1e-420"],
    ["1e-320*e/e-1e-320*(1+1e-100)", "−1×10^−420", "mpmath: -1e-420"],
    ["exp(-1000)-exp(-1001)", "3.20861797491×10^−435", "mpmath: 3.20861797491e-435"],
  ];
  for (const [source, want, why] of rows) {
    const got = shown(source);
    if (got !== want) {
      failed += 1;
      console.log("FAIL port", source, "got", got, "want", want, `(${why})`);
    } else console.log("port", source, got);
  }
  return failed;
}
