import { exactReport, formatExact } from "../exact";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * (x − 1) must not certify the square term as a real 0.
 * (10^n+i)/(10^n−i) − 1 is −2×10^(−2n) + 2×10^(−n) i. At n = 200 that real
 * was certified as 0, on this branch and on v1.0.13. At n = 300 and n = 400
 * the square is past 480 digits; the remembered-sum path certified a pure
 * imaginary (v1.0.13 refused the n = 400 forms). A certified value has to be
 * the leading terms below. A refusal is also right when the square does not
 * fit. A pure imaginary certification is not.
 * The worker wire evaluates the same circuit the app does.
 */
function sources(n: number): Array<[string, string]> {
  const n2 = 2 * n;
  return [
    [`(10^${n}+i)/(10^${n}-i)-1`, `−2×10^−${n2} + 2×10^−${n}i`],
    [`(10^${n}-i)/(10^${n}+i)-1`, `−2×10^−${n2} − 2×10^−${n}i`],
    [`(10^${n}+i)/(10^${n}+2*i)-1`, `−2×10^−${n2} − 1×10^−${n}i`],
    [`(10^${n}+2*i)/(10^${n}+i)-1`, `1×10^−${n2} + 1×10^−${n}i`],
    [`10^${n}/(10^${n}+i)-1`, `−1×10^−${n2} − 1×10^−${n}i`],
    [`1/(10^${n}+i)*10^${n}-1`, `−1×10^−${n2} − 1×10^−${n}i`],
    [`sqrt(10^${n}+i)/10^${n / 2}-1`, `1.25×10^−${n2 + 1} + 5×10^−${n + 1}i`],
  ];
}

const checkModule: CheckModule = {
  id: 113,
  weight: 60604,
  run(ctx) {
    const judge = (source: string, want: string, allowRefusal: boolean) => {
      const node = compileExpression(source, {});
      const packed = packCircuit(node);
      const reports = [
        ["app", exactReport(node)],
        ["wire", exactReport(unpackCircuit(packed.tokens, packed.root))],
      ] as const;
      for (const [path, report] of reports) {
        if (report.unverified) {
          if (!allowRefusal) ctx.fail(`FAIL x-1 ${path} ${source} refused`);
          continue;
        }
        const got = formatExact(report.value);
        if (got !== want) ctx.fail(`FAIL x-1 ${path} ${source} got="${got}" want="${want}"`);
      }
    };
    // These fit in 480 digits, so the square is part of the certified value.
    judge("(10^20+i)/(10^20-i)-1", "−2×10^−40 + 2×10^−20i", false);
    for (const [source, want] of sources(200)) judge(source, want, false);
    // The square is past the 480-digit cap. A certified leading term is right; so is a refusal.
    for (const n of [300, 400]) {
      for (const [source, want] of sources(n)) judge(source, want, true);
    }
  },
};

export default checkModule;
