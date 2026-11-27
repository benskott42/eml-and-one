import { exactReport, formatExact } from "../exact";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Regressions for:
 * A. A huge integer kept beside a non-integer (10^400 + i) is evaluated as that sum.
 *    Every circuit built on it was refused before: (10^400 + i)/7 said it could not verify.
 *    A circuit rebuilt from its tokens has no record of the sum, and stays refused or right.
 * B. A part far below the other keeps only the decades its pass resolved. (10^100 + i)·2
 *    printed 2.000…0078i: the raised read was rounded back to 120 significant digits.
 * Expected values are mpmath at 1000 digits, principal branches.
 */
const checkModule: CheckModule = {
  id: 110,
  weight: 15000,
  run(ctx) {
    const kept: [string, string][] = [
      ["(10^400+i)/7", "1.428571428571×10^399 + 0.142857142857i"],
      ["(10^400+2i)/7", "1.428571428571×10^399 + 0.285714285714i"],
      ["(10^400+i)*2", "2×10^400 + 2i"],
      ["(10^400+i)*i", "−1 + 1×10^400i"],
      ["(10^400+i)^2", "1×10^800 + 2×10^400i"],
      ["1/(10^400+i)", "1×10^−400 − 1×10^−800i"],
      ["(10^400-i)/(10^400+i)", "1 − 2×10^−400i"],
      ["sqrt(10^400+i)", "1×10^200 + 5×10^−201i"],
      ["ln(10^400+i)", "921.034037197618 + 1×10^−400i"],
      ["(10^420+i)/3", "3.333333333333×10^419 + 0.333333333333i"],
      ["(10^400+i)-10^400", "i"],
      ["2*(10^400+pi)", "2×10^400"],
      ["(10^400-(2-2*i))^-1", "1×10^−400 − 2×10^−800i"],
      ["(10^100+i)*2", "2×10^100 + 2i"],
      ["(10^200+i)*2", "2×10^200 + 2i"],
      ["(10^300+i)*2", "2×10^300 + 2i"],
      ["(10^300+i)*i", "−1 + 1×10^300i"],
    ];
    for (const [source, want] of kept) {
      const node = compileExpression(source, {});
      const report = exactReport(node);
      const got = report.unverified ? "unverified" : formatExact(report.value);
      if (got !== want) ctx.fail(`FAIL huge-sum ${source} got="${got}" want="${want}"`);
      // The packed circuit loses the remembered sum. It may refuse, but never certify the bare integer.
      const packed = packCircuit(node);
      const wire = exactReport(unpackCircuit(packed.tokens, packed.root));
      const wireGot = wire.unverified ? "unverified" : formatExact(wire.value);
      if (wireGot !== "unverified" && wireGot !== want) ctx.fail(`FAIL huge-sum wire ${source} got="${wireGot}" want="${want}" or unverified`);
    }
    // Past what 480 digits can hold, the beside sum stays refused.
    const refused = ["(10^400+0.5)*2-2*10^400", "atan(10^400-6+i)", "atanh(exp(-50)-10^400)"];
    for (const source of refused) {
      const report = exactReport(compileExpression(source, {}));
      if (!report.unverified) ctx.fail(`FAIL huge-sum refusal ${source} got="${formatExact(report.value)}"`);
    }
  },
};

export default checkModule;
