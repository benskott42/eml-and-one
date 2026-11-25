import { exactReport, exactToFloat } from "../exact";
import { beyondFloatBound } from "../float-bound";
import { formatC } from "../format";
import { evaluateReport } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * Step 7: re-test of docs/known-limitations.md items.
 * sinh(±0.00005i) in float mode tidies its -1e-17 real dust to 0 and prints
 * ±0.0000499999999792i ≈ (accurate to 12 significant digits, matching i·sin(0.00005))
 * with no false-positive flag.
 */
const checkModule: CheckModule = {
  id: 101,
  weight: 200,
  run(ctx) {
    const cases: [string, string][] = [
      ["sinh(0.00005*i)", "0.0000499999999792i ≈"],
      ["sinh(-0.00005*i)", "−0.0000499999999792i ≈"],
    ];
    for (const [src, wantFloat] of cases) {
      const node = compileExpression(src, {});
      const fl = evaluateReport(node, {});
      const flText = formatC(fl.value);
      const ex = exactReport(node, {});
      if (flText !== wantFloat) {
        ctx.fail(`FAIL sinh-float-display ${src} got="${flText}" want="${wantFloat}"`);
      }
      if (beyondFloatBound(fl.value, exactToFloat(ex.value))) {
        ctx.fail(`FAIL sinh-float-bound ${src} flagged unexpectedly`);
      }
    }
  },
};

export default checkModule;
