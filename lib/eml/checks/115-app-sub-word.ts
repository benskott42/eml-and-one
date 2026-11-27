import { APP_SUB_WORD, variableRpnFromNode } from "../export";
import { V, evaluateReport } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * The compiler's x − y for variable operands is exactly APP_SUB_WORD, the word
 * that formal/lean/Eml/AppSub.lean proves evaluates to a − b for every a, b
 * (EmlDir, b = 0 included). If lowering changes, this fails until the word and
 * its Lean proof are updated together. The float engine agrees on sample points,
 * b = 0 among them.
 */
const points: [number, number, number, number][] = [
  [3, 0, 5, 0],
  [0, 0, 0, 0],
  [2, -1, 0, 0],
  [-1.5, 2, 0.25, -3],
  [1e10, 0, 1, 1],
  [0, 3, 0, -3],
];

const checkModule: CheckModule = {
  id: 115,
  weight: 400,
  run(ctx) {
    const x = V("x");
    const y = V("y");
    const node = compileExpression("x-y", { x, y });
    const word = variableRpnFromNode(node);
    if (word !== APP_SUB_WORD) {
      ctx.fail(`FAIL x−y circuit changed (K ${word?.length ?? "?"}): update APP_SUB_WORD and formal/lean/Eml/AppSub.lean`);
      return;
    }
    for (const [ar, ai, br, bi] of points) {
      const r = evaluateReport(node, { x: { re: ar, im: ai }, y: { re: br, im: bi } });
      const re = ar - br;
      const im = ai - bi;
      const tol = 1e-9 * Math.max(1, Math.hypot(ar, ai), Math.hypot(br, bi));
      if (Math.abs(r.value.re - re) > tol || Math.abs(r.value.im - im) > tol) {
        ctx.fail(`FAIL x−y circuit at (${ar}+${ai}i) − (${br}+${bi}i): ${r.value.re} + ${r.value.im}i`);
      }
    }
  },
};

export default checkModule;
