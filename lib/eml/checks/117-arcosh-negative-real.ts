import { exactReport, exactToFloat } from "../exact";
import { evaluateReport } from "../node";
import { reportUnpacked } from "../packed-eval";
import { compileExpression } from "../parse";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Float arcosh of a negative real stays on the same bank as exact: Im ≥ 0.
 * The spread covers x < −1, x = −1, −1 < x < 0, and −0, on the app path and
 * the worker wire.
 */
const probes = ["-1e6", "-3", "-1", "-0.5", "-1e-9", "-0"];

function matches(got: { re: number; im: number }, want: { re: number; im: number }): boolean {
  const scale = Math.max(1, Math.hypot(want.re, want.im));
  if (Math.abs(got.re - want.re) > 1e-8 * scale || Math.abs(got.im - want.im) > 1e-8 * scale) return false;
  return !(got.im < 0 || Object.is(got.im, -0));
}

const checkModule: CheckModule = {
  id: 117,
  weight: 8000,
  run(ctx) {
    for (const text of probes) {
      const source = `arcosh(${text})`;
      const node = compileExpression(source, {});
      const appExact = exactReport(node);
      if (appExact.unverified) {
        ctx.fail(`FAIL arcosh app ${source} exact unverified`);
        continue;
      }
      const packed = packCircuit(node);
      const wired = reportUnpacked(packed.tokens, packed.root);
      if (wired.report.unverified) {
        ctx.fail(`FAIL arcosh wire ${source} exact unverified`);
        continue;
      }
      const paths = [
        ["app", evaluateReport(node).value, exactToFloat(appExact.value)],
        ["wire", evaluateReport(wired.node).value, exactToFloat(wired.report.value)],
      ] as const;
      for (const [path, floated, exact] of paths) {
        if (!matches(floated, exact)) {
          ctx.fail(
            `FAIL arcosh ${path} ${source} float=${floated.re}+${floated.im}i exact=${exact.re}+${exact.im}i`,
          );
        }
      }
    }
  },
};

export default checkModule;
