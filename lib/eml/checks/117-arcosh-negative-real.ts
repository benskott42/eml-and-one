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
 * A tiny imaginary part keeps its own sign, including one that underflows to
 * −0. arcosh(−∞) is not certified as undefined.
 */
const probes = ["-1e6", "-3", "-1", "-0.5", "-1e-9", "-0"];
const signed = [
  "arcosh(-3-exp(-800)*i)",
  "arcosh(-7.5-exp(-800)*i)",
  "arcosh(-3+1e-17*i)",
  "arcosh(-30-1e-17*i)",
];

function matches(got: { re: number; im: number }, want: { re: number; im: number }): boolean {
  const scale = Math.max(1, Math.hypot(want.re, want.im));
  if (Math.abs(got.re - want.re) > 1e-8 * scale || Math.abs(got.im - want.im) > 1e-8 * scale) return false;
  return !(got.im < 0 || Object.is(got.im, -0));
}

function agrees(got: { re: number; im: number }, want: { re: number; im: number }): boolean {
  const scale = Math.max(1, Math.hypot(want.re, want.im));
  if (!Number.isFinite(got.re) || !Number.isFinite(got.im)) return false;
  if (Math.abs(got.re - want.re) > 1e-8 * scale || Math.abs(got.im - want.im) > 1e-8 * scale) return false;
  if (want.im < 0) return got.im < 0;
  if (want.im > 0) return got.im > 0;
  return true;
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
    for (const source of signed) {
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
        ["app", evaluateReport(node), exactToFloat(appExact.value)],
        ["wire", evaluateReport(wired.node), exactToFloat(wired.report.value)],
      ] as const;
      for (const [path, report, exact] of paths) {
        if (report.unverified || !agrees(report.value, exact)) {
          const floated = report.value;
          ctx.fail(
            `FAIL arcosh ${path} ${source} float=${report.unverified ? "unverified" : `${floated.re}+${floated.im}i`} exact=${exact.re}+${exact.im}i`,
          );
        }
      }
    }
    {
      const source = "arcosh(-inf)";
      const node = compileExpression(source, {});
      const packed = packCircuit(node);
      const wired = reportUnpacked(packed.tokens, packed.root);
      const rows = [
        ["app float", evaluateReport(node).unverified],
        ["app exact", exactReport(node).unverified],
        ["wire float", evaluateReport(wired.node).unverified],
        ["wire exact", exactReport(wired.node).unverified],
      ] as const;
      for (const [path, unverified] of rows) {
        if (!unverified) ctx.fail(`FAIL arcosh ${path} ${source} certified undefined`);
      }
    }
  },
};

export default checkModule;
