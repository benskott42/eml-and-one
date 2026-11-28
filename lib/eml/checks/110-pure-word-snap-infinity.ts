import { exactClose, exactReport, formatExact, type ExactReport } from "../exact";
import { isolateCircuit, nodeFromRpn, SINGULAR_LN0 } from "../node";
import { reportUnpacked } from "../packed-eval";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Three pure words the 120-digit pass and a raw mpmath run disagree on.
 * `11111EE1E1E1EE1E11EEE` is exp(exp(e−1)), about 263.734133269523. The pass snapped
 * exp(e − exp(exp(e−1))) − 1, about 10^(−114), to 0 and then took ln 0.
 * `1111E11E11E1EE1EE1EEE` is +∞: e − ln(exp(e)) is an exact 0, and a finite mpmath
 * value there is the log of rounding noise. `1111E1EEE111E1E1EEE1E` is −∞ on the
 * lower cut: exp(+∞ + iπ) points along the negative real axis.
 */
const WORDS: { word: string; text: string; re: string; ln0: boolean }[] = [
  { word: "11111EE1E1E1EE1E11EEE", text: "263.734133269523", re: "263.73413326952317463", ln0: false },
  { word: "1111E11E11E1EE1EE1EEE", text: "∞", re: "Infinity", ln0: true },
  { word: "1111E1EEE111E1E1EEE1E", text: "−∞", re: "-Infinity", ln0: true },
];

function matches(report: ExactReport, row: (typeof WORDS)[number]): boolean {
  const text = formatExact(report.value).replace(/\u200b/g, "");
  const logged = report.touchedLn0 === true && report.singular === SINGULAR_LN0;
  return (
    !report.unverified &&
    text === row.text &&
    report.value.im.isZero() &&
    !report.value.im.isNeg() &&
    (row.ln0 ? logged : report.singular === null && report.touchedLn0 === false) &&
    exactClose(report.value, row.re, 0, 20)
  );
}

const checkModule: CheckModule = {
  id: 110,
  weight: 400,
  run(ctx) {
    for (const row of WORDS) {
      const app = isolateCircuit(() => exactReport(nodeFromRpn(row.word.split(""))));
      const wire = isolateCircuit(() => {
        const packed = packCircuit(nodeFromRpn(row.word.split("")));
        return reportUnpacked(packed.tokens, packed.root).report;
      });
      if (!matches(app, row) || !matches(wire, row)) {
        const show = (report: ExactReport) =>
          `${formatExact(report.value)} ln0=${report.touchedLn0 === true} ${report.singular ?? ""} unverified=${report.unverified === true}`;
        ctx.fail("FAIL pure word", row.word, "app", show(app), "wire", show(wire), "want", row.text);
      }
    }
  },
};

export default checkModule;
