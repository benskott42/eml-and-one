import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { exactClose, exactParts, exactReport, formatExact, type ExactReport } from "../exact";
import { tAdd, tExp, tMul, tNeg, tSub } from "../library";
import { E, ONE, V, isolateCircuit, nodeFromRpn, SINGULAR_LN0 } from "../node";
import { reportUnpacked } from "../packed-eval";
import { compileExpression } from "../parse";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Three pure words the 120-digit pass and a raw mpmath run disagree on.
 * `11111EE1E1E1EE1E11EEE` is exp(exp(e−1)), about 263.734133269523. The pass snapped
 * exp(e − exp(exp(e−1))) − 1, about 10^(−114), to 0 and then took ln 0.
 * `1111E11E11E1EE1EE1EEE` is +∞: e − ln(exp(e)) is an exact 0, and a finite mpmath
 * value there is the log of rounding noise. `1111E1EEE111E1E1EEE1E` is −∞ on the
 * lower cut: exp(+∞ + iπ) points along the negative real axis.
 *
 * The 60-word family and the flip word are e − ln(a − ln(exp a)). That difference
 * is an exact 0, so the value is +∞. A certified finite there is the log of a
 * rounding residue. The enclosure failing to open is not a counterexample: the
 * identity is already ln 0. Two agreeing precisions are not a proof.
 *
 * zw/zw2 cancel by only a few digits. The enclosure, not the size of that gap,
 * is what proves the result is +∞. `1111E1111EE1EEEE11EEE` and
 * `1111E1EE11111EE1EEEEE` are the same kind of identity. ln(exp(10^(−n)) − 1)
 * is a finite the enclosure pins once the radius is smaller than the value.
 */
const WORDS: { word: string; text: string; re: string; ln0: boolean }[] = [
  { word: "11111EE1E1E1EE1E11EEE", text: "263.734133269523", re: "263.73413326952317463", ln0: false },
  { word: "1111E11E11E1EE1EE1EEE", text: "∞", re: "Infinity", ln0: true },
  { word: "1111E1EEE111E1E1EEE1E", text: "−∞", re: "-Infinity", ln0: true },
];

const probeDir = path.join(path.dirname(fileURLToPath(import.meta.url)), "snap-probes");

function probeWords(name: string): string[] {
  return readFileSync(path.join(probeDir, name), "utf8")
    .split("\n")
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
}

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

function certifiedFinite(report: ExactReport): boolean {
  return report.unverified !== true && report.value.re.isFinite() && report.value.im.isFinite();
}

function provedPlusInfinity(report: ExactReport): boolean {
  const text = formatExact(report.value).replace(/\u200b/g, "");
  return report.unverified !== true && text === "∞" && report.touchedLn0 === true && report.singular === SINGULAR_LN0;
}

const TINY_G: { source: string; re: string }[] = [
  { source: "ln(exp(1e-150) - 1)", re: "-345.3877639491068526026987" },
  { source: "ln(exp(1e-400) - 1)", re: "-921.0340371976182736071966" },
  { source: "e - ln(exp(1e-150) - 1)", re: "348.106045777565897838059005674" },
  { source: "e - ln(exp(1e-400) - 1)", re: "923.752319026077318842556869345" },
];

function bothPaths(word: string): { app: ExactReport; wire: ExactReport } {
  const app = isolateCircuit(() => exactReport(nodeFromRpn(word.split(""))));
  const wire = isolateCircuit(() => {
    const packed = packCircuit(nodeFromRpn(word.split("")));
    return reportUnpacked(packed.tokens, packed.root).report;
  });
  return { app, wire };
}

function bothExpr(source: string): { app: ExactReport; wire: ExactReport } {
  const app = isolateCircuit(() => exactReport(compileExpression(source, {})));
  const wire = isolateCircuit(() => {
    const packed = packCircuit(compileExpression(source, {}));
    return reportUnpacked(packed.tokens, packed.root).report;
  });
  return { app, wire };
}

/** N4: e − ln(exp(g) exp(−g(1+h)) − 1) at g = 10^(−20), h = 10^(−10). The residue is not 0. */
function breakN4(): { app: ExactReport; wire: ExactReport } {
  const env = { g: exactParts("1e-20", "0"), h: exactParts("1e-10", "0") };
  const build = () => E(ONE, tSub(tMul(tExp(V("g")), tExp(tNeg(tMul(V("g"), tAdd(ONE, V("h")))))), ONE));
  const app = isolateCircuit(() => exactReport(build(), env));
  const wire = isolateCircuit(() => {
    const packed = packCircuit(build());
    return reportUnpacked(packed.tokens, packed.root, 80_000, env).report;
  });
  return { app, wire };
}

/** Real e − ln(x − ln(exp x)). The complex 1e−110 i forms are the separate dust hole. */
function realExactZero(source: string): boolean {
  return source.startsWith("e - ln(") && !source.startsWith("e - ln(exp(") && !source.includes("*i");
}

const checkModule: CheckModule = {
  id: 117,
  weight: 22000,
  run(ctx) {
    for (const row of WORDS) {
      const { app, wire } = bothPaths(row.word);
      if (!matches(app, row) || !matches(wire, row)) {
        const show = (report: ExactReport) =>
          `${formatExact(report.value)} ln0=${report.touchedLn0 === true} ${report.singular ?? ""} unverified=${report.unverified === true}`;
        ctx.fail("FAIL pure word", row.word, "app", show(app), "wire", show(wire), "want", row.text);
      }
    }
    const family = [...probeWords("wz.txt"), ...probeWords("flip.txt")];
    if (family.length !== 61) ctx.fail("FAIL family size", family.length);
    const identities = [
      ...family,
      ...probeWords("w10new.txt"),
      ...probeWords("zw.txt"),
      ...probeWords("zw2.txt"),
    ];
    if (probeWords("w10new.txt").length !== 2) ctx.fail("FAIL identity size");
    if (probeWords("zw.txt").length !== 3 || probeWords("zw2.txt").length !== 36) ctx.fail("FAIL zw size");
    for (const word of identities) {
      const { app, wire } = bothPaths(word);
      for (const [name, report] of [
        ["app", app],
        ["wire", wire],
      ] as const) {
        if (!provedPlusInfinity(report)) {
          ctx.fail(
            "FAIL proved infinity",
            name,
            formatExact(report.value),
            report.singular ?? "",
            `unverified=${report.unverified === true}`,
            word.slice(0, 32),
          );
        }
      }
    }
    for (const row of TINY_G) {
      const { app, wire } = bothExpr(row.source);
      for (const [name, report] of [
        ["app", app],
        ["wire", wire],
      ] as const) {
        if (report.unverified === true || report.singular !== null || !exactClose(report.value, row.re, 0, 12)) {
          ctx.fail("FAIL tiny G", name, row.source, formatExact(report.value), `unverified=${report.unverified === true}`);
        }
      }
    }
    const n4 = breakN4();
    for (const [name, report] of [
      ["app", n4.app],
      ["wire", n4.wire],
    ] as const) {
      if (
        report.unverified === true ||
        report.singular !== null ||
        !exactClose(report.value, "71.79583461828041575590003", "3.14159265358979323846", 12)
      ) {
        ctx.fail("FAIL break N4", name, formatExact(report.value), `unverified=${report.unverified === true}`);
      }
    }
    const exactZero = probeWords("expr1.txt").filter(realExactZero);
    if (exactZero.length !== 42) ctx.fail("FAIL expr1 size", exactZero.length);
    for (const source of exactZero) {
      const { app, wire } = bothExpr(source);
      for (const [name, report] of [
        ["app", app],
        ["wire", wire],
      ] as const) {
        if (certifiedFinite(report)) ctx.fail("FAIL expr finite", name, formatExact(report.value), source.slice(0, 48));
      }
    }
  },
};

export default checkModule;
