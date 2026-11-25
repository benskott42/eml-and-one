import { packCircuit, unpackCircuit } from "../wire";
import { agreementNote, compileExpression } from "../parse";
import { exactReport, formatExact } from "../exact";
import type { CheckModule } from "./_types";
import { evaluate, evaluateReport } from "../node";
import { provenInteger } from "../facts";
import { knownValue } from "../lowering";
import { runTsx } from "./_helpers";

/**
 * Float underflow preservation, tiny-term cancellations, and fresh-child wire verification.
 */
// Identities that are exactly 0. A rounding residue, including one that
// holds still while the precision climbs, must come out 0 or unverified.
// A nearby difference, and a sum that does not cancel, stays a certified
// value. Both the packed worker and a fresh process.
const tinyCancelRows = [
  "exp(ln(1e-400))-1e-400",
  "1e-400*1.5/1.5-1e-400",
  "(1e-400)/2*2-(1e-400)",
  "1e-400/0.5/2-1e-400",
  "1e-400*(2^0.5)^2-2e-400",
  "1e-450*e/e-1e-450",
  "1e-500*e/e-1e-500",
  "1e-600*e/e-1e-600",
  "1e-200*(2^0.5)^2-2*1e-200",
  "1e-100*1.5/1.5-1e-100",
  "1e-50*1.5/1.5-1e-50",
  "1e-150*1.5/1.5-1e-150",
  "1e-320*pi/pi-1e-320",
  "1e-320*e/e-1e-320",
  "1e-320*3/3-1e-320",
  "exp(ln(1e-320))-1e-320",
  "1e-318*pi/pi-1e-318",
];
const tinyKeptRows: Array<[string, string]> = [
  ["1e-400-1e-400*(1+1e-50)", "−1×10^−450"],
  ["(1e-400)*3/3-(1e-400)*(1+1e-50)", "−1×10^−450"],
  ["1e-400*(1+1e-100)-1e-400", "1×10^−500"],
  ["1e-400*pi+1e-400", "4.14159265359×10^−400"],
  ["exp(-1000)-exp(-1001)", "3.20861797491×10^−435"],
];
function packedTinyReport(source: string) {
  const packed = packCircuit(compileExpression(source, {}));
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 400_000 });
}
const tinyShownText = (report: ReturnType<typeof exactReport>) => formatExact(report.value).replace(/\u200b/g, "");
function honestZero(report: ReturnType<typeof exactReport>) {
  if (report.unverified) return true;
  const text = tinyShownText(report);
  return text === "0" || text === "−0";
}

const checks: CheckModule[] = [
  {
    id: 50,
    weight: 28440,
    run(ctx) {
      // A float underflow is not the integer 0. Negation, sine, and 0 − b keep the tiny term.
      const tinyRows: Array<[string, string]> = [
        ["-10^(-400)", "−1×10^−400"],
        ["-exp(-1000)", "−5.075958897549×10^−435"],
        ["sin(-10^(-400))", "−1×10^−400"],
        ["(0-1)*10^(-400)", "−1×10^−400"],
        ["-(2*exp(-1000))", "−1.01519177951×10^−434"],
        ["0-10^(-400)", "−1×10^−400"],
        ["0-exp(-1000)", "−5.075958897549×10^−435"],
        ["0-exp(-1000+i)", "−2.742552296838×10^−435 − 4.271272132365×10^−435i"],
        ["0-(2*exp(-1000))", "−1.01519177951×10^−434"],
        ["0+exp(-1000)", "5.075958897549×10^−435"],
        ["-10^(-500)", "−1×10^−500"],
        ["0-1/10^400", "−1×10^−400"],
        ["0-1/10^433", "−1×10^−433"],
        ["0-(exp(-1000)/3)", "−1.691986299183×10^−435"],
        ["(1+10^-500)-1", "1×10^−500"],
        ["10^-500+1-1", "1×10^−500"],
        ["exp(-1000)+exp(-1000)", "1.01519177951×10^−434"],
        ["-(exp(-1000)+exp(-1000))", "−1.01519177951×10^−434"],
        ["ln(1+1/10^400)", "1×10^−400"],
        ["0-ln(1+10^(-400))", "−1×10^−400"],
        ["ln(1-10^(-400))", "−1×10^−400"],
        ["ln(1+10^(-400))", "1×10^−400"],
        ["-(10^(-30))", "−1×10^−30"],
        ["10^(-30)", "1×10^−30"],
        ["-10^(-130)", "−1×10^−130"],
        ["10^(-130)", "1×10^−130"],
        ["10^(-400)", "1×10^−400"],
        ["-0", "−0"],
      ];
      const tinyNodes = tinyRows.map(([source]) => compileExpression(source, {}));
      for (const [i, [source, want]] of tinyRows.entries()) {
        const report = exactReport(tinyNodes[i], {}, { maxNodes: 400_000 });
        const text = formatExact(report.value).replace(/\u200b/g, "");
        const zero = text === "0" || text === "−0";
        const note = agreementNote(source, evaluateReport(tinyNodes[i], {}, { maxNodes: 400_000 }).value, {}, text);
        const vouched = note === "matches the usual value" && source !== "-0" && source !== "10^(-30)" && source !== "-(10^(-30))" && source !== "10^(-130)" && source !== "-10^(-130)";
        if (report.unverified || text !== want || (zero && source !== "-0") || vouched) {
          ctx.fail("FAIL tiny underflow", source, report.unverified ? "unverified" : text, note);
        } else {
          console.log("tiny", source, text);
        }
      }
      const barePow = compileExpression("10^(-400)", {});
      const bareExp = compileExpression("exp(-1000)", {});
      if (provenInteger(barePow) !== undefined || knownValue(barePow) !== null || knownValue(bareExp) !== null) {
        ctx.fail("FAIL underflow tagged as exact 0", provenInteger(barePow), knownValue(barePow), knownValue(bareExp));
      }
      const signed = evaluate(compileExpression("-0", {}));
      if (!Object.is(signed.re, -0) || signed.im !== 0) {
        ctx.fail("FAIL typed -0", signed);
      }
      // A logarithm the circuit collapses past the cap must not certify 0.
      const lostRows = ["ln(1-10^(-500))", "ln(1+10^(-500))", "ln(1+exp(-1000))", "ln(1-exp(-1000))"];
      // Past-cap 0 − power may print the value or say it could not verify. A confident 0 fails.
      const eitherRows: Array<[string, string]> = [
        ["0-10^(-433)", "−1×10^−433"],
        ["0-10^(-500)", "−1×10^−500"],
      ];
      const eitherNodes = eitherRows.map(([source]) => compileExpression(source, {}));
      for (const [i, [source, want]] of eitherRows.entries()) {
        const report = exactReport(eitherNodes[i], {}, { maxNodes: 400_000 });
        const text = formatExact(report.value).replace(/\u200b/g, "");
        if (report.unverified) console.log("either", source, "couldn't verify");
        else if (text === want) console.log("either", source, text);
        else {
          ctx.fail("FAIL past-cap sub", source, text);
        }
      }
      const lostNodes = lostRows.map((source) => compileExpression(source, {}));
      for (const [i, source] of lostRows.entries()) {
        const report = exactReport(lostNodes[i], {}, { maxNodes: 400_000 });
        const text = formatExact(report.value).replace(/\u200b/g, "");
        const collapsed = text === "0" || text === "−0";
        if (!report.unverified || !collapsed) {
          ctx.fail("FAIL lost tiny", source, report.unverified ? "unverified" : text);
        } else {
          console.log("lost", source, "couldn't verify");
        }
      }
      const foldedPow = exactReport(compileExpression("10^(-500)-10^(-500)", {}), {}, { maxNodes: 400_000 });
      const foldedText = formatExact(foldedPow.value).replace(/\u200b/g, "");
      if (foldedPow.unverified || foldedText !== "0") {
        ctx.fail("FAIL identical past-cap cancel", foldedPow.unverified ? "unverified" : foldedText);
      }
      // Exact zeros. A cap mark must not turn these into "couldn't verify".
      const zeroRows = [
        "0*10^-500",
        "10^-500*0",
        "ln(1)*10^-500",
        "(0-10^-433)+10^-433",
        "(exp(-1000)+exp(-1000))-2*exp(-1000)",
        "(0-10^-500)*0",
      ];
      const zeroNodes = zeroRows.map((source) => compileExpression(source, {}));
      for (const [i, source] of zeroRows.entries()) {
        const report = exactReport(zeroNodes[i], {}, { maxNodes: 400_000 });
        const text = formatExact(report.value).replace(/\u200b/g, "");
        if (report.unverified || text !== "0") {
          ctx.fail("FAIL exact tiny zero", source, report.unverified ? "unverified" : text);
        } else {
          console.log("zero", source, text);
        }
      }
      const tinyJobs = [
        ...tinyRows.flatMap(([source, want], i) => {
          // JSON has no −0, so the typed −0 control stays in this process.
          if (source === "-0") return [];
          const packed = packCircuit(tinyNodes[i]);
          return [{ source, tokens: packed.tokens, root: packed.root, unverified: false, want, either: false }];
        }),
        ...lostRows.map((source, i) => {
          const packed = packCircuit(lostNodes[i]);
          return { source, tokens: packed.tokens, root: packed.root, unverified: true, want: "0", either: false };
        }),
        ...zeroRows.map((source, i) => {
          const packed = packCircuit(zeroNodes[i]);
          return { source, tokens: packed.tokens, root: packed.root, unverified: false, want: "0", either: false };
        }),
        ...eitherRows.map(([source, want], i) => {
          const packed = packCircuit(eitherNodes[i]);
          return { source, tokens: packed.tokens, root: packed.root, unverified: false, want, either: true };
        }),
      ];
      const tinyFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(tinyJobs), 300_000);
      if (tinyFresh.status !== 0) {
        ctx.fail("FAIL fresh tiny underflow", tinyFresh.status, tinyFresh.stderr);
      } else {
        const rows = JSON.parse(tinyFresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
        for (const row of rows) {
          const job = tinyJobs.find((item) => item.source === row.source);
          const text = row.text.replace(/\u200b/g, "");
          if (!job) continue;
          if (job.either) {
            if (row.unverified || text === job.want) continue;
            ctx.fail("FAIL fresh past-cap sub", row.source, text);
          } else if (job.unverified) {
            const collapsed = text === "0" || text === "−0";
            if (!row.unverified || !collapsed) {
              ctx.fail("FAIL fresh lost tiny", row.source, row.unverified ? "unverified" : text);
            }
          } else if (row.unverified || text !== job.want) {
            ctx.fail("FAIL fresh tiny", row.source, row.unverified ? "unverified" : text);
          }
        }
      }
    },
  },
  {
    id: 51,
    weight: 20203,
    run(ctx) {
      for (const source of tinyCancelRows) {
        const report = packedTinyReport(source);
        if (!honestZero(report)) {
          ctx.fail("FAIL certified tiny cancel", source, tinyShownText(report));
        } else {
          console.log("cancel", source, report.unverified ? "couldn't verify" : tinyShownText(report));
        }
      }
    },
  },
  {
    id: 61,
    weight: 9505,
    run(ctx) {
      for (const [source, want] of tinyKeptRows) {
        const report = packedTinyReport(source);
        const text = tinyShownText(report);
        if (report.unverified || text !== want) {
          ctx.fail("FAIL tiny kept value", source, report.unverified ? "unverified" : text);
        } else {
          console.log("kept", source, text);
        }
      }
    },
  },
  {
    id: 62,
    weight: 35495,
    run(ctx) {
      const cancelJobs = [...tinyCancelRows, ...tinyKeptRows.map(([source]) => source)].map((source) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root };
      });
      const cancelFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(cancelJobs), 300_000);
      if (cancelFresh.status !== 0) {
        ctx.fail("FAIL fresh tiny cancel", cancelFresh.status, cancelFresh.stderr?.slice(0, 400));
      } else {
        const rows = JSON.parse(cancelFresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
        rows.forEach((row, index) => {
          const text = row.text.replace(/\u200b/g, "");
          if (index < tinyCancelRows.length) {
            const ok = row.unverified || text === "0" || text === "−0";
            if (!ok) {
              ctx.fail("FAIL fresh certified tiny cancel", row.source, text);
            }
            return;
          }
          const want = tinyKeptRows[index - tinyCancelRows.length]?.[1];
          if (!want || row.unverified || text !== want) {
            ctx.fail("FAIL fresh tiny kept value", row.source, row.unverified ? "unverified" : text, want);
          }
        });
      }
    },
  },
];

export default checks;
