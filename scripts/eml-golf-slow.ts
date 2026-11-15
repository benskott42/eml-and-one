/**
 * The K=35 constant search. One worker thread runs the enumeration; it is not
 * a parallel split of the pool. `npm run eml:check` stays on the fast search.
 */
import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import Decimal from "decimal.js";
import { nodeFromCompact } from "../lib/eml/programs";
import { exactClose, exactEvaluate } from "../lib/eml/exact";
import { acceptsConstantProgram, searchConstants, type GolfHit } from "../lib/eml/golf";
import { evaluateReport } from "../lib/eml/node";

Decimal.set({ precision: 50 });
const pi = new Decimal(-1).acos().toFixed(40);
const e40 = new Decimal(1).exp().toFixed(40);

const wanted: Record<string, number> = {
  e: 3,
  "0": 7,
  "-1": 15,
  "2": 19,
  ipi: 21,
  "-2": 25,
  "3": 29,
  "1/2": 29,
  "-1/2": 29,
  "-3": 35,
};

const precise: Record<string, { re: string; im: string }> = {
  e: { re: e40, im: "0" },
  "0": { re: "0", im: "0" },
  "-1": { re: "-1", im: "0" },
  "2": { re: "2", im: "0" },
  ipi: { re: "0", im: pi },
  "-2": { re: "-2", im: "0" },
  "3": { re: "3", im: "0" },
  "1/2": { re: "0.5", im: "0" },
  "-1/2": { re: "-0.5", im: "0" },
  "-3": { re: "-3", im: "0" },
};

if (!isMainThread) {
  const maxK = (workerData as { maxK: number }).maxK;
  parentPort?.postMessage({
    withInf: searchConstants(maxK).hits,
    noInf: searchConstants(maxK, { allowLn0: false }).hits,
  });
} else {
  const worker = new Worker(new URL(import.meta.url), { workerData: { maxK: 35 } });
  worker.on("message", (tables: { withInf: GolfHit[]; noInf: GolfHit[] }) => {
    let failed = 0;
    const hits = tables.withInf;
    for (const [id, k] of Object.entries(wanted)) {
      const hit = hits.find((item) => item.id === id);
      if (!hit || hit.k !== k) {
        failed += 1;
        console.log("FAIL", id, hit, "want", k);
        continue;
      }
      const target = precise[id];
      if (!target) continue;
      const value = exactEvaluate(nodeFromCompact(hit.rpn));
      if (!exactClose(value, target.re, target.im, 30)) {
        failed += 1;
        console.log("FAIL 30 digits", id, hit.k, hit.branch);
      } else {
        const name = id === "ipi" ? "+iπ" : id === "-ipi" ? "−iπ" : id;
        console.log(`${name} K=${hit.k} ${hit.branch} ${hit.domain}${hit.usesLn0 ? " uses ln 0" : ""}`);
      }
    }
    const impostor = "11111111E1E1EEEEEE111EEE1E11E1E1EEE";
    if (hits.some((hit) => hit.rpn === impostor) || acceptsConstantProgram(nodeFromCompact(impostor), 0, -Math.PI)) {
      failed += 1;
      console.log("FAIL K35 −iπ impostor stayed in the table");
    }
    for (const hit of tables.noInf) {
      const report = evaluateReport(nodeFromCompact(hit.rpn));
      if (report.overflowed || report.underflowed) {
        failed += 1;
        console.log("FAIL no-inf range impostor", hit.id, hit.k, hit.rpn, report.overflowed, report.underflowed);
      }
    }
    const noInfMinus = tables.noInf.find((hit) => hit.id === "-1");
    if (noInfMinus && noInfMinus.k !== 17) {
      failed += 1;
      console.log("FAIL no-inf −1", noInfMinus);
    }
    for (const id of ["-1", "1/2", "ipi"]) {
      const hit = hits.find((item) => item.id === id);
      if (!hit?.usesLn0 || hit.singular) {
        failed += 1;
        console.log("FAIL ln 0 should cancel", id, hit);
      }
      const clean = tables.noInf.find((item) => item.id === id);
      if (clean?.usesLn0) {
        failed += 1;
        console.log("FAIL no-inf table kept a ln 0 program", id);
      }
    }
    const cleanPi = tables.noInf.find((item) => item.id === "ipi");
    if (!cleanPi || cleanPi.k !== 23) {
      failed += 1;
      console.log("FAIL no-inf +iπ", cleanPi);
    }
    const cleanNeg = tables.noInf.find((item) => item.id === "-ipi");
    if (cleanNeg && cleanNeg.k <= 29) {
      failed += 1;
      console.log("FAIL no-inf −iπ with K ≤ 29", cleanNeg);
    }
    const infNeg = tables.withInf.find((item) => item.id === "-ipi");
    if (infNeg && infNeg.k <= 29) {
      failed += 1;
      console.log("FAIL −iπ with K ≤ 29", infNeg);
    }
    const cleanHalf = tables.noInf.find((item) => item.id === "1/2");
    if (!cleanHalf || cleanHalf.k !== 31) {
      failed += 1;
      console.log("FAIL no-inf 1/2", cleanHalf);
    }
    const negHalf = tables.noInf.find((item) => item.rpn === "1111111EEE1EE11E1EEE11E1E1EEE1E");
    if (!negHalf || negHalf.k !== 31 || negHalf.usesLn0) {
      failed += 1;
      console.log("FAIL no-inf −1/2 record", negHalf);
    }
    if (failed) {
      console.log(`${failed} failed`);
      process.exit(1);
    }
    console.log("golf K=35 passed");
  });
  worker.on("error", (err) => {
    console.error(err);
    process.exit(1);
  });
}
