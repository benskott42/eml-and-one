/**
 * Evaluate packed circuits in a process that never built them.
 * A long literal arrives as text on the wire; the float value does not.
 */
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { exactReport, formatExact } from "../lib/eml/exact";
import { exactLiteralOf } from "../lib/eml/node";
import { unpackCircuit, type Wire } from "../lib/eml/wire";

type Job = { id: string; tokens: Wire[]; root: number };

const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
const out = jobs.map((job) => {
  const started = performance.now();
  try {
    const node = unpackCircuit(job.tokens, job.root);
    const report = exactReport(node, {}, { maxNodes: 80_000 });
    const re = report.value.re.isFinite() ? report.value.re.toFixed() : String(report.value.re);
    return {
      id: job.id,
      text: formatExact(report.value),
      re,
      literal: exactLiteralOf(node) ?? null,
      unverified: report.unverified === true,
      ms: performance.now() - started,
    };
  } catch (error) {
    return { id: job.id, error: error instanceof Error ? error.message : String(error), ms: performance.now() - started };
  }
});
process.stdout.write(`${JSON.stringify(out)}\n`);
