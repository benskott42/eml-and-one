/**
 * Evaluate packed circuits in a process that never built them.
 * The range table is empty here, so a tiny known value has to arrive on the wire.
 */
import { readFileSync } from "node:fs";
import { exactReport, formatExact } from "../lib/eml/exact";
import { unpackCircuit, type Wire } from "../lib/eml/wire";

type Job = { source: string; tokens: Wire[]; root: number };

const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
const out = jobs.map((job) => {
  const node = unpackCircuit(job.tokens, job.root);
  const report = exactReport(node, {}, { maxNodes: 80_000 });
  return { source: job.source, text: formatExact(report.value), unverified: report.unverified === true };
});
process.stdout.write(`${JSON.stringify(out)}\n`);
