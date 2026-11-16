/**
 * Evaluate packed circuits in a process that never built them.
 * The range table is empty here, so a value that exact mode needs has to arrive on the wire.
 */
import { readFileSync } from "node:fs";
import { exactClose, exactReport, formatExact } from "../lib/eml/exact";
import { unpackCircuit, type Wire } from "../lib/eml/wire";

type Job = {
  source: string;
  tokens: Wire[];
  root: number;
  re?: string;
  im?: string;
  digits?: number;
};

const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
const out = jobs.map((job) => {
  const node = unpackCircuit(job.tokens, job.root);
  const report = exactReport(node, {}, { maxNodes: 400_000 });
  const row: { source: string; text: string; unverified: boolean; singular: string | null; close?: boolean } = {
    source: job.source,
    text: formatExact(report.value),
    unverified: report.unverified === true,
    singular: report.singular,
  };
  if (job.re !== undefined) row.close = exactClose(report.value, job.re, job.im ?? "0", job.digits ?? 40);
  return row;
});
process.stdout.write(`${JSON.stringify(out)}\n`);
