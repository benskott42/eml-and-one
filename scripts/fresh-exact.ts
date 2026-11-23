/**
 * Evaluate packed circuits in a process that never built them.
 * The range table is empty here, so a value that exact mode needs has to arrive on the wire.
 */
import { readFileSync } from "node:fs";
import { exactClose, exactReport, formatExact } from "../lib/eml/exact";
import { nodeFromRpn } from "../lib/eml/node";
import { unpackCircuit, type Wire } from "../lib/eml/wire";

type Job = {
  source: string;
  tokens?: Wire[];
  root?: number;
  /** A word of 1, x, y and E, built here with no lowering notes. */
  word?: string[];
  /** Variable values, as the worker receives them. */
  env?: Record<string, { re: number; im: number }>;
  /** Evaluate the same node a second time and report that text too. */
  again?: true;
  re?: string;
  im?: string;
  digits?: number;
};

const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
const out = jobs.map((job) => {
  const started = performance.now();
  const node = job.word ? nodeFromRpn(job.word) : unpackCircuit(job.tokens ?? [], job.root ?? 0);
  const report = exactReport(node, job.env ?? {}, { maxNodes: 400_000 });
  const row: { source: string; text: string; unverified: boolean; singular: string | null; close?: boolean; ms: number; again?: string; againSingular?: string | null } = {
    source: job.source,
    text: formatExact(report.value),
    unverified: report.unverified === true,
    singular: report.singular,
    ms: Math.round(performance.now() - started),
  };
  if (job.again) {
    const second = exactReport(node, job.env ?? {}, { maxNodes: 400_000 });
    row.again = second.unverified ? "unverified" : formatExact(second.value);
    row.againSingular = second.singular;
  }
  if (job.re !== undefined) row.close = exactClose(report.value, job.re, job.im ?? "0", job.digits ?? 40);
  return row;
});
process.stdout.write(`${JSON.stringify(out)}\n`);
