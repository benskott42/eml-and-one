/**
 * Evaluate packed circuits in a process that never built them.
 * Started with stdin JSON, or as a worker that receives the same jobs by message.
 */
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { parentPort } from "node:worker_threads";
import { exactReport, formatExact } from "../lib/eml/exact";
import { exactLiteralOf, provenInteger, type Node } from "../lib/eml/node";
import { unpackCircuit, type Wire } from "../lib/eml/wire";

export type Job = { id: string; tokens: Wire[]; root: number };

export type LiteralRow = {
  id: string;
  text?: string;
  re?: string;
  im?: string;
  literal?: string | null;
  intDigits?: string | null;
  unverified?: boolean;
  leaves?: { re: string; im: string; label: string }[];
  ms?: number;
  error?: string;
};

function part(n: number): string {
  if (Object.is(n, -0)) return "-0";
  if (Object.is(n, 0)) return "0";
  if (Number.isNaN(n)) return "NaN";
  if (n === Infinity) return "Infinity";
  if (n === -Infinity) return "-Infinity";
  return String(n);
}

function decPart(n: { isFinite(): boolean; isNaN(): boolean; isNeg(): boolean; isZero(): boolean; toFixed(): string }): string {
  if (n.isNaN()) return "NaN";
  if (!n.isFinite()) return n.isNeg() ? "-Infinity" : "Infinity";
  if (n.isZero() && n.isNeg()) return "-0";
  return n.toFixed();
}

function leavesOf(node: Node): { re: string; im: string; label: string }[] {
  const out: { re: string; im: string; label: string }[] = [];
  const seen = new Set<Node>();
  const stack: Node[] = [node];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    if (n.type === "input") out.push({ re: part(n.value.re), im: part(n.value.im), label: n.label });
    else if (n.type === "eml" && n.a && n.b) stack.push(n.a, n.b);
  }
  return out;
}

export function evaluateJobs(jobs: Job[]): LiteralRow[] {
  return jobs.map((job) => {
    const started = performance.now();
    try {
      const node = unpackCircuit(job.tokens, job.root);
      const report = exactReport(node, {}, { maxNodes: 80_000 });
      const re = decPart(report.value.re);
      const im = decPart(report.value.im);
      return {
        id: job.id,
        text: formatExact(report.value),
        re,
        im,
        literal: exactLiteralOf(node) ?? null,
        intDigits: provenInteger(node)?.toString() ?? null,
        unverified: report.unverified === true,
        leaves: leavesOf(node),
        ms: performance.now() - started,
      };
    } catch (error) {
      return { id: job.id, error: error instanceof Error ? error.message : String(error), ms: performance.now() - started };
    }
  });
}

if (parentPort) {
  parentPort.on("message", (message: { jobs: Job[]; port: import("node:worker_threads").MessagePort; sab: SharedArrayBuffer }) => {
    message.port.postMessage(evaluateJobs(message.jobs));
    const flag = new Int32Array(message.sab);
    Atomics.store(flag, 0, 1);
    Atomics.notify(flag, 0);
  });
} else {
  const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
  process.stdout.write(`${JSON.stringify(evaluateJobs(jobs))}\n`);
}
