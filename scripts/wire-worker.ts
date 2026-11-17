// v1.1 (reviewbot 04:47): the browser worker path without a browser. The page posts the packed
// wire with postMessage (structured clone) and the worker posts the value back the same way.
// node:worker_threads uses the same structured clone. Input on stdin: [{ src, tokens, root }].
// Output: one JSON line per row; numbers go through wireNum so −0 and ±∞ survive the stdout JSON.
import { readFileSync } from "node:fs";
import { Worker, isMainThread, parentPort } from "node:worker_threads";
import { fileURLToPath } from "node:url";
import { unpackCircuit, wireNum, type Wire } from "../lib/eml/wire";
import { evaluateReport } from "../lib/eml/node";
import { exactReport, formatExact } from "../lib/eml/exact";

type Job = { src: string; tokens: Wire[]; root: number };

if (isMainThread) {
  const jobs = JSON.parse(readFileSync(0, "utf8")) as Job[];
  const worker = new Worker(fileURLToPath(import.meta.url));
  const out: unknown[] = [];
  worker.on("message", (msg: { src: string; leafRe: number | null; leafIm: number | null; re: number; im: number; text: string; unverified: boolean }) => {
    out.push({ ...msg, leafRe: msg.leafRe === null ? null : wireNum(msg.leafRe), leafIm: msg.leafIm === null ? null : wireNum(msg.leafIm), re: wireNum(msg.re), im: wireNum(msg.im) });
    if (out.length === jobs.length) {
      process.stdout.write(`${JSON.stringify(out)}\n`);
      void worker.terminate();
    }
  });
  worker.on("error", (e) => { console.error(e); process.exit(1); });
  // Structured clone, as postMessage does in the browser. Numbers are posted as wireNum gives them.
  for (const job of jobs) worker.postMessage(job);
} else {
  parentPort!.on("message", (job: Job) => {
    const node = unpackCircuit(job.tokens, job.root);
    const leaf = node.type === "input" ? node.value : null;
    const f = evaluateReport(node, {}, { maxNodes: 200_000 });
    const x = exactReport(unpackCircuit(job.tokens, job.root), {}, { maxNodes: 80_000 });
    parentPort!.postMessage({ src: job.src, leafRe: leaf ? leaf.re : null, leafIm: leaf ? leaf.im : null, re: f.value.re, im: f.value.im, text: formatExact(x.value).replace(/\u200b/g, ""), unverified: x.unverified === true });
  });
}
