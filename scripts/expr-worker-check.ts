import { Worker } from "node:worker_threads";
import { exactClose, exactParts } from "../lib/eml/exact";
import { compilePresses } from "../lib/eml/exprSeq";
import { packCircuit } from "../lib/eml/wire";

const rows = [
  { source: "3+4", presses: 85, re: "7", im: "0" },
  { source: "2*5", presses: 83, re: "10", im: "0" },
  { source: "5-4*i", presses: 501, re: "5", im: "-4" },
  { source: "(6)+(-6)", presses: 7, re: "0", im: "0" },
  { source: "(-4)-(-4)", presses: 7, re: "0", im: "0" },
  { source: "(2^3−1)+(0−7)", presses: 7, re: "0", im: "0" },
  { source: "(−4*1)−(−4)", presses: 7, re: "0", im: "0" },
];

type Reply = {
  type?: string;
  request?: number;
  reDigits?: string;
  imDigits?: string;
  unverified?: boolean;
  singular?: string | null;
  message?: string;
};

async function main(): Promise<void> {
  const execArgv = process.execArgv.length > 0 ? process.execArgv : ["--import", "tsx"];
  const worker = new Worker(new URL("./expr-exact-worker.ts", import.meta.url), { execArgv });
  const fails: string[] = [];
  const pending = new Map<number, (reply: Reply) => void>();
  worker.on("message", (data: Reply) => {
    if (data.type !== "done" && data.type !== "error") return;
    if (data.request === undefined) return;
    const resolve = pending.get(data.request);
    if (!resolve) return;
    pending.delete(data.request);
    resolve(data);
  });
  await new Promise<void>((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error("worker did not start")), 30_000);
    const onReady = (data: Reply) => {
      if (data.type !== "ready") return;
      clearTimeout(timer);
      worker.off("message", onReady);
      resolve();
    };
    worker.on("message", onReady);
  });

  for (let request = 0; request < rows.length; request += 1) {
    const row = rows[request];
    if (!row) continue;
    const seq = compilePresses(row.source);
    if (seq.presses !== row.presses) {
      fails.push(`${row.source} presses ${seq.presses} wanted ${row.presses}`);
      continue;
    }
    const packed = packCircuit(seq.node);
    const reply = await new Promise<Reply>((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error(`${row.source} timed out`)), 90_000);
      pending.set(request, (data) => {
        clearTimeout(timer);
        resolve(data);
      });
      worker.postMessage({ request, tokens: packed.tokens, root: packed.root, env: {} });
    });
    if (reply.type !== "done" || reply.reDigits === undefined || reply.imDigits === undefined) {
      fails.push(`${row.source} ${reply.message ?? "missing 120-digit parts"}`);
      continue;
    }
    const close = exactClose(exactParts(reply.reDigits, reply.imDigits), row.re, row.im, 100);
    if (!close || reply.unverified === true || reply.singular) {
      fails.push(`${row.source} close=${close} unverified=${String(reply.unverified)} singular=${reply.singular ?? "none"}`);
    }
  }
  await worker.terminate();
  if (fails.length > 0) {
    console.log(fails.join("\n"));
    process.exitCode = 1;
    return;
  }
  console.log("expr worker 100 digits ok");
}

void main().catch((err: unknown) => {
  console.log(err instanceof Error ? err.stack ?? err.message : err);
  process.exit(1);
});
