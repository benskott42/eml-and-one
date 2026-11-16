// Exact worker emulation for check.ts (overnight findings): never compiles; unpacks the
// posted wire and evaluates it twice (the 2nd is a repeat compute on a warm pureCache).
import { readFileSync } from "node:fs";
import { unpackCircuit } from "../lib/eml/wire";
import { exactReport, formatExact } from "../lib/eml/exact";
import { evaluateReport } from "../lib/eml/node";
const job = JSON.parse(readFileSync(process.argv[2], "utf8")) as { items: { tokens: unknown[]; root: number; env: Record<string, { re: number; im: number }> }[] };
const out: unknown[] = [];
for (const it of job.items) {
  const runs: unknown[] = [];
  for (let pass = 0; pass < 2; pass++) {
    const t0 = Date.now();
    try {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const r = exactReport(unpackCircuit(it.tokens as any, it.root), it.env ?? {}, { maxNodes: 80_000 }) as any;
      // Float mode on the same fresh circuit (v1.1: ln 0 folds are checked in both modes).
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const f = evaluateReport(unpackCircuit(it.tokens as any, it.root), it.env ?? {}, { maxNodes: 200_000 });
      runs.push({ text: formatExact(r.value), unverified: r.unverified === true, notCertified: r.notCertified ? true : false, singular: r.singular ?? null, floatRe: f.value.re, floatIm: f.value.im, floatSingular: f.singular, ms: Date.now() - t0 });
    } catch (e) {
      runs.push({ error: (e as Error).message, ms: Date.now() - t0 });
    }
  }
  out.push(runs);
}
console.log(JSON.stringify(out));
