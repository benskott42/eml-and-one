// Cold: a process that never compiled anything. Load each word from presses only.
import { readFileSync } from "node:fs";
import { nodeFromRpn } from "../lib/eml/node";
import { exactReport, formatExact } from "../lib/eml/exact";
import { packCircuit, unpackCircuit } from "../lib/eml/wire";
const words = JSON.parse(readFileSync(process.argv[2] ?? "scripts/e1-words-v10.json", "utf8")) as Record<string, string>;
const res: Record<string, string> = {};
for (const [src, w] of Object.entries(words)) {
  const n = nodeFromRpn(w.split(""));
  const p = packCircuit(n);
  const r = exactReport(unpackCircuit(p.tokens, p.root), {}, { maxNodes: 200_000 });
  res[src] = (r.unverified ? "unverified " : "") + formatExact(r.value) + ((r as { notCertified?: unknown }).notCertified ? " [not certified]" : "");
}
console.log(JSON.stringify(res));
