/**
 * One fresh process, one expression.
 * The parent packs the circuit and sends it with v8.serialize (signed zero
 * and NaN survive; JSON would not). This process unpacks through the same
 * path as the exact worker, evaluates twice, and writes both screens back.
 */
import { deserialize, serialize } from "node:v8";
import { reportNode, reportUnpacked, WORKER_NODE_BUDGET } from "../lib/eml/packed-eval";
import { screenOf, type Screen } from "../lib/eml/golden/screen";
import type { Wire } from "../lib/eml/wire";

type Job = { tokens: Wire[]; root: number };

const chunks: Buffer[] = [];
process.stdin.on("data", (chunk: Buffer) => {
  chunks.push(chunk);
});
process.stdin.on("end", () => {
  try {
    const job = deserialize(Buffer.concat(chunks)) as Job;
    const { node, report } = reportUnpacked(job.tokens, job.root, WORKER_NODE_BUDGET);
    const first: Screen = screenOf(node, report, WORKER_NODE_BUDGET);
    const again = reportNode(node, WORKER_NODE_BUDGET);
    const second: Screen = screenOf(node, again, WORKER_NODE_BUDGET);
    process.stdout.write(serialize({ first, second }));
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    process.stderr.write(`${message}\n`);
    process.exit(1);
  }
});
