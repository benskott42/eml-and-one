/**
 * Loaded with EML_NOCACHE=1 already in the environment, so exact.ts reads it
 * at module load. Evaluates each expression twice on the same node.
 */
import { compileExpression } from "../lib/eml/parse";
import { reportNode } from "../lib/eml/packed-eval";
import { formatExact } from "../lib/eml/exact";

function shown(node: ReturnType<typeof compileExpression>): string {
  const report = reportNode(node);
  return report.unverified ? "—" : formatExact(report.value).replace(/\u200b/g, "");
}

let input = "";
process.stdin.on("data", (chunk) => {
  input += chunk.toString();
});
process.stdin.on("end", () => {
  const sources = JSON.parse(input) as string[];
  const rows = sources.map((source) => {
    const node = compileExpression(source, {});
    return { source, first: shown(node), second: shown(node) };
  });
  process.stdout.write(JSON.stringify({ nocache: process.env.EML_NOCACHE ?? "", rows }));
});
