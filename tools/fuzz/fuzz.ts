/**
 * EML engine fuzzer: evaluates deterministic random expression sets both
 * in-process and through the worker wire (packCircuit -> unpackCircuit),
 * checking wire parity and recording certified/refused/singular counts.
 *
 * Usage:
 *   npx tsx tools/fuzz/fuzz.ts [--count 500] [--seed 1] [--max-nodes 80000] [--json out.json]
 */
import { writeFileSync } from "node:fs";
import { exactReport, formatExact } from "../../lib/eml/exact";
import { isolateCircuit } from "../../lib/eml/node";
import { compileExpression } from "../../lib/eml/parse";
import { packCircuit, unpackCircuit } from "../../lib/eml/wire";
import { generateFuzzCases } from "./generate";

type FuzzRow = {
  category: string;
  source: string;
  status: "certified" | "unverified" | "singular" | "error";
  exact?: string;
  re?: string;
  im?: string;
  singular?: string | null;
  wireStatus?: string;
  wireExact?: string;
  wireMismatch?: boolean;
};

function parseFlags(argv: string[]) {
  let count = 500;
  let seed = 1;
  let maxNodes = 80_000;
  let timeoutMs = 10_000;
  let jsonOut = "";
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--count" && argv[i + 1]) count = Number(argv[++i]);
    else if (arg === "--seed" && argv[i + 1]) seed = Number(argv[++i]);
    else if (arg === "--max-nodes" && argv[i + 1]) maxNodes = Number(argv[++i]);
    else if (arg === "--timeout-ms" && argv[i + 1]) timeoutMs = Number(argv[++i]);
    else if (arg === "--json" && argv[i + 1]) jsonOut = argv[++i] ?? "";
  }
  return { count, seed, maxNodes, timeoutMs, jsonOut };
}

function summarizeReport(report: ReturnType<typeof exactReport>) {
  if (report.unverified) return { status: "unverified" as const, exact: "—" };
  const exact = formatExact(report.value).replace(/\u200b/g, "");
  if (report.singular !== null) return { status: "singular" as const, exact, singular: report.singular };
  return { status: "certified" as const, exact };
}

const { count, seed, maxNodes, timeoutMs, jsonOut } = parseFlags(process.argv.slice(2));
const cases = generateFuzzCases(count, seed);
const rows: FuzzRow[] = [];

let certified = 0;
let unverified = 0;
let singular = 0;
let errors = 0;
let wireMismatches = 0;

const t0 = performance.now();

for (const item of cases) {
  try {
    const node = compileExpression(item.source, {});
    const directRep = exactReport(node, {}, { maxNodes, deadline: performance.now() + timeoutMs });
    const direct = summarizeReport(directRep);

    const packed = packCircuit(node);
    const wireRep = isolateCircuit(() => {
      const unpacked = unpackCircuit(packed.tokens, packed.root);
      return exactReport(unpacked, {}, { maxNodes, deadline: performance.now() + timeoutMs });
    });
    const wire = summarizeReport(wireRep);

    const mismatch = direct.status !== wire.status || direct.exact !== wire.exact;
    if (mismatch) wireMismatches += 1;

    if (direct.status === "certified") certified += 1;
    else if (direct.status === "unverified") unverified += 1;
    else singular += 1;

    rows.push({
      category: item.category,
      source: item.source,
      status: direct.status,
      exact: direct.exact,
      ...(direct.status === "certified" && directRep.value.re.isFinite() && directRep.value.im.isFinite()
        ? { re: directRep.value.re.toSignificantDigits(30).toString(), im: directRep.value.im.toSignificantDigits(30).toString() }
        : {}),
      ...(directRep.singular ? { singular: directRep.singular } : {}),
      ...(mismatch ? { wireStatus: wire.status, wireExact: wire.exact, wireMismatch: true } : {}),
    });
  } catch {
    errors += 1;
    rows.push({ category: item.category, source: item.source, status: "error" });
  }
}

const elapsedMs = Math.round(performance.now() - t0);
console.log(
  `fuzz seed=${seed} count=${cases.length} (${elapsedMs}ms): certified=${certified} unverified=${unverified} singular=${singular} errors=${errors} wireMismatches=${wireMismatches}`,
);

if (wireMismatches > 0) {
  for (const row of rows.filter((r) => r.wireMismatch)) {
    console.error(`WIRE MISMATCH ${row.source}: direct=${row.status}(${row.exact}) wire=${row.wireStatus}(${row.wireExact})`);
  }
}

if (jsonOut) {
  writeFileSync(
    jsonOut,
    `${JSON.stringify({ seed, count: cases.length, elapsedMs, certified, unverified, singular, errors, wireMismatches, rows }, null, 2)}\n`,
    "utf8",
  );
}

process.exit(wireMismatches > 0 ? 1 : 0);
