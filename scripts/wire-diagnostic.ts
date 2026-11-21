#!/usr/bin/env tsx
/**
 * Diagnostic for wire bug: compare three evaluation paths
 * (a) direct evaluation of parsed node
 * (b) same-process packCircuit → unpackCircuit → evaluate
 * (c) fresh-process wire (via child process)
 */

import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { compileExpression } from "../lib/eml/parse";
import { exactReport, formatExact } from "../lib/eml/exact";
import { packCircuit, unpackCircuit, type Wire } from "../lib/eml/wire";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const wireChildScript = path.join(repoRoot, "scripts/wire-eval-child.ts");
const tsxCli = path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs");

const testCases = [
  "((1+10^(-130))-1)+i/2",
  "((1+10^(-130))-1)+i*(1+10^(-130))/2",
  "((1+10^(-136))-1)+i*3/2",
];

interface WireJob {
  source: string;
  tokens: Wire[];
  root: number;
}

interface WireResult {
  source: string;
  exactText: string;
  exactNotes: string[];
  floatText: string;
  floatNotes: string[];
  pressCount: string;
  error?: string;
}

console.log("Wire bug diagnostic - 3 evaluation paths:\n");
console.log("Path (a): Direct evaluation (no pack/unpack)");
console.log("Path (b): Same-process round-trip (pack → unpack → evaluate)");
console.log("Path (c): Fresh-process wire (child process)\n");

const jobs: WireJob[] = [];
for (const source of testCases) {
  console.log(`Expression: ${source}`);
  
  // Path (a): Direct evaluation
  try {
    const node = compileExpression(source, {});
    const direct = exactReport(node, {}, { maxNodes: 200_000 });
    const directText = direct.unverified ? "—" : formatExact(direct.value).replace(/\u200b/g, "");
    console.log(`  (a) Direct:      ${directText} ${direct.unverified ? "(unverified)" : "(certified)"}`);
  } catch (err) {
    console.log(`  (a) Direct:      ERROR: ${err}`);
  }
  
  // Path (b): Same-process round-trip
  try {
    const node = compileExpression(source, {});
    const packed = packCircuit(node);
    const unpacked = unpackCircuit(packed.tokens, packed.root);
    const roundTrip = exactReport(unpacked, {}, { maxNodes: 200_000 });
    const rtText = roundTrip.unverified ? "—" : formatExact(roundTrip.value).replace(/\u200b/g, "");
    console.log(`  (b) Same-proc:   ${rtText} ${roundTrip.unverified ? "(unverified)" : "(certified)"}`);
    
    // Prepare for fresh-process
    jobs.push({
      source,
      tokens: packed.tokens,
      root: packed.root,
    });
  } catch (err) {
    console.log(`  (b) Same-proc:   ERROR: ${err}`);
  }
}

// Path (c): Fresh-process wire
console.log("\nRunning fresh-process wire evaluation...\n");
const childResult = spawnSync(
  process.execPath,
  [tsxCli, wireChildScript],
  {
    input: JSON.stringify(jobs),
    encoding: "utf8",
    timeout: 60_000,
  }
);

if (childResult.status !== 0) {
  console.error("Fresh-process wire evaluation failed:", childResult.stderr);
} else {
  try {
    const wireResults: WireResult[] = JSON.parse(childResult.stdout);
    for (const wr of wireResults) {
      console.log(`Expression: ${wr.source}`);
      console.log(`  (c) Fresh-proc:  ${wr.exactText} ${wr.error ? "(ERROR)" : "(certified)"}`);
    }
  } catch (err) {
    console.error("Failed to parse wire results:", err);
  }
}

console.log("\n=== DIAGNOSTIC TABLE ===\n");
console.log("| Expression                              | (a) Direct | (b) Same-proc | (c) Fresh-proc |");
console.log("|----------------------------------------|------------|---------------|----------------|");
for (const source of testCases) {
  // Get direct
  let directResult = "";
  try {
    const node = compileExpression(source, {});
    const direct = exactReport(node, {}, { maxNodes: 200_000 });
    directResult = direct.unverified ? "—" : formatExact(direct.value).replace(/\u200b/g, "");
  } catch {
    directResult = "ERROR";
  }
  
  // Get same-proc
  let sameProcResult = "";
  try {
    const node = compileExpression(source, {});
    const packed = packCircuit(node);
    const unpacked = unpackCircuit(packed.tokens, packed.root);
    const roundTrip = exactReport(unpacked, {}, { maxNodes: 200_000 });
    sameProcResult = roundTrip.unverified ? "—" : formatExact(roundTrip.value).replace(/\u200b/g, "");
  } catch {
    sameProcResult = "ERROR";
  }
  
  // Get fresh-proc from results
  let freshProcResult = "—";
  if (childResult.status === 0) {
    try {
      const wireResults: WireResult[] = JSON.parse(childResult.stdout);
      const wr = wireResults.find(r => r.source === source);
      if (wr) {
        freshProcResult = wr.exactText;
      }
    } catch {
      freshProcResult = "ERROR";
    }
  }
  
  const shortSource = source.length > 40 ? source.substring(0, 37) + "..." : source;
  console.log(`| ${shortSource.padEnd(38)} | ${directResult.padEnd(10)} | ${sameProcResult.padEnd(13)} | ${freshProcResult.padEnd(14)} |`);
}
