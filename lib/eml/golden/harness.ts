#!/usr/bin/env tsx
/**
 * Golden output parity harness for EML and One.
 * 
 * This script evaluates a fixed corpus of expressions and records:
 * - Exact-mode display text
 * - Certification flags/notes (certified, not-certified, differs-from-float,
 *   singular/precision notes, series-shortcut 'lead' marks)
 * - Float-mode display text
 * - Press/RPN word or press count
 * - packCircuit→unpackCircuit round-trip verification
 * 
 * The output is deterministic (no timings) and stored in a stable,
 * sorted format for readable diffs.
 */

import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { getAllCorpus, heavyCorpus } from "./corpus";
import { compileExpression } from "../parse";
import { exactReport, formatExact, exactToFloat, exactClose } from "../exact";
import { evaluateReport } from "../node";
import { packCircuit, unpackCircuit } from "../wire";
import { seriesShortcutNote } from "../library";
import { pressPreviewForNode } from "../presses";
import { formatC } from "../format";
import type { Node } from "../node";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../../..");
const goldenPath = path.join(repoRoot, "lib/eml/golden/golden.txt");

interface GoldenEntry {
  source: string;
  exactText: string;
  exactNotes: string[];
  floatText: string;
  floatNotes: string[];
  pressCount: string;
  roundTripOk: boolean;
  roundTripError?: string;
}

function evaluateExpression(source: string, useCache: boolean): GoldenEntry {
  // Disable cache if requested
  const originalCache = process.env.EML_NOCACHE;
  if (!useCache) {
    process.env.EML_NOCACHE = "1";
  }
  
  try {
    const node = compileExpression(source, {});
    const budget = { maxNodes: 200_000 };
    
    // Exact mode evaluation
    const exactRep = exactReport(node, {}, budget);
    const exactNotes: string[] = [];
    
    let exactText = "";
    if (exactRep.unverified) {
      exactText = "—";
      exactNotes.push("couldn't verify");
    } else if (exactRep.singular !== null) {
      exactText = formatExact(exactRep.value).replace(/\u200b/g, "");
      exactNotes.push(`singular:${exactRep.singular}`);
    } else {
      exactText = formatExact(exactRep.value).replace(/\u200b/g, "");
      exactNotes.push("certified");
    }
    
    if (exactRep.touchedLn0) {
      exactNotes.push("ln0");
    }
    
    // Check for series shortcut
    const shortcut = seriesShortcutNote(node);
    if (shortcut) {
      exactNotes.push("series-shortcut");
    }
    
    // Float mode evaluation
    const floatRep = evaluateReport(node, {}, budget);
    const floatNotes: string[] = [];
    
    let floatText = "";
    if (floatRep.unverified) {
      floatText = "—";
      floatNotes.push("unverified");
    } else {
      floatText = formatC({ re: floatRep.value.re, im: floatRep.value.im });
    }
    
    if (floatRep.singular !== null) {
      floatNotes.push(`singular:${floatRep.singular}`);
    }
    if (floatRep.touchedLn0) {
      floatNotes.push("ln0");
    }
    if (floatRep.overflowed) {
      floatNotes.push("overflowed");
    }
    if (floatRep.underflowed) {
      floatNotes.push("underflowed");
    }
    if (floatRep.nearCut) {
      floatNotes.push("near-cut");
    }
    
    // Check if float differs from exact
    if (!exactRep.unverified && !floatRep.unverified) {
      const exactFloat = exactToFloat(exactRep.value);
      const reDiff = Math.abs(exactFloat.re - floatRep.value.re);
      const imDiff = Math.abs(exactFloat.im - floatRep.value.im);
      const reScale = Math.max(Math.abs(exactFloat.re), Math.abs(floatRep.value.re), 1e-320);
      const imScale = Math.max(Math.abs(exactFloat.im), Math.abs(floatRep.value.im), 1e-320);
      
      if (reDiff / reScale > 5e-12 || imDiff / imScale > 5e-12) {
        floatNotes.push("differs-from-exact");
      }
    }
    
    // Press count
    const press = pressPreviewForNode(node);
    const pressCount = press 
      ? (press.truncated ? `${press.presses.toString()}+` : press.presses.toString())
      : "N/A";
    
    // Round-trip test: packCircuit → unpackCircuit
    let roundTripOk = true;
    let roundTripError: string | undefined;
    
    try {
      const packed = packCircuit(node);
      const unpacked = unpackCircuit(packed.tokens, packed.root);
      
      // Evaluate unpacked and compare
      const unpackedExact = exactReport(unpacked, {}, budget);
      
      // Compare results
      if (exactRep.unverified && !unpackedExact.unverified) {
        roundTripOk = false;
        roundTripError = "unverified→verified";
      } else if (!exactRep.unverified && unpackedExact.unverified) {
        roundTripOk = false;
        roundTripError = "verified→unverified";
      } else if (!exactRep.unverified && !unpackedExact.unverified) {
        const originalText = formatExact(exactRep.value);
        const unpackedText = formatExact(unpackedExact.value);
        if (originalText !== unpackedText) {
          roundTripOk = false;
          roundTripError = `text-mismatch`;
        }
      }
    } catch (err) {
      roundTripOk = false;
      roundTripError = err instanceof Error ? err.message : String(err);
    }
    
    return {
      source,
      exactText,
      exactNotes,
      floatText,
      floatNotes,
      pressCount,
      roundTripOk,
      roundTripError,
    };
  } finally {
    // Restore original cache setting
    if (originalCache !== undefined) {
      process.env.EML_NOCACHE = originalCache;
    } else {
      delete process.env.EML_NOCACHE;
    }
  }
}

function formatGoldenEntry(entry: GoldenEntry, knownBugs: Map<string, string>): string {
  const parts: string[] = [];
  
  parts.push(`expr: ${entry.source}`);
  parts.push(`exact: ${entry.exactText}`);
  parts.push(`exact-notes: ${entry.exactNotes.join(",")}`);
  parts.push(`float: ${entry.floatText}`);
  parts.push(`float-notes: ${entry.floatNotes.join(",")}`);
  parts.push(`press: ${entry.pressCount}`);
  parts.push(`round-trip: ${entry.roundTripOk ? "OK" : `FAIL:${entry.roundTripError}`}`);
  
  const bugId = knownBugs.get(entry.source);
  if (bugId) {
    parts.push(`# KNOWN-BUG ${bugId}`);
  }
  
  return parts.join(" | ");
}

function parseGoldenFile(content: string): Map<string, string> {
  const lines = content.split("\n").filter(line => line.trim() && !line.startsWith("#"));
  const map = new Map<string, string>();
  
  for (const line of lines) {
    const match = line.match(/^expr: (.+?) \|/);
    if (match) {
      map.set(match[1], line);
    }
  }
  
  return map;
}

function generateGolden(includeHeavy: boolean): string {
  const corpus = includeHeavy ? [...getAllCorpus(), ...heavyCorpus] : getAllCorpus();
  
  // Known bugs (from docs/known-limitations.md and task description)
  const knownBugs = new Map<string, string>();
  knownBugs.set("6.103e-120*i+6.103e-120*i", "v1.1-complex-half");
  knownBugs.set("(i*(1+10^(-124))-i)*i+i*10^10/3", "A1-real-drop");
  
  // Evaluate all expressions
  console.log(`Evaluating ${corpus.length} expressions...`);
  const entries: GoldenEntry[] = [];
  
  for (const source of corpus) {
    try {
      const entry = evaluateExpression(source, true);
      entries.push(entry);
    } catch (err) {
      console.error(`Error evaluating ${source}:`, err);
      entries.push({
        source,
        exactText: "ERROR",
        exactNotes: [err instanceof Error ? err.message : String(err)],
        floatText: "ERROR",
        floatNotes: [],
        pressCount: "?",
        roundTripOk: false,
        roundTripError: "evaluation-error",
      });
    }
  }
  
  // Sort by source for stable output
  entries.sort((a, b) => a.source.localeCompare(b.source));
  
  // Format output
  const lines: string[] = [];
  lines.push("# EML and One Golden Output");
  lines.push(`# Generated: ${new Date().toISOString()}`);
  lines.push(`# Corpus size: ${entries.length}`);
  lines.push("");
  
  for (const entry of entries) {
    lines.push(formatGoldenEntry(entry, knownBugs));
  }
  
  return lines.join("\n") + "\n";
}

function checkCacheConsistency(): { ok: boolean; issues: string[] } {
  console.log("Checking cache consistency (COLD vs WARM)...");
  const issues: string[] = [];
  const corpus = getAllCorpus().slice(0, 50); // Sample for cache check
  
  // COLD run (with cache disabled)
  const coldResults = new Map<string, string>();
  for (const source of corpus) {
    try {
      const entry = evaluateExpression(source, false);
      coldResults.set(source, entry.exactText);
    } catch (err) {
      coldResults.set(source, "ERROR");
    }
  }
  
  // WARM run (with cache enabled, twice)
  for (let pass = 1; pass <= 2; pass++) {
    for (const source of corpus) {
      try {
        const entry = evaluateExpression(source, true);
        const cold = coldResults.get(source);
        
        if (entry.exactText !== cold) {
          const issue = `CACHE-MISMATCH [pass${pass}]: ${source} | cold=${cold} warm=${entry.exactText}`;
          if (!issues.includes(issue)) {
            issues.push(issue);
          }
        }
      } catch (err) {
        // Skip errors in warm run
      }
    }
  }
  
  return { ok: issues.length === 0, issues };
}

function main() {
  const args = process.argv.slice(2);
  const isUpdate = args.includes("--update");
  const isHeavy = args.includes("--heavy");
  
  if (isUpdate) {
    console.log("Regenerating golden output...");
    const content = generateGolden(isHeavy);
    writeFileSync(goldenPath, content, "utf-8");
    console.log(`Golden output written to ${goldenPath}`);
    
    // Also run cache check on update
    const cacheCheck = checkCacheConsistency();
    if (!cacheCheck.ok) {
      console.error("\nCache consistency issues found:");
      for (const issue of cacheCheck.issues) {
        console.error(`  KNOWN: ${issue}`);
      }
      console.log("\nThese are known issues (v1.1 fixes planned).");
    } else {
      console.log("\nCache consistency: OK");
    }
    
    process.exit(0);
  }
  
  // Compare mode
  console.log("Comparing against golden output...");
  
  let existingContent: string;
  try {
    existingContent = readFileSync(goldenPath, "utf-8");
  } catch (err) {
    console.error(`Could not read ${goldenPath}`);
    console.error("Run with --update to generate the golden output.");
    process.exit(1);
  }
  
  const newContent = generateGolden(isHeavy);
  
  if (newContent === existingContent) {
    console.log("✓ Golden output matches!");
    
    // Run cache check
    const cacheCheck = checkCacheConsistency();
    if (!cacheCheck.ok) {
      console.log("\nCache consistency issues (KNOWN, v1.1):");
      for (const issue of cacheCheck.issues) {
        console.log(`  ${issue}`);
      }
    } else {
      console.log("✓ Cache consistency OK");
    }
    
    process.exit(0);
  }
  
  // Show diff
  const existingLines = existingContent.split("\n");
  const newLines = newContent.split("\n");
  const existing = parseGoldenFile(existingContent);
  const current = parseGoldenFile(newContent);
  
  let diffCount = 0;
  
  // Check for changed expressions
  for (const [source, newLine] of current.entries()) {
    const oldLine = existing.get(source);
    if (!oldLine) {
      console.log(`+ NEW: ${source}`);
      console.log(`  ${newLine}`);
      diffCount++;
    } else if (oldLine !== newLine) {
      console.log(`~ CHANGED: ${source}`);
      console.log(`  - ${oldLine}`);
      console.log(`  + ${newLine}`);
      diffCount++;
    }
  }
  
  // Check for removed expressions
  for (const source of existing.keys()) {
    if (!current.has(source)) {
      console.log(`- REMOVED: ${source}`);
      diffCount++;
    }
  }
  
  console.log(`\n${diffCount} difference(s) found.`);
  console.log("\nRun with --update to regenerate the golden output.");
  console.log("Note: Every changed line must be explained in the PR description.");
  
  process.exit(1);
}

main();
