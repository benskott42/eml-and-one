#!/usr/bin/env tsx
/**
 * Child process for fresh-process wire evaluation.
 * Receives packed circuits via stdin, evaluates via unpackCircuit,
 * and returns results as JSON to stdout.
 */

import { unpackCircuit } from "../lib/eml/wire";
import { exactReport, formatExact, exactToFloat } from "../lib/eml/exact";
import { evaluateReport } from "../lib/eml/node";
import { seriesShortcutNote } from "../lib/eml/library";
import { pressPreviewForNode } from "../lib/eml/presses";
import { formatC } from "../lib/eml/format";
import type { Wire } from "../lib/eml/wire";

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

// Read all input
let input = "";
process.stdin.on("data", (chunk) => {
  input += chunk.toString();
});

process.stdin.on("end", () => {
  try {
    const jobs: WireJob[] = JSON.parse(input);
    const results: WireResult[] = [];
    
    for (const job of jobs) {
      try {
        // Unpack the circuit
        const node = unpackCircuit(job.tokens, job.root);
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
        
        results.push({
          source: job.source,
          exactText,
          exactNotes,
          floatText,
          floatNotes,
          pressCount,
        });
      } catch (err) {
        results.push({
          source: job.source,
          exactText: "ERROR",
          exactNotes: [err instanceof Error ? err.message : String(err)],
          floatText: "ERROR",
          floatNotes: [],
          pressCount: "?",
          error: err instanceof Error ? err.message : String(err),
        });
      }
    }
    
    console.log(JSON.stringify(results));
  } catch (err) {
    console.error(JSON.stringify({ error: err instanceof Error ? err.message : String(err) }));
    process.exit(1);
  }
});
