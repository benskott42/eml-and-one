#!/usr/bin/env tsx
/**
 * Detailed diagnostic: check if the issue is in parsing, evaluation, or wire
 */

import { compileExpression } from "../lib/eml/parse";
import { exactReport, formatExact, exactParts } from "../lib/eml/exact";
import { evaluate } from "../lib/eml/node";

const testCases = [
  "((1+10^(-130))-1)+i/2",
  "10^(-130)",
  "((1+10^(-130))-1)",
  "1+10^(-130)",
];

console.log("Detailed diagnostic:\n");

for (const source of testCases) {
  console.log(`\nExpression: ${source}`);
  
  try {
    const node = compileExpression(source, {});
    
    // Float evaluation
    const floatVal = evaluate(node, {}, { maxNodes: 200_000 });
    console.log(`  Float:  re=${floatVal.re.toExponential(6)} im=${floatVal.im.toExponential(6)}`);
    
    // Exact evaluation
    const exact = exactReport(node, {}, { maxNodes: 200_000 });
    const exactText = exact.unverified ? "—" : formatExact(exact.value).replace(/\u200b/g, "");
    console.log(`  Exact:  ${exactText} ${exact.unverified ? "(unverified)" : "(certified)"}`);
    
    if (!exact.unverified) {
      const parts = exactParts(exactText);
      console.log(`  Parts:  re=${parts.re.toString()} im=${parts.im.toString()}`);
    }
  } catch (err) {
    console.log(`  ERROR: ${err}`);
  }
}
