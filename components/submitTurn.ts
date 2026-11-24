import type { C } from "@/lib/eml/complex";
import { evaluateReport, type Node } from "@/lib/eml/node";
import { compileExpression } from "@/lib/eml/parse";
import { readScalar } from "@/components/keyTables";

export type Submission = { node: Node; numbers: Record<string, C> };

/**
 * Compiles the expression field with x and y read from their fields. This is
 * the work that was done in the submit event itself: compileExpression builds
 * the whole circuit inside one isolateCircuit, so the node it returns does not
 * depend on what was built before or after it.
 */
export function compileSubmission(text: string, xText: string, yText: string): Submission {
  const variables: Record<string, Node> = {};
  const numbers: Record<string, C> = {};
  if (/\bx\b/i.test(text)) {
    variables.x = readScalar(xText, "x");
    numbers.x = evaluateReport(variables.x).value;
  }
  if (/\by\b/i.test(text)) {
    variables.y = readScalar(yText, "y");
    numbers.y = evaluateReport(variables.y).value;
  }
  return { node: compileExpression(text, variables), numbers };
}

/**
 * Runs `run` in a later task. A submit then ends its own task after the pending
 * screen, and the compile, the render of the result and the key captions each
 * get a task of their own. Together they took about 70 ms in one task at 6x CPU
 * throttling for tan(10^(−5000)), past the site check's 50 ms limit.
 */
export function nextTurn(run: () => void): () => void {
  const handle = setTimeout(run, 0);
  return () => clearTimeout(handle);
}
