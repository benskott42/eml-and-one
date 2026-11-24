// Key captions and tooltips. No "use client": app/page.tsx builds the tables
// for the first screen at export time and hands them to EmlCalculator, so the
// browser does not rebuild every key's circuit while it hydrates.

import {
  BINARY_KEYS,
  CONSTANT_KEYS,
  UNARY_KEYS,
  applyBinaryNode,
  applyUnaryNode,
  binaryNode,
  constantNode,
  integerNode,
  scalarNode,
  unaryNode,
} from "@/lib/eml/library";
import { EmlError, type Node, circuitStats } from "@/lib/eml/node";
import { compileExpression } from "@/lib/eml/parse";
import { pressPreviewForNode } from "@/lib/eml/presses";

export const INITIAL_X = "0.5";
export const INITIAL_Y = "2";

/** Key id to text. */
export type KeyTable = Record<string, string>;

export type KeyTables = {
  /** keyCosts([], INITIAL_X, INITIAL_Y): the K captions while the stack is empty and x, y are untouched. */
  costs: KeyTable;
  /** keyExpansions(). */
  expansions: KeyTable;
};

/** The x or y field. Its own errors name the field: "Enter an expression." read as the box below. */
export function readScalar(text: string, field: "x" | "y"): Node {
  const trimmed = text.trim();
  if (!trimmed) throw new EmlError(`Give ${field} a value.`);
  try {
    return scalarNode(trimmed);
  } catch {
    try {
      return compileExpression(trimmed, {});
    } catch (err) {
      if (err instanceof EmlError) throw new EmlError(`In ${field}: ${err.message}`);
      throw err;
    }
  }
}

function shortcutTitle(node: Node, hint?: string): string {
  const presses = pressPreviewForNode(node);
  const lead = hint ? `${hint}. ` : "";
  if (!presses) return `${lead}Shortcut for the 1 and EML keys.`;
  return `${lead}Presses ${presses.preview}${presses.truncated ? ` (${presses.presses} presses)` : ""}`;
}

/** The K caption under each key, for what that key would push onto this stack. */
export function keyCosts(stack: readonly { node: Node }[], xText: string, yText: string): KeyTable {
  const table: KeyTable = {};
  const label = (node: Node) => {
    const k = circuitStats(node).rpnLength;
    return k <= BigInt(9999) ? `K ${k}` : "wide";
  };
  for (const key of CONSTANT_KEYS) {
    try {
      table[key.id] = label(constantNode(key.id));
    } catch {
      table[key.id] = "";
    }
  }
  let xNode = integerNode(2);
  let yNode = integerNode(3);
  try {
    if (stack.length >= 2) {
      xNode = stack[stack.length - 2]?.node ?? xNode;
      yNode = stack[stack.length - 1]?.node ?? yNode;
    } else if (stack.length === 1) {
      xNode = stack[0]?.node ?? xNode;
      yNode = readScalar(yText, "y");
    } else {
      xNode = readScalar(xText, "x");
      yNode = readScalar(yText, "y");
    }
  } catch {
    xNode = integerNode(2);
    yNode = integerNode(3);
  }
  const arg = stack[stack.length - 1]?.node ?? xNode;
  for (const key of UNARY_KEYS) {
    try {
      table[key.id] = label(applyUnaryNode(key.id, arg));
    } catch {
      table[key.id] = "";
    }
  }
  for (const key of BINARY_KEYS) {
    try {
      table[key.id] = label(applyBinaryNode(key.id, xNode, yNode));
    } catch {
      table[key.id] = "";
    }
  }
  return table;
}

/** The tooltip on each shortcut key: the presses it stands for. It does not depend on the stack. */
export function keyExpansions(): KeyTable {
  const table: KeyTable = {};
  for (const key of CONSTANT_KEYS) {
    try {
      table[key.id] = shortcutTitle(constantNode(key.id), key.label);
    } catch {
      table[key.id] = "Shortcut for the 1 and EML keys.";
    }
  }
  for (const key of UNARY_KEYS) {
    try {
      table[key.id] = shortcutTitle(unaryNode(key.id), key.label);
    } catch {
      table[key.id] = "Shortcut for the 1 and EML keys.";
    }
  }
  for (const key of BINARY_KEYS) {
    try {
      table[key.id] = shortcutTitle(binaryNode(key.id), key.hint);
    } catch {
      table[key.id] = key.hint;
    }
  }
  return table;
}

export function initialKeyTables(): KeyTables {
  return { costs: keyCosts([], INITIAL_X, INITIAL_Y), expansions: keyExpansions() };
}
