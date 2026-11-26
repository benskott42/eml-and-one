import { eml, type C } from "./complex";
import { binaryToRpn } from "./binary";
import { formatC } from "./format";
import { type Node } from "./node";
import { isProgram } from "./programIndex";

export type RpnTraceStep = {
  /** 1-based step index (0 is the initial empty stack). */
  step: number;
  /** Token pressed at this step ("1" or "E"), or "" at step 0. */
  token: "1" | "E" | "";
  /** Binary bit ("1" for 1, "0" for E), or "" at step 0. */
  bit: "1" | "0" | "";
  /** Formatted stack values from bottom to top. */
  stack: string[];
  /** Formatted top of stack, or "empty" at step 0. */
  top: string;
  /** Number of items on the stack after this step. */
  depth: number;
};

export type TreeLayoutNode = {
  id: number;
  label: "1" | "E";
  /** 1-based RPN step index that produces this node. */
  step: number;
  /** Normalized x coordinate in [0, 1] or pixel space. */
  x: number;
  /** Depth from root (0 = root). */
  depth: number;
  leftId: number | null;
  rightId: number | null;
};

export type TreeLayout = {
  nodes: TreeLayoutNode[];
  edges: Array<{ from: number; to: number }>;
  maxDepth: number;
  leafCount: number;
};

const MAX_EXPORT_NODES = 120;

function countTreeNodes(node: Node, cap = MAX_EXPORT_NODES + 1): number {
  let count = 0;
  const stack: Node[] = [node];
  while (stack.length > 0) {
    const cur = stack.pop();
    if (!cur) break;
    count += 1;
    if (count >= cap) return count;
    if (cur.type === "eml" && cur.a && cur.b) {
      stack.push(cur.b, cur.a);
    }
  }
  return count;
}

function leafLabel(node: Node, format: "eml" | "lean" | "latex"): string {
  if (node.type === "one") return "1";
  if (node.type === "var") return node.name;
  if (node.type === "input") {
    const text = formatC(node.value);
    return format === "lean" ? `(${text})` : text;
  }
  return "1";
}

/**
 * Format a compact circuit as nested `eml(x, y)` notation.
 * Returns null if the expanded tree exceeds `maxNodes` nodes.
 */
export function nodeToEmlExpr(node: Node, maxNodes = MAX_EXPORT_NODES): string | null {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return null;
  const go = (n: Node): string => {
    if (n.type !== "eml" || !n.a || !n.b) return leafLabel(n, "eml");
    return `eml(${go(n.a)}, ${go(n.b)})`;
  };
  return go(node);
}

/**
 * Format a compact circuit as a Lean 4 term (`eml 1 (eml (eml 1 1) 1)`),
 * matching the convention in tomdif/eml-lean.
 * Returns null if the expanded tree exceeds `maxNodes` nodes.
 */
export function nodeToLean4(node: Node, maxNodes = MAX_EXPORT_NODES): string | null {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return null;
  const go = (n: Node, parens: boolean): string => {
    if (n.type !== "eml" || !n.a || !n.b) return leafLabel(n, "lean");
    const inner = `eml ${go(n.a, true)} ${go(n.b, true)}`;
    return parens ? `(${inner})` : inner;
  };
  return go(node, false);
}

/**
 * Format a compact circuit as expanded LaTeX (`\exp(...) - \ln(...)`).
 * Returns null if the expanded tree exceeds `maxNodes` nodes.
 */
export function nodeToLatex(node: Node, maxNodes = MAX_EXPORT_NODES): string | null {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return null;
  const go = (n: Node): string => {
    if (n.type !== "eml" || !n.a || !n.b) return leafLabel(n, "latex");
    const left = go(n.a);
    const right = go(n.b);
    return `\\exp\\!\\left(${left}\\right) - \\ln\\!\\left(${right}\\right)`;
  };
  return go(node);
}

/**
 * Normalize either a binary string ("110") or RPN string ("11E") into a valid RPN string.
 * Throws if invalid.
 */
function normalizeRpn(program: string): string {
  const trimmed = program.trim();
  const rpn = /^[01]+$/.test(trimmed) ? binaryToRpn(trimmed) : trimmed;
  if (!/^[1E]+$/.test(rpn) || !isProgram(rpn)) {
    throw new Error(`Invalid EML program: "${program}"`);
  }
  return rpn;
}

/**
 * Trace a pure 1-and-EML program press by press on a float64 RPN stack.
 * Step 0 is the empty stack; steps 1..K correspond to each press.
 */
export function traceRpnSteps(program: string): RpnTraceStep[] {
  const rpn = normalizeRpn(program);
  const steps: RpnTraceStep[] = [
    { step: 0, token: "", bit: "", stack: [], top: "empty", depth: 0 },
  ];
  const stack: C[] = [];
  for (let i = 0; i < rpn.length; i += 1) {
    const ch = rpn[i];
    if (ch === "1") {
      stack.push({ re: 1, im: 0 });
    } else {
      const y = stack.pop() ?? { re: Number.NaN, im: Number.NaN };
      const x = stack.pop() ?? { re: Number.NaN, im: Number.NaN };
      stack.push(eml(x, y));
    }
    const formatted = stack.map((v) => formatC(v));
    steps.push({
      step: i + 1,
      token: ch === "1" ? "1" : "E",
      bit: ch === "1" ? "1" : "0",
      stack: formatted,
      top: formatted[formatted.length - 1] ?? "empty",
      depth: stack.length,
    });
  }
  return steps;
}

/**
 * Build an inorder-spaced binary tree layout from a valid RPN or binary program.
 * Leaf nodes sit at integer x positions 0..(leaves-1); each internal E node sits
 * centered above its two children.
 */
export function layoutBinaryTree(program: string): TreeLayout {
  const rpn = normalizeRpn(program);
  type RawNode = {
    id: number;
    label: "1" | "E";
    step: number;
    left: RawNode | null;
    right: RawNode | null;
  };
  const stack: RawNode[] = [];
  let nextId = 0;
  for (let i = 0; i < rpn.length; i += 1) {
    const ch = rpn[i];
    if (ch === "1") {
      stack.push({ id: nextId++, label: "1", step: i + 1, left: null, right: null });
    } else {
      const right = stack.pop() ?? null;
      const left = stack.pop() ?? null;
      stack.push({ id: nextId++, label: "E", step: i + 1, left, right });
    }
  }
  const root = stack[0];
  if (!root) {
    return { nodes: [], edges: [], maxDepth: 0, leafCount: 0 };
  }

  const nodes: TreeLayoutNode[] = [];
  const edges: Array<{ from: number; to: number }> = [];
  let leafIndex = 0;
  let maxDepth = 0;

  const place = (n: RawNode, depth: number): number => {
    if (depth > maxDepth) maxDepth = depth;
    let x: number;
    if (!n.left || !n.right) {
      x = leafIndex;
      leafIndex += 1;
    } else {
      const lx = place(n.left, depth + 1);
      const rx = place(n.right, depth + 1);
      x = (lx + rx) / 2;
      edges.push({ from: n.id, to: n.left.id }, { from: n.id, to: n.right.id });
    }
    nodes.push({
      id: n.id,
      label: n.label,
      step: n.step,
      x,
      depth,
      leftId: n.left ? n.left.id : null,
      rightId: n.right ? n.right.id : null,
    });
    return x;
  };

  place(root, 0);
  return { nodes, edges, maxDepth, leafCount: leafIndex };
}
