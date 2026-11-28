import { eml, type C } from "./complex";
import { binaryToRpn } from "./binary";
import { formatC } from "./format";
import { certifyRpnForLean, certifyRpnForLeanExt, rpnToLeanBits } from "./leanCert";
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
    const raw = formatC(node.value);
    const text = format === "eml" ? raw : raw.replace(/−/g, "-");
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
 * Format a compact circuit as a Lean 4 term (`eml 1 (eml (eml 1 1) 1)`).
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
 * What the compiler emits for `x − y` with variable operands (lowering.ts `scaledRot`):
 * `k · rotSub(x/k, y/k)` with `k = √(y²) − (−1)` and the K 21 iπ word, 565 tokens.
 * `Eml.AppSub.appSub_correct` (formal/lean/Eml/AppSub.lean) proves that this exact word
 * evaluates to `a − b` in `EmlDir` for every `a b : ℂ`, `b = 0` included. Check 115 fails
 * if the compiler stops emitting it; the Lean bridge compares it with `appSubToks`.
 */
export const APP_SUB_WORD =
  "1111111111111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEE" +
  "E1EE111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE111111111111EEE1" +
  "EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1xE1EE1111111" +
  "11111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1" +
  "EE1E1EEE1EE1111111111E1EEEE11E1E1EEEEE1EE111111111111EEE1EE11EE1EEEE1EE1111111yE" +
  "E1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1EE111111111111EEE1EE11EE1EEEE1EE" +
  "1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1EE1E1EEE1EE1E1EEE1EE1EE" +
  "1EE1E";

/**
 * What the compiler emits for the other operators with variable operands. Each is proved
 * in formal/lean/Eml/AppOps.lean (`add_correct`, `mul_correct`, …) for all inputs:
 * x + y, 2·x, x², √x and exp x exactly; x · y and −x up to the sign of zero; x / y and
 * 1/x for a nonzero divisor; ln x as the principal log. x + y is the x − y circuit with
 * operand (−1)·y. Check 115 and the Lean bridge compare these with the compiler.
 */
export const APP_WORDS: Readonly<Record<string, { source: string; word: string }>> = {
  add: {
    source: "x+y",
    word:
      "1111111111111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEE" +
      "E1EE111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE111111111111EEE1" +
      "EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1xE1EE1111111" +
      "11111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1111" +
      "111111E1EEEE11EEEE1EEyE1EE1EE1EE1E1EEE1EE1111111111E1EEEE11E1E1EEEEE1EE111111111" +
      "111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE111111" +
      "1111E1EEEE11EEEE1EEyE1EE1EE1EE111111111111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1E" +
      "E1EEE1EE1E11111E1EEEE11EE1EEEE1EE1111111111E1EEEE11EEEE1EEyE1EE1EE1EE1E1EEE1EE1E" +
      "1EEE1EE1EE1EE1E",
  },
  mul: {
    source: "x*y",
    word:
      "1111xEE1EEyE1EE1E",
  },
  div: {
    source: "x/y",
    word:
      "111yEE1EE1xE1EE1E",
  },
  neg: {
    source: "-x",
    word:
      "111111111E1EEEE11EEEE1EExE1EE1E",
  },
  sq: {
    source: "x^2",
    word:
      "1111111111EEE1EE11EE1EEEE1EE11xE1EEE1EE1E1E",
  },
  twoMul: {
    source: "2*x",
    word:
      "1111111111EEE1EE11EE1EEEE1EExE1EE1E",
  },
  inv: {
    source: "1/x",
    word:
      "111xEE1EE11E1EE1E",
  },
  sqrt: {
    source: "sqrt(x)",
    word:
      "111111111EEE1EE11EE1EEEE1EE111xE1EEE1EE1E1E",
  },
  exp: {
    source: "exp(x)",
    word:
      "x1E",
  },
  ln: {
    source: "ln(x)",
    word:
      "11xE1EE",
  },
  subOne: {
    source: "x-1",
    word:
      "111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE11xE1EE11EEE1EE11111" +
      "11111E1EEEE11E1E1EEEEE1EE111E1EE11EEE1EE1E1EEE1EE1E",
  },
  addOne: {
    source: "x+1",
    word:
      "111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE11xE1EE11111E1EEEE11" +
      "EE1EEE1EE1111111111E1EEEE11E1E1EEEEE1EE1111111E1EEEE11EEE1EE11111E1EEEE11EE1EEE1" +
      "EE1E1EEE1EE1E",
  },
  subTwo: {
    source: "x-2",
    word:
      "111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE11xE1EE111111EEE1EE1" +
      "1EE1EE1EEE1EE1111111111E1EEEE11E1E1EEEEE1EE11111111EEE1EE11EE1EEE1EE111111EEE1EE" +
      "11EE1EE1EEE1EE1E1EEE1EE1E",
  },
  pow: {
    source: "x^y",
    word:
      "1111yEE1EE11xE1EEE1EE1E1E",
  },
  expE: {
    source: "e^x",
    word:
      "1111xEE1EE1111EE1EEE1EE1E1E",
  },
  mulTwo: {
    source: "x*2",
    word:
      "1111xEE1EE111111EEE1EE11EE1EEE1EE1E",
  },
  divTwo: {
    source: "x/2",
    word:
      "111111111EEE1EE11EE1EEEE1EE1xE1EE1E",
  },
  cube: {
    source: "x^3",
    word:
      "111111111111EEE1EE11EEE1EE11EE1EEEE1EE11xE1EEE1EE1E1E",
  },
};

/**
 * RPN of a circuit whose leaves are `1` or variables, with each variable as its
 * name (`1`, `x`, `y`, `E`), or `null` for any other leaf or past `maxNodes`.
 */
export function variableRpnFromNode(node: Node, maxNodes = 4096): string | null {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return null;
  const out: string[] = [];
  const stack: { n: Node; seen: boolean }[] = [{ n: node, seen: false }];
  while (stack.length > 0) {
    const frame = stack.pop()!;
    const n = frame.n;
    if (n.type === "one") out.push("1");
    else if (n.type === "var") out.push(n.name);
    else if (n.type === "eml" && n.a && n.b) {
      if (frame.seen) out.push("E");
      else stack.push({ n, seen: true }, { n: n.b, seen: false }, { n: n.a, seen: false });
    } else return null;
  }
  return out.join("");
}

/**
 * Extract the pure RPN string (`1` and `E`) for a compact pure circuit,
 * or `null` if it contains variables/inputs or exceeds `maxNodes`.
 */
function pureRpnFromNode(node: Node, maxNodes = MAX_EXPORT_NODES): string | null {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return null;
  let pure = true;
  const out: string[] = [];
  const go = (n: Node) => {
    if (!pure) return;
    if (n.type === "one") {
      out.push("1");
      return;
    }
    if (n.type === "eml" && n.a && n.b) {
      go(n.a);
      go(n.b);
      out.push("E");
      return;
    }
    pure = false;
  };
  go(node);
  return pure ? out.join("") : null;
}

/** Collect distinct variable names (`var` nodes) in a compact circuit. */
function freeVarsFromNode(node: Node, maxNodes = MAX_EXPORT_NODES): string[] {
  if (countTreeNodes(node, maxNodes + 1) > maxNodes) return [];
  const vars = new Set<string>();
  const stack: Node[] = [node];
  while (stack.length > 0) {
    const cur = stack.pop();
    if (!cur) break;
    if (cur.type === "var") vars.add(cur.name);
    else if (cur.type === "eml" && cur.a && cur.b) stack.push(cur.b, cur.a);
  }
  return [...vars].sort();
}

/**
 * Format a compact circuit as a ready-to-compile Lean 4 + Mathlib snippet
 * against `formal/lean/Eml/`.
 *
 * - If the circuit is pure and certified by `Eml.Cert.certify`, emits a
 *   kernel-checked `theorem circuit_eval` proved in one line by `certify_sound (by decide)`.
 * - Else if it matches a pre-proved record in `LEAN_VERIFIED_THEOREMS`, emits a
 *   compiling check against that theorem.
 * - Else if `Eml.Cert.certifyExt` certifies it in `EmlExt` (`ln 0 = −∞`), emits a
 *   theorem proved by `certifyExt_sound (by decide)`.
 * - Otherwise emits a compiling `noncomputable def circuit : ℂ` (binding any
 *   free variables as parameters).
 */
export function nodeToLean4Snippet(node: Node, maxNodes = MAX_EXPORT_NODES): string | null {
  const term = nodeToLean4(node, maxNodes);
  if (!term) return null;

  const rpn = pureRpnFromNode(node, maxNodes);
  if (rpn) {
    const cert = certifyRpnForLean(rpn, maxNodes);
    if (cert) {
      const bits = rpnToLeanBits(rpn);
      return [
        "import Eml.Cert",
        "",
        "open Eml Eml.Binary Eml.Extended Eml.Cert",
        "",
        `def circuitBits : List Bool := ${bits}`,
        "",
        `/-- Kernel-checked value: \`${cert.display}\` (both \`ℂ\` and \`EmlExt\`, zero \`ln 0\`). -/`,
        "theorem circuit_eval :",
        `    evalRpn (1 : ℂ) eml circuitBits [] = some [(${cert.leanSym} : Sym).denote] ∧`,
        `    evalRpn (EmlExt.finite 1) extEml circuitBits [] = some [.finite (${cert.leanSym} : Sym).denote] :=`,
        "  certify_sound (by decide)",
        "",
      ].join("\n");
    }

    const ref = leanTheoremForRpn(rpn);
    if (ref) {
      return [
        "import Eml",
        "",
        "open Eml Eml.Binary Eml.Extended",
        "",
        `-- Machine-checked (${ref.model === "C" ? "ℂ" : "EmlExt, uses ln 0 = −∞"}): ${ref.value}`,
        `#check @${ref.theorem}`,
        "",
      ].join("\n");
    }

    const ext = certifyRpnForLeanExt(rpn, maxNodes);
    if (ext) {
      return [
        "import Eml.CertExt",
        "",
        "open Eml Eml.Binary Eml.Extended Eml.Cert",
        "",
        `def circuitBits : List Bool := ${rpnToLeanBits(rpn)}`,
        "",
        `/-- Kernel-checked value in \`EmlExt\` (uses \`ln 0 = −∞\`): \`${ext.display}\`. -/`,
        "theorem circuit_eval :",
        `    evalRpn (EmlExt.finite 1) extEml circuitBits [] = some [(${ext.leanXSym} : XSym).denote] :=`,
        "  certifyExt_sound (by decide)",
        "",
      ].join("\n");
    }
  }

  const vars = freeVarsFromNode(node, maxNodes);
  const binders = vars.length > 0 ? ` (${vars.join(" ")} : ℂ)` : "";
  return `import Eml.Basic\n\nopen Eml\n\nnoncomputable def circuit${binders} : ℂ :=\n  ${term}\n`;
}

export type LeanTheoremRef = {
  theorem: string;
  file: string;
  value: string;
  /**
   * The proved stack value as a Lean term, exactly as the theorem states it
   * (an `ℂ` term for `"C"`, an `EmlExt` term otherwise). The bridge proves
   * `evalRpn … = some [lean]` from the theorem, and check 112 compares this
   * term numerically with the exact engine's value of the word.
   */
  lean: string;
  /** `"C"` = proved over plain `ℂ` (no `ln 0`); `"EmlExt"` = proved in `EmlExt` (uses `ln 0 = −∞`). */
  model: "C" | "EmlExt";
};

/** Exact RPN words with machine-checked Lean 4 + Mathlib `evalRpn` proofs in `formal/lean/Eml/`. */
export const LEAN_VERIFIED_THEOREMS: Record<string, LeanTheoremRef> = {
  "1": { theorem: "Eml.RpnSoundness.evalRpn_0x1", file: "RpnSoundness.lean", value: "1", model: "C", lean: "(1 : ℂ)" },
  "11E": { theorem: "Eml.RpnSoundness.evalRpn_0x6", file: "RpnSoundness.lean", value: "e", model: "C", lean: "(Complex.exp 1 : ℂ)" },
  "111E1EE": { theorem: "Eml.RpnSoundness.evalRpn_0x74", file: "RpnSoundness.lean", value: "0 (minimal K=7: Eml.MinimalityZero.zero_minimal_k7)", model: "C", lean: "(0 : ℂ)" },
  "11111E1EEEE": { theorem: "Eml.Extended.evalRpn_0x7d0", file: "Extended.lean", value: "−∞", model: "EmlExt", lean: "EmlExt.negInf" },
  "11111E1EEEE11EE": { theorem: "Eml.Extended.evalRpn_0x7d0c", file: "Extended.lean", value: "−1", model: "EmlExt", lean: "EmlExt.finite (-1)" },
  "11111EEE1EE11E1EE": { theorem: "Eml.Records.evalRpn_negOne_strict", file: "Records.lean", value: "−1 (no ln 0)", model: "C", lean: "(-1 : ℂ)" },
  "111111EEE1EE11EE1EE": { theorem: "Eml.Records.evalRpn_two", file: "Records.lean", value: "2", model: "C", lean: "(2 : ℂ)" },
  "111111E1EEEE11E1E1EEE": { theorem: "Eml.Extended.evalRpn_0x1fa1a8", file: "Extended.lean", value: "+iπ (lower cut)", model: "EmlExt", lean: "EmlExt.finite (Real.pi * Complex.I)" },
  "111111E1E1EEE1EE11E1EEE": { theorem: "Eml.Records.evalRpn_ipi_strict", file: "Records.lean", value: "+iπ (no ln 0)", model: "C", lean: "(Real.pi * Complex.I : ℂ)" },
  "111111E1EEEE11E1E1EEE11EE": { theorem: "Eml.Extended.evalRpn_0x1fa1a8c", file: "Extended.lean", value: "−2", model: "EmlExt", lean: "EmlExt.finite (-2)" },
  "11111111EEE1EE11EE1EEE1EE": { theorem: "Eml.Records.evalRpn_ln2", file: "Records.lean", value: "ln 2", model: "C", lean: "(Complex.log 2 : ℂ)" },
  "11111111EEE1EE11EEE1EE11EE1EE": { theorem: "Eml.Records.evalRpn_three", file: "Records.lean", value: "3", model: "C", lean: "(3 : ℂ)" },
  "111E11111E1EEEE11E1E1EE1EEE1E": { theorem: "Eml.Extended.evalRpn_half", file: "Extended.lean", value: "1/2", model: "EmlExt", lean: "EmlExt.finite ((1 : ℂ) / 2)" },
  "1111111E1EEEE11EEE11E1E1EEE1E": { theorem: "Eml.Extended.evalRpn_negHalf", file: "Extended.lean", value: "−1/2", model: "EmlExt", lean: "EmlExt.finite (-(1 : ℂ) / 2)" },
  "111E111111EEE1EE11E1EEE1E1EEE1E": { theorem: "Eml.Records.evalRpn_half_strict", file: "Records.lean", value: "1/2 (no ln 0)", model: "C", lean: "((1 : ℂ) / 2 : ℂ)" },
  "1111111EEE1EE11E1EEE11E1E1EEE1E": { theorem: "Eml.Records.evalRpn_negHalf_strict", file: "Records.lean", value: "−1/2 (no ln 0)", model: "C", lean: "(-(1 : ℂ) / 2 : ℂ)" },
  "1111111E1E1EEE1EE11E1E1EE1EEE1E": { theorem: "Eml.Records.evalRpn_half_alt", file: "Records.lean", value: "1/2 (alt, no ln 0)", model: "C", lean: "((1 : ℂ) / 2 : ℂ)" },
  "111E111111E1EEEE11EEE11E1E1EE1EEE1E": { theorem: "Eml.Extended.evalRpn_third", file: "Extended.lean", value: "1/3", model: "EmlExt", lean: "EmlExt.finite ((1 : ℂ) / 3)" },
  "111E111111EEE1EE11E1EEE11E1E1EE1EEE1E": { theorem: "Eml.Records.evalRpn_third_strict", file: "Records.lean", value: "1/3 (no ln 0)", model: "C", lean: "((1 : ℂ) / 3 : ℂ)" },
  "11111111EEE1EE11EE1EEE11E1E1EEE11EE": { theorem: "Eml.Records.evalRpn_negThree", file: "Records.lean", value: "−3", model: "C", lean: "(-3 : ℂ)" },
  "1111111111EEE1EE11EEE1EE11EEE1EE11EE1EE": { theorem: "Eml.Records.evalRpn_four", file: "Records.lean", value: "4", model: "C", lean: "(4 : ℂ)" },
  "111E1111111EEE1EE11EE1EEE11E1E1EE1EEE1E": { theorem: "Eml.Records.evalRpn_twoThirds", file: "Records.lean", value: "2/3", model: "C", lean: "((2 : ℂ) / 3 : ℂ)" },
  "111E1111111EEE1EE11EE1EEE11E1E1EE1EEE11EE": { theorem: "Eml.Records.evalRpn_negThird", file: "Records.lean", value: "−1/3", model: "C", lean: "(-(1 : ℂ) / 3 : ℂ)" },
  "111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1E": { theorem: "Eml.Extended.evalRpn_i", file: "Extended.lean", value: "i", model: "EmlExt", lean: "EmlExt.finite Complex.I" },
  "111111111EEE1EE11EE1EEEE1EE111111111EEE1EE11EE1EEE1EEE1EE1E1E": { theorem: "Eml.Records.evalRpn_sqrt2", file: "Records.lean", value: "√2", model: "C", lean: "((Real.sqrt 2 : ℂ) : ℂ)" },
  "11111E1E1EEEE11111E1EEEE11111E1E1EEEE1E1E1EEE": { theorem: "Eml.Extended.evalRpn_negIpi", file: "Extended.lean", value: "−iπ (lower cut)", model: "EmlExt", lean: "EmlExt.finite (-(Real.pi * Complex.I))" },
  "11111E1E1EEEE11111111E1E1EEEE1E1E1EEE1EE11E1EEE": { theorem: "Eml.Records.evalRpn_negIpi_strict", file: "Records.lean", value: "−iπ (lower cut, no ln 0)", model: "C", lean: "(-(Real.pi * Complex.I) : ℂ)" },
  "1111111111E1EEEE11E1E1EEEE1EEE1EE111111111EEE1EE11EE1EEEE1EE1111111E1EEEE11E1E1EEEE1EE1E1EE1E": { theorem: "Eml.Extended.evalRpn_pi", file: "Extended.lean", value: "π", model: "EmlExt", lean: "EmlExt.finite (Real.pi : ℂ)" },
  "111111EEE1EE11EE1EE1E": { theorem: "Eml.MoreRecords.evalRpn_eSq", file: "MoreRecords.lean", value: "e²", model: "C", lean: "(Complex.exp 2 : ℂ)" },
  "11111EEE1EE11E1EE1E": { theorem: "Eml.MoreRecords.evalRpn_invE_strict", file: "MoreRecords.lean", value: "1/e (no ln 0)", model: "C", lean: "(Complex.exp (-1) : ℂ)" },
  "1111E11E1EEE1EE11E1E1EE": { theorem: "Eml.MoreRecords.evalRpn_negE_strict", file: "MoreRecords.lean", value: "−e (no ln 0)", model: "C", lean: "(-Complex.exp 1 : ℂ)" },
  "111E1EE1111111EEE1EE11E1EEE11E1E1EEE1E1EE": { theorem: "Eml.MoreRecords.evalRpn_threeHalves_strict", file: "MoreRecords.lean", value: "3/2 (no ln 0)", model: "C", lean: "((3 : ℂ) / 2 : ℂ)" },
  "1111111EEE1EE11E1EEE11E1E1EEE11EE": { theorem: "Eml.MoreRecords.evalRpn_negThreeHalves_strict", file: "MoreRecords.lean", value: "−3/2 (no ln 0)", model: "C", lean: "(-(3 : ℂ) / 2 : ℂ)" },
  "11111E1EEEE11EE1E": { theorem: "Eml.MoreRecords.evalRpn_invE", file: "MoreRecords.lean", value: "1/e", model: "EmlExt", lean: "EmlExt.finite (Complex.exp (-1))" },
  "11111E1EEEE11E1EE": { theorem: "Eml.MoreRecords.evalRpn_negE", file: "MoreRecords.lean", value: "−e", model: "EmlExt", lean: "EmlExt.finite (-Complex.exp 1)" },
  "111E1EE1111111E1EEEE11EEE11E1E1EEE1E1EE": { theorem: "Eml.MoreRecords.evalRpn_threeHalves", file: "MoreRecords.lean", value: "3/2", model: "EmlExt", lean: "EmlExt.finite ((3 : ℂ) / 2)" },
  "1111111E1EEEE11EEE11E1E1EEE11EE": { theorem: "Eml.MoreRecords.evalRpn_negThreeHalves", file: "MoreRecords.lean", value: "−3/2", model: "EmlExt", lean: "EmlExt.finite (-(3 : ℂ) / 2)" },
  "111E1EE1111111E1EEEE11EEE11E1E1EEE11EE1EE": { theorem: "Eml.MoreRecords.evalRpn_fiveHalves", file: "MoreRecords.lean", value: "5/2", model: "EmlExt", lean: "EmlExt.finite ((5 : ℂ) / 2)" },
  "111111111E1EEEE11EEE11E1E1EEE11EEE1EE11EE": { theorem: "Eml.MoreRecords.evalRpn_negFiveHalves", file: "MoreRecords.lean", value: "−5/2", model: "EmlExt", lean: "EmlExt.finite (-(5 : ℂ) / 2)" },
  "111111E1E1EEEE1EE1111E1E1EEE1EE": { theorem: "Eml.MoreRecords.evalRpn_twoPiI", file: "MoreRecords.lean", value: "+2πi (lower cut, no ln 0)", model: "C", lean: "(2 * Real.pi * Complex.I : ℂ)" },
  "11111E1E1EEEE11111E1E1EEEE1E1EE": { theorem: "Eml.MoreRecords.evalRpn_negTwoPiI", file: "MoreRecords.lean", value: "−2πi (lower cut, no ln 0)", model: "C", lean: "(-(2 * Real.pi * Complex.I) : ℂ)" },
  "111E111111E1EEEE11EEE1E1EEE": { theorem: "Eml.MoreRecords.evalRpn_negLn2", file: "MoreRecords.lean", value: "−ln 2", model: "EmlExt", lean: "EmlExt.finite (-Complex.log 2)" },
  "111E111111E1EEEE11EEE11E1E1EE1EEE11EE": { theorem: "Eml.MoreRecords.evalRpn_negTwoThirds", file: "MoreRecords.lean", value: "−2/3", model: "EmlExt", lean: "EmlExt.finite (-(2 : ℂ) / 3)" },
  "111E111111EEE1EE11E1EEE11E1E1EE1EEE11EE": { theorem: "Eml.MoreRecords.evalRpn_negTwoThirds_strict", file: "MoreRecords.lean", value: "−2/3 (no ln 0)", model: "C", lean: "(-(2 : ℂ) / 3 : ℂ)" },
  "11111111E1EEEE11E1E1EEE11EEE11E1E1EEE11EE": { theorem: "Eml.MoreRecords.evalRpn_negFiveThirds", file: "MoreRecords.lean", value: "−5/3", model: "EmlExt", lean: "EmlExt.finite (-(5 : ℂ) / 3)" },
};

/** Look up the machine-checked Lean 4 theorem for an exact RPN program, if one exists. */
export function leanTheoremForRpn(rpn: string): LeanTheoremRef | null {
  return Object.prototype.hasOwnProperty.call(LEAN_VERIFIED_THEOREMS, rpn)
    ? LEAN_VERIFIED_THEOREMS[rpn]
    : null;
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
