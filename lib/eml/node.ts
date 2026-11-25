import { type C, C1, eml } from "./complex";
import { dependsOnUnverified, isUnverified, noteDependsUnverified } from "./facts";

/**
 * A circuit in the grammar S → 1 | var | input | eml(S, S).
 *
 * `E` hash-conses on the child ids, so identical subtrees are one node.
 * That is structural common-subexpression elimination, not an algebraic
 * rewrite. Input nodes are only numbers the user typed; library programs
 * are built from 1, variables, and eml.
 *
 * Gate counts, each labeled by the caller:
 * - tree gates: eml nodes in the fully expanded tree (BigInt DP)
 * - RPN length: 2 × tree gates + 1 (one token per leaf and per eml)
 * - DAG gates: distinct eml nodes after hash-consing
 * - depth: longest eml path in the DAG
 */
export type Node =
  | { type: "one"; id: number }
  | { type: "var"; name: string; id: number }
  | { type: "input"; value: C; label: string; id: number }
  | { type: "eml"; a: Node; b: Node; id: number };

let nextId = 1;

export const ONE: Node = Object.freeze({ type: "one", id: nextId++ });

const vars = new Map<string, Node>();
const inputs = new Map<string, WeakRef<Node>>();
const cons = new Map<string, WeakRef<Node>>();
let circuitDepth = 0;
const isolateHooks: Array<() => void> = [];

/** Side tables in other modules drop their per-expression entries here. */
export function onCircuitIsolate(fn: () => void): void {
  isolateHooks.push(fn);
}
const released = new FinalizationRegistry<string>((key) => {
  const bucket = key.startsWith("in\0") ? inputs : cons;
  const current = bucket.get(key);
  if (!current || current.deref() === undefined) bucket.delete(key);
});

export function V(name: string): Node {
  const hit = vars.get(name);
  if (hit) return hit;
  const node: Node = Object.freeze({ type: "var", name, id: nextId++ });
  vars.set(name, node);
  return node;
}

function inputKey(value: C, label: string): string {
  const re = Object.is(value.re, -0) ? "-0" : String(value.re);
  const im = Object.is(value.im, -0) ? "-0" : String(value.im);
  return `${label}\0${re}\0${im}`;
}

/** A number the user typed, as a bound leaf. Not a rewritten subexpression. */
export function input(value: C, label: string): Node {
  // +∞ and −∞ are not the same leaf. Interning them made ∞ − ∞ the zero program.
  if (Number.isFinite(value.re) && Number.isFinite(value.im)) {
    const key = `in\0${inputKey(value, label)}`;
    const hit = inputs.get(key)?.deref();
    if (hit) return hit;
    const node: Node = Object.freeze({ type: "input", value, label, id: nextId++ });
    inputs.set(key, new WeakRef(node));
    released.register(node, key);
    return node;
  }
  return Object.freeze({ type: "input", value, label, id: nextId++ });
}

/**
 * Float64 rotSub leaves the exact strip outside (−71π, 71π).
 * The top end underflows: [71π, 73π) is barely subnormal and [73π, 75π)
 * is degraded. Past 75π the rotated exponential underflows to 0.
 * Lowering scales before using the rotation on an unknown range.
 */
export const ROT_IM_MIN = -71 * Math.PI;
export const ROT_IM_MAX = 73 * Math.PI;

/**
 * Start a top-level expression. Nested builds keep the table, so a circuit
 * shares its own subexpressions, and a later expression cannot reuse those
 * nodes or the ranges hanging off them.
 */
export function isolateCircuit<T>(build: () => T): T {
  const outer = circuitDepth === 0;
  if (outer) {
    cons.clear();
    for (const hook of isolateHooks) hook();
  }
  circuitDepth += 1;
  try {
    return build();
  } finally {
    circuitDepth -= 1;
  }
}

/** Hash-consed eml. The same children always return the same node inside one expression. */
export function E(a: Node, b: Node): Node {
  const key = `${a.id},${b.id}`;
  const hit = cons.get(key)?.deref();
  if (hit) {
    if (dependsOnUnverified(a) || dependsOnUnverified(b)) noteDependsUnverified(hit);
    return hit;
  }
  const node: Node = Object.freeze({ type: "eml", id: nextId++, a, b });
  if (dependsOnUnverified(a) || dependsOnUnverified(b)) noteDependsUnverified(node);
  cons.set(key, new WeakRef(node));
  released.register(node, key);
  return node;
}

export class EmlError extends Error {}

export class EmlLimitError extends EmlError {}

export type EvalBudget = {
  maxNodes?: number;
  deadline?: number;
};

const DEFAULT_MAX_NODES = 200_000;

export const SINGULAR_LN0 = "uses ln 0 = −∞";
export const SINGULAR_INDET = "indeterminate (∞ − ∞ or 0 · ∞)";
export const SINGULAR_RANGE = "out of float range / overflow";
export const SINGULAR_NONFINITE = "passed through a non-finite value";
/** The gates ran. Their absolute error is larger than this result, so it is not a value to trust. */
export const SINGULAR_PRECISION = "low absolute precision";
/** tan of a float near an odd multiple of π/2. The digits are not a value. */
export const SINGULAR_POLE = "near a pole";
/** sin, cos, or tan of a real whose magnitude is too large to reduce. */
export const SINGULAR_TRIG = "argument too large to reduce";

type PrecisionNote =
  | { kind: "asinh"; arg: Node }
  | { kind: "add"; left: Node; right: Node }
  | { kind: "pole"; arg: Node }
  | { kind: "trig"; arg: Node };

const precisionNotes = new WeakMap<Node, PrecisionNote>();

/** Mark a circuit whose float value is untrustworthy for a small unknown input. Evaluation still returns the gates. */
export function notePrecision(node: Node, note: PrecisionNote): void {
  precisionNotes.set(node, note);
}

export function precisionNoteOf(node: Node): PrecisionNote | undefined {
  return precisionNotes.get(node);
}

/** Argument of sin, cos, or tan. tan is stored as a pole note. */
export function trigArg(node: Node): Node | null {
  const note = precisionNotes.get(node);
  if (!note || (note.kind !== "trig" && note.kind !== "pole")) return null;
  return note.arg;
}

/**
 * A function the library replaced by a short series. The next term is past
 * the 480-digit cap. A later cancellation that makes the whole result 0 is
 * not a certified zero: the dropped term could have been the answer.
 */
const seriesShortcuts = new WeakMap<Node, string>();
const seriesErrorExps = new WeakMap<Node, number>();

export function markSeriesShortcut(node: Node, note = "series shortcut"): Node {
  seriesShortcuts.set(node, note);
  return node;
}

/** Record the exponent (base 10) of the dropped error term for a crude linear series shortcut. */
export function markSeriesError(node: Node, errExp: number): Node {
  const prev = seriesErrorExps.get(node);
  if (prev === undefined || errExp > prev) seriesErrorExps.set(node, errExp);
  return node;
}

export function seriesErrorExp(node: Node): number | undefined {
  return seriesErrorExps.get(node);
}

/** Largest dropped-term exponent among crude series shortcuts reachable from `root`, if any. */
export function maxSeriesErrorExp(root: Node): number | undefined {
  let max: number | undefined;
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    const err = seriesErrorExps.get(node);
    if (err !== undefined && (max === undefined || err > max)) max = err;
    if (node.type === "eml") {
      if (node.a) stack.push(node.a);
      if (node.b) stack.push(node.b);
    }
  }
  return max;
}

export function isSeriesShortcut(node: Node): boolean {
  return seriesShortcuts.has(node);
}

export function seriesShortcutText(node: Node): string | undefined {
  return seriesShortcuts.get(node);
}

export function seriesShortcutNoteFrom(root: Node): string | null {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    const note = seriesShortcuts.get(node);
    if (note) return note;
    if (node.type === "eml") {
      if (node.a) stack.push(node.a);
      if (node.b) stack.push(node.b);
    }
  }
  return null;
}

export function usesSeriesShortcut(root: Node): boolean {
  return seriesShortcutNoteFrom(root) !== null;
}

export type EvalReport = {
  value: C;
  /** Set when a singularity changes the result. A finite value that merely passed through ln 0 is not singular. */
  singular: string | null;
  /** True when some eml logged 0, even if that cancelled in a finite result. */
  touchedLn0: boolean;
  /** True when a float overflowed, even if a later step looks finite again. */
  overflowed: boolean;
  /**
   * True when exp of a finite, nonzero input underflowed to 0 or a subnormal.
   * exp(−∞) from ln 0 is the real value 0, not this flag.
   */
  underflowed: boolean;
  /** The float result landed on the branch cut, or within a few ulps of it. */
  nearCut: boolean;
  /** The circuit dropped a term. The number is not a result. */
  unverified?: boolean;
};

function zeroC(v: C): boolean {
  return (v.re === 0 || Object.is(v.re, -0)) && (v.im === 0 || Object.is(v.im, -0));
}

function finiteC(v: C): boolean {
  return Number.isFinite(v.re) && Number.isFinite(v.im);
}

/** On ±π, or close enough that the bank is a rounding choice. */
function nearBranchCut(value: C): boolean {
  if (!Number.isFinite(value.re) || !Number.isFinite(value.im)) return false;
  return Math.abs(Math.abs(value.im) - Math.PI) <= 32 * Number.EPSILON * Math.PI;
}

/**
 * exp(z) lost its magnitude in float64. The input has to be finite and
 * nonzero: exp(0) is 1, and exp(−∞) from ln 0 is a real 0.
 */
export function expUnderflows(input: C): boolean {
  if (!Number.isFinite(input.re) || !Number.isFinite(input.im)) return false;
  const reZero = input.re === 0 || Object.is(input.re, -0);
  const imZero = input.im === 0 || Object.is(input.im, -0);
  if (reZero && imZero) return false;
  const mag = Math.exp(input.re);
  // 2^(−1022) is the smallest normal float64. Anything smaller has underflowed.
  return mag === 0 || mag < 2 ** -1022;
}

export function evaluateReport(root: Node, env: Record<string, C> = {}, budget: EvalBudget = {}): EvalReport {
  const report = evaluateReportAt(root, env, budget);
  // A value read off a node refused below the root is not certified either.
  // An undefined result stays: (1 + 1/0) − 1/0 is still the indeterminate ∞ − ∞.
  if (report.unverified || (Number.isNaN(report.value.re) && Number.isNaN(report.value.im)) || !dependsOnUnverified(root)) return report;
  return { value: { re: Number.NaN, im: Number.NaN }, singular: null, touchedLn0: false, overflowed: false, underflowed: false, nearCut: false, unverified: true };
}

function evaluateReportAt(root: Node, env: Record<string, C>, budget: EvalBudget): EvalReport {
  if (isUnverified(root)) {
    return {
      value: { re: Number.NaN, im: Number.NaN },
      singular: null,
      touchedLn0: false,
      overflowed: false,
      underflowed: false,
      nearCut: false,
      unverified: true,
    };
  }
  const maxNodes = budget.maxNodes ?? DEFAULT_MAX_NODES;
  const deadline = budget.deadline ?? 0;
  const memo = new Map<Node, C>();
  const why = new Map<Node, string | null>();
  const logged = new Map<Node, boolean>();
  const overflowed = new Map<Node, boolean>();
  const underflowed = new Map<Node, boolean>();
  const rangeBorn = new Map<Node, boolean>();
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  let steps = 0;

  while (stack.length) {
    if ((++steps & 63) === 0) {
      if (steps > maxNodes) {
        throw new EmlLimitError("This circuit is too large to evaluate.");
      }
      if (deadline && performance.now() > deadline) {
        throw new EmlLimitError("Evaluation timed out.");
      }
    }
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n) throw new EmlError("Could not evaluate this circuit.");
    if (memo.has(n)) continue;

    if (n.type === "one") {
      memo.set(n, C1);
      why.set(n, null);
      logged.set(n, false);
      overflowed.set(n, false);
      underflowed.set(n, false);
      rangeBorn.set(n, false);
      continue;
    }
    if (n.type === "input") {
      memo.set(n, n.value);
      why.set(n, null);
      logged.set(n, false);
      overflowed.set(n, false);
      underflowed.set(n, false);
      rangeBorn.set(n, false);
      continue;
    }
    if (n.type === "var") {
      if (!Object.hasOwn(env, n.name)) {
        throw new EmlError(`This expression needs a value for ${n.name}.`);
      }
      const bound = env[n.name];
      if (!bound) throw new EmlError(`This expression needs a value for ${n.name}.`);
      memo.set(n, bound);
      why.set(n, null);
      logged.set(n, false);
      overflowed.set(n, false);
      underflowed.set(n, false);
      rangeBorn.set(n, false);
      continue;
    }

    if (!n.a || !n.b) throw new EmlError("Could not evaluate this circuit.");

    if (!frame.seen) {
      if (visiting.has(n)) throw new EmlError("Could not evaluate this circuit.");
      visiting.add(n);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }

    visiting.delete(n);
    const a = memo.get(n.a);
    const b = memo.get(n.b);
    if (a === undefined || b === undefined) throw new EmlError("Could not evaluate this circuit.");
    const childLog = logged.get(n.a) === true || logged.get(n.b) === true || zeroC(b);
    const childOverflow = overflowed.get(n.a) === true || overflowed.get(n.b) === true;
    const childUnder = underflowed.get(n.a) === true || underflowed.get(n.b) === true;
    // sin, cos, and tan of ±∞ are undefined. The exp formula otherwise returns an infinity.
    const angle = trigArg(n);
    const angleValue = angle ? memo.get(angle) : undefined;
    const angleInfinite = !!angleValue && (!Number.isFinite(angleValue.re) || !Number.isFinite(angleValue.im));
    const value = angleInfinite ? { re: NaN, im: NaN } : eml(a, b);
    const nan = Number.isNaN(value.re) || Number.isNaN(value.im);
    // Logging 0 at this gate is a real pole. An infinity born from two finite
    // inputs that are not that pole is float overflow, even if some other
    // gate in the circuit logged 0. A later ∞ − ∞ of those is out of range.
    const loggedHere = zeroC(b);
    const rangeHere =
      rangeBorn.get(n.a) === true ||
      rangeBorn.get(n.b) === true ||
      (finiteC(a) && finiteC(b) && !loggedHere && !finiteC(value));
    let singular: string | null = null;
    if (nan) {
      // ∞ + iπ is a magnitude that overflowed and then picked up a log's
      // argument. Real ∞ − ∞ of two poles stays indeterminate.
      const messy = (value: C) => !finiteC(value) && Number.isFinite(value.im) && value.im !== 0 && !Object.is(value.im, -0);
      const childRange = why.get(n.a) === SINGULAR_RANGE || why.get(n.b) === SINGULAR_RANGE;
      singular = angleInfinite || !(rangeHere || childRange || messy(a) || messy(b)) ? SINGULAR_INDET : SINGULAR_RANGE;
    }
    // An infinity born from finite inputs is overflow, even if another gate logged 0.
    // ln 0 itself is the label only when this infinity was not that overflow.
    else if (!finiteC(value)) singular = rangeHere ? SINGULAR_RANGE : childLog ? SINGULAR_LN0 : why.get(n.a) || why.get(n.b) || SINGULAR_NONFINITE;
    memo.set(n, value);
    why.set(n, singular);
    logged.set(n, childLog);
    rangeBorn.set(n, rangeHere);
    const fromLn0 = childLog && !nan && !childOverflow;
    overflowed.set(n, childOverflow || (!finiteC(value) && !fromLn0));
    underflowed.set(n, childUnder || expUnderflows(a));
  }

  const out = memo.get(root);
  if (!out) throw new EmlError("Could not evaluate this circuit.");
  let singular = why.get(root) ?? null;
  // A scaled add can rebuild its operands, so a noted term need not be a gate
  // here. Evaluate it on its own: without that, 2x + 1 near x = −1/2 lost the
  // low-precision flag that x + 1 near x = −1 gets.
  const flag = precisionMessage(root, (n) => {
    const hit = memo.get(n);
    if (hit !== undefined) return hit;
    try {
      return evaluateReport(n, env, budget).value;
    } catch {
      return undefined;
    }
  });
  if (flag === SINGULAR_POLE) singular = flag;
  else if (!singular && flag) singular = flag;
  return {
    value: out,
    singular,
    touchedLn0: logged.get(root) === true,
    overflowed: overflowed.get(root) === true,
    underflowed: underflowed.get(root) === true,
    nearCut: nearBranchCut(out),
  };
}

/**
 * A rebuilt press string does not carry this note: it lives beside the node,
 * not in the gates. Callers that copy the circuit by RPN lose the flag.
 */
export function precisionMessage(root: Node, valueOf: (n: Node) => C | undefined): string | null {
  const note = precisionNotes.get(root);
  if (!note) return null;
  if (note.kind === "pole" || note.kind === "trig") {
    const arg = valueOf(note.arg);
    if (!arg || !finiteC(arg) || Math.abs(arg.im) > 1) return null;
    if (note.kind === "pole") {
      const half = Math.PI / 2;
      const n = Math.round(arg.re / half);
      // tan(π/2) and tan(3π/2) are the same pole. The check uses the value, so a
      // product whose range is unknown is still flagged.
      if (n % 2 !== 0 && Math.abs(arg.re - n * half) < 1e-6) return SINGULAR_POLE;
    }
    if (Math.abs(arg.re) >= 1e6) return SINGULAR_TRIG;
    return null;
  }
  if (note.kind === "asinh") {
    const arg = valueOf(note.arg);
    if (!arg || !finiteC(arg)) return null;
    const mag = Math.hypot(arg.re, arg.im);
    // Above about 10^(−12), asinh z ≈ z in float. Below that the identity underflows and is flagged.
    return mag > 0 && mag < 1e-12 ? SINGULAR_PRECISION : null;
  }
  if (note.kind !== "add") return null;
  const left = valueOf(note.left);
  const right = valueOf(note.right);
  const value = valueOf(root);
  if (!left || !right || !value || !finiteC(value)) return null;
  if (!(Math.hypot(value.re, value.im) < 1e-8)) return null;
  const zero = (part: C) => Math.hypot(part.re, part.im) === 0;
  return zero(left) && zero(right) ? null : SINGULAR_PRECISION;
}

export function evaluate(root: Node, env: Record<string, C> = {}, budget: EvalBudget = {}): C {
  return evaluateReport(root, env, budget).value;
}

/** True when every leaf is 1 or a variable. User-typed inputs fail this. */
export function isPure(root: Node): boolean {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    if (n.type === "input") return false;
    if (n.type === "eml") {
      if (!n.a || !n.b) return false;
      stack.push(n.a, n.b);
    }
  }
  return true;
}

export type CircuitStats = {
  treeGates: bigint;
  rpnLength: bigint;
  dagGates: number;
  depth: number;
};

function walkShape(root: Node): { tree: bigint; depth: number; dag: number } {
  const treeOf = new Map<number, bigint>();
  const depthOf = new Map<number, number>();
  const visiting = new Set<number>();
  let dag = 0;
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];

  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n || n.type !== "eml" || !n.a || !n.b) {
      if (n) {
        treeOf.set(n.id, BigInt(0));
        depthOf.set(n.id, 0);
      }
      continue;
    }
    if (treeOf.has(n.id)) continue;
    if (!frame.seen) {
      if (visiting.has(n.id)) throw new EmlError("Could not evaluate this circuit.");
      visiting.add(n.id);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    visiting.delete(n.id);
    const lt = treeOf.get(n.a.id) ?? BigInt(0);
    const rt = treeOf.get(n.b.id) ?? BigInt(0);
    const ld = depthOf.get(n.a.id) ?? 0;
    const rd = depthOf.get(n.b.id) ?? 0;
    treeOf.set(n.id, lt + rt + BigInt(1));
    depthOf.set(n.id, 1 + Math.max(ld, rd));
    dag += 1;
  }

  return {
    tree: treeOf.get(root.id) ?? BigInt(0),
    depth: depthOf.get(root.id) ?? 0,
    dag,
  };
}

/** Tree gates, RPN length, DAG gates, and depth. */
export function circuitStats(root: Node): CircuitStats {
  const shape = walkShape(root);
  return {
    treeGates: shape.tree,
    rpnLength: shape.tree * BigInt(2) + BigInt(1),
    dagGates: shape.dag,
    depth: shape.depth,
  };
}

function walkPost<T>(root: Node, visit: (n: Node, a: T | null, b: T | null) => T): T {
  const memo = new Map<Node, T>();
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n) throw new EmlError("Could not evaluate this circuit.");
    if (memo.has(n)) continue;
    if (n.type !== "eml" || !n.a || !n.b) {
      memo.set(n, visit(n, null, null));
      continue;
    }
    if (!frame.seen) {
      if (visiting.has(n)) throw new EmlError("Could not evaluate this circuit.");
      visiting.add(n);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    visiting.delete(n);
    const a = memo.get(n.a);
    const b = memo.get(n.b);
    if (a === undefined || b === undefined) throw new EmlError("Could not evaluate this circuit.");
    memo.set(n, visit(n, a, b));
  }
  const out = memo.get(root);
  if (out === undefined) throw new EmlError("Could not evaluate this circuit.");
  return out;
}

export function substitute(root: Node, bindings: Record<string, Node>): Node {
  return walkPost(root, (n, a, b) => {
    if (n.type === "var" && Object.prototype.hasOwnProperty.call(bindings, n.name)) {
      const bound = bindings[n.name];
      if (!bound) throw new EmlError(`This expression needs a value for ${n.name}.`);
      return bound;
    }
    if (n.type === "eml") {
      if (!a || !b) throw new EmlError("Could not evaluate this circuit.");
      return E(a, b);
    }
    return n;
  });
}

/** Nested eml(…) text when it is short enough to read. */
export function describe(node: Node, budget = 96): string | null {
  try {
    if (circuitStats(node).treeGates > BigInt(budget)) return null;
  } catch {
    return null;
  }
  try {
    return walkPost(node, (n, a, b) => {
      if (n.type === "one") return budget >= 1 ? "1" : null;
      if (n.type === "var") return n.name.length <= budget ? n.name : null;
      if (n.type === "input") return n.label.length <= budget ? n.label : null;
      if (a === null || b === null) return null;
      const text = `eml(${a}, ${b})`;
      return text.length > budget ? null : text;
    });
  } catch {
    return null;
  }
}

/**
 * Expanded RPN. `E` is eml. Returns null when the expansion is longer
 * than `budget` or the circuit is cyclic. The length is checked from the
 * tree-gate count first, so a shared tower does not get expanded.
 */
export function rpnTokens(node: Node, budget = 48): string[] | null {
  let tree = BigInt(0);
  try {
    tree = circuitStats(node).treeGates;
  } catch {
    return null;
  }
  if (tree * BigInt(2) + BigInt(1) > BigInt(budget)) return null;

  const tokens: string[] = [];
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: node, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n) return null;
    if (!frame.seen) {
      if (n.type !== "eml" || !n.a || !n.b) {
        tokens.push(n.type === "one" ? "1" : n.type === "var" ? n.name : n.type === "input" ? n.label : "");
        if (!tokens[tokens.length - 1] || tokens.length > budget) return null;
        continue;
      }
      if (visiting.has(n)) return null;
      visiting.add(n);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    visiting.delete(n);
    tokens.push("E");
    if (tokens.length > budget) return null;
  }
  return tokens;
}

/** Parse an RPN program of 1, x, y, and E back into a hash-consed circuit. */
export function nodeFromRpn(tokens: readonly string[]): Node {
  const stack: Node[] = [];
  for (const token of tokens) {
    if (token === "1") stack.push(ONE);
    else if (token === "x") stack.push(V("x"));
    else if (token === "y") stack.push(V("y"));
    else if (token === "E") {
      const b = stack.pop();
      const a = stack.pop();
      if (!a || !b) throw new EmlError("The RPN program is missing a value.");
      stack.push(E(a, b));
    } else {
      throw new EmlError(`Unknown RPN token ${token}.`);
    }
  }
  if (stack.length !== 1) throw new EmlError("The RPN program did not leave one value.");
  return stack[0];
}
