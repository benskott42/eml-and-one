import { rangeOf } from "./lowering";
import type { Node } from "./node";

/**
 * What is known about a node from how it was built, in one record per node.
 * A builder calls derive(op, out, a, b) once, and the rules below say which facts
 * the result has. A fact added here needs a rule for every operation in this file,
 * so a missing one can be seen. See docs/architecture-plan.md, step 1.
 */
export type Rational = { n: bigint; d: bigint };

/** The value is q·π ("real") or q·π·i ("imag"): a recorded multiple, not a float near one. */
export type Angle = { q: Rational; unit: "real" | "imag" };

/** What is known about a node's infinity/overflow status (replaces directedInfinity, poleSign, nonfiniteNode, maybeInfinite). */
export type InfinityFact = {
  /** Built from a ln 0, pole, or division by 0; an ∞ − ∞ here can be the value. Crosses the wire as `inf`. */
  maybe?: boolean;
  /** Float-nonfinite classification: a real pole (`sign`), a float overflow (finite exact value), or a directed infinity (`quarter`, `magnitude`). */
  kind?: "pole" | "overflow" | "directed";
  /** Sign of a real pole (`noteNonfinite`). */
  sign?: -1 | 1;
  /** Quarter turn (0: +∞, 1: +∞i, 2: −∞, 3: −∞i) for a directed infinity. */
  quarter?: number;
  /** Positive real infinity magnitude node for a directed infinity. */
  magnitude?: Node;
};

export type Facts = {
  angle?: Angle;
  /** The node is i (1) or −i (−1). */
  imaginaryUnit?: 1 | -1;
  infinity?: InfinityFact;
};

export type WireFacts = {
  inf?: 1;
};

export type Op = "add" | "sub" | "mul" | "div" | "neg";

const NONE: Facts = Object.freeze({});
const table = new WeakMap<Node, Facts>();

export function factsOf(node: Node): Facts {
  return table.get(node) ?? NONE;
}

/** Record facts on a node. Shared finite input leaves and proven integers carry no derived angle/unit facts. */
export function learn(node: Node, facts: Facts): Node {
  const prev = table.get(node);
  const next: Facts = { ...prev };
  if (node.type !== "input") {
    if (facts.angle && rangeOf(node).int === undefined) next.angle = facts.angle;
    if (facts.imaginaryUnit) next.imaginaryUnit = facts.imaginaryUnit;
  }
  if (facts.infinity) {
    next.infinity = { ...prev?.infinity, ...facts.infinity };
  }
  if (next.angle || next.imaginaryUnit || next.infinity) table.set(node, next);
  return node;
}

/** Pack facts that cross the worker wire onto a wire token. */
export function packFacts(node: Node, target: WireFacts): void {
  if (factsOf(node).infinity?.maybe) target.inf = 1;
}

/** Restore facts that crossed the worker wire onto an unpacked node. */
export function unpackFacts(node: Node, source: WireFacts): void {
  if (source.inf) learn(node, { infinity: { maybe: true } });
}

export function mayBeInfinite(node: Node): boolean {
  return factsOf(node).infinity?.maybe === true;
}

export function markInfiniteSource(node: Node): Node {
  return learn(node, { infinity: { maybe: true } });
}

export function markMaybeInfinite(out: Node, ...from: Node[]): Node {
  if (from.some((node) => mayBeInfinite(node))) learn(out, { infinity: { maybe: true } });
  return out;
}

/** A typed infinity. 0 · ∞ is indeterminate even when the infinity was not a division. */
export function noteNonfinite(node: Node, sign: -1 | 1 = 1): Node {
  return learn(node, { infinity: { kind: "pole", sign } });
}

/**
 * A finite overflow such as exp(800). The node is non-finite in float, but it is
 * not a pole: exp(800) − exp(800) is 0. exp of this node is a pole, because
 * exp(exp(800)) has already left any finite range.
 */
export function noteOverflow(node: Node): Node {
  return learn(node, { infinity: { kind: "overflow" } });
}

export function isNonfiniteNode(node: Node): boolean {
  const kind = factsOf(node).infinity?.kind;
  return kind === "pole" || kind === "overflow";
}

export function recordedPoleSign(node: Node): -1 | 1 | null {
  const inf = factsOf(node).infinity;
  return inf?.kind === "pole" ? (inf.sign ?? null) : null;
}

export function recordedDirection(node: Node): { magnitude: Node; quarter: number } | null {
  const inf = factsOf(node).infinity;
  if (inf?.kind === "directed" && inf.magnitude !== undefined && inf.quarter !== undefined) {
    return { magnitude: inf.magnitude, quarter: inf.quarter };
  }
  return null;
}

export function rational(n: bigint, d: bigint): Rational | null {
  if (d === BigInt(0)) return null;
  if (d < BigInt(0)) {
    n = -n;
    d = -d;
  }
  let x = n < BigInt(0) ? -n : n;
  let y = d;
  while (y !== BigInt(0)) {
    const next = x % y;
    x = y;
    y = next;
  }
  return { n: n / x, d: d / x };
}

/** The node's integer value, when it is a proven integer and not an angle. */
function integerOf(node: Node): bigint | null {
  if (factsOf(node).angle) return null;
  const n = rangeOf(node).int;
  return n === undefined ? null : n;
}

function scale(angle: Angle, n: bigint, d: bigint): Angle | null {
  const q = rational(angle.q.n * n, angle.q.d * d);
  return q ? { q, unit: angle.unit } : null;
}

function negate(angle: Angle): Angle {
  return { q: { n: -angle.q.n, d: angle.q.d }, unit: angle.unit };
}

/** q·π turned by ±i is ±q·π·i, and q·π·i turned by ±i is ∓q·π. */
function turn(angle: Angle, sign: 1 | -1): Angle {
  const flip = angle.unit === "imag" ? -sign : sign;
  const q = flip === 1 ? angle.q : { n: -angle.q.n, d: angle.q.d };
  return { q, unit: angle.unit === "imag" ? "real" : "imag" };
}

function angleOf(op: Op, a: Node, b: Node | undefined): Angle | null {
  const left = factsOf(a).angle;
  if (op === "neg") return left ? negate(left) : null;
  if (!b) return null;
  const right = factsOf(b).angle;
  if (op === "add" || op === "sub") {
    if (left && right) {
      if (left.unit !== right.unit) return null;
      const sign = op === "add" ? BigInt(1) : BigInt(-1);
      const q = rational(left.q.n * right.q.d + sign * right.q.n * left.q.d, left.q.d * right.q.d);
      return q ? { q, unit: left.unit } : null;
    }
    if (left && integerOf(b) === BigInt(0)) return left;
    if (right && integerOf(a) === BigInt(0)) return op === "add" ? right : negate(right);
    return null;
  }
  if (op === "mul") {
    const ia = integerOf(a);
    const ib = integerOf(b);
    if (left && ib !== null) return scale(left, ib, BigInt(1));
    if (right && ia !== null) return scale(right, ia, BigInt(1));
    const ua = factsOf(a).imaginaryUnit;
    const ub = factsOf(b).imaginaryUnit;
    if (left && ub) return turn(left, ub);
    if (right && ua) return turn(right, ua);
    return null;
  }
  const under = integerOf(b);
  if (left && under !== null && under !== BigInt(0)) return scale(left, BigInt(1), under);
  const ub = factsOf(b).imaginaryUnit;
  if (left && ub) return turn(left, ub === 1 ? -1 : 1);
  return null;
}

function unitOf(op: Op, a: Node, b: Node | undefined): 1 | -1 | undefined {
  const ua = factsOf(a).imaginaryUnit;
  if (op === "neg") return ua ? (ua === 1 ? -1 : 1) : undefined;
  if (!b) return undefined;
  const ub = factsOf(b).imaginaryUnit;
  const ia = integerOf(a);
  const ib = integerOf(b);
  if (op === "add") {
    if (ua && ib === BigInt(0)) return ua;
    if (ub && ia === BigInt(0)) return ub;
    return undefined;
  }
  if (op === "sub") {
    if (ua && ib === BigInt(0)) return ua;
    if (ub && ia === BigInt(0)) return ub === 1 ? -1 : 1;
    return undefined;
  }
  if (op === "mul") {
    if (ua && (ib === BigInt(1) || ib === BigInt(-1))) return ib === BigInt(1) ? ua : ua === 1 ? -1 : 1;
    if (ub && (ia === BigInt(1) || ia === BigInt(-1))) return ia === BigInt(1) ? ub : ub === 1 ? -1 : 1;
    return undefined;
  }
  if (ua && (ib === BigInt(1) || ib === BigInt(-1))) return ib === BigInt(1) ? ua : ua === 1 ? -1 : 1;
  return undefined;
}

/** Record on `out` the facts that follow from the operation and its operands. Returns `out`. */
export function derive(op: Op, out: Node, a: Node, b?: Node): Node {
  const angle = angleOf(op, a, b);
  const unit = unitOf(op, a, b);
  if (!angle && !unit) return out;
  return learn(out, { ...(angle ? { angle } : {}), ...(unit ? { imaginaryUnit: unit } : {}) });
}
