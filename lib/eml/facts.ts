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

export type Facts = {
  angle?: Angle;
  /** The node is i (1) or −i (−1). */
  imaginaryUnit?: 1 | -1;
};

export type Op = "add" | "sub" | "mul" | "div" | "neg";

const NONE: Facts = Object.freeze({});
const table = new WeakMap<Node, Facts>();

export function factsOf(node: Node): Facts {
  return table.get(node) ?? NONE;
}

/** Record facts on a node. Shared input leaves and proven integers carry no derived facts. */
export function learn(node: Node, facts: Facts): Node {
  if (node.type === "input") return node;
  const next: Facts = { ...table.get(node) };
  if (facts.angle && rangeOf(node).int === undefined) next.angle = facts.angle;
  if (facts.imaginaryUnit) next.imaginaryUnit = facts.imaginaryUnit;
  if (next.angle || next.imaginaryUnit) table.set(node, next);
  return node;
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
