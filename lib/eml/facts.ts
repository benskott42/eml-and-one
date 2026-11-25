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

/** An exact terminating decimal n·10^(−s), with s >= 0. */
export type ExactDecimal = { n: bigint; s: number };

export const DECIMAL_SCALE_MAX = 1000;

/**
 * Exact integer value known for a node (replaces provenBig, markedExactInt, Range.int).
 * When `marked` is true, exact evaluation reads `value` directly.
 */
export type IntegerFact = {
  value: bigint;
  marked?: boolean;
};

/**
 * Refused-node marks (replaces unverifiedNodes, exactUnsureNodes, dependsCache in node.ts).
 * `dependsUnverified` is propagated at E(a, b) build time so dependsOnUnverified is O(1).
 */
export type RefusedFact = {
  /** A result that dropped a term; refused in both exact and float modes. Crosses the wire as `unver`. */
  unverified?: boolean;
  /** Exact mode cannot certify this value; float keeps its own. Crosses the wire as `xu`. */
  exactUnsure?: boolean;
  /** Built on an unverified descendant. */
  dependsUnverified?: boolean;
};

export type Facts = {
  angle?: Angle;
  /** The node is i (1) or −i (−1). */
  imaginaryUnit?: 1 | -1;
  infinity?: InfinityFact;
  /** Exact terminating decimal n·10^(−s); null means poisoned by conflicting values on the same node. */
  decimal?: ExactDecimal | null;
  /** Exact integer value; `marked: true` means exact evaluation reads it directly. */
  integer?: IntegerFact;
  /** Refusal marks for exact and float certification. */
  refused?: RefusedFact;
};

export type WireFacts = {
  inf?: 1;
  int?: string;
  pint?: string;
  unver?: 1;
  xu?: 1;
};

export type Op = "add" | "sub" | "mul" | "div" | "neg";

const NONE: Facts = Object.freeze({});
const table = new WeakMap<Node, Facts>();

export function factsOf(node: Node): Facts {
  return table.get(node) ?? NONE;
}

function normalizeDecimal(value: ExactDecimal): ExactDecimal | null {
  let { n, s } = value;
  if (s < 0) return null;
  if (n === BigInt(0)) return { n: BigInt(0), s: 0 };
  while (s > 0 && n % BigInt(10) === BigInt(0)) {
    n /= BigInt(10);
    s -= 1;
  }
  if (s > DECIMAL_SCALE_MAX) return null;
  // Cap mantissa width so repeated products/powers cannot build huge BigInts.
  const digits = (n < BigInt(0) ? -n : n).toString().length;
  if (digits > DECIMAL_SCALE_MAX + 20) return null;
  return { n, s };
}

function sameDecimal(a: ExactDecimal, b: ExactDecimal): boolean {
  const s = Math.max(a.s, b.s);
  return a.n * BigInt(10) ** BigInt(s - a.s) === b.n * BigInt(10) ** BigInt(s - b.s);
}

/** Record facts on a node. Shared finite input leaves and proven integers carry no derived angle/unit/decimal facts. */
export function learn(node: Node, facts: Facts): Node {
  const prev = table.get(node);
  const next: Facts = { ...prev };
  if (node.type !== "input") {
    if (facts.angle && provenInteger(node) === undefined && facts.integer === undefined) next.angle = facts.angle;
    if (facts.imaginaryUnit) next.imaginaryUnit = facts.imaginaryUnit;
    if (facts.decimal !== undefined && !isUnverified(node) && !isExactUnsure(node)) {
      if (facts.decimal === null || prev?.decimal === null) {
        next.decimal = null;
      } else {
        const norm = normalizeDecimal(facts.decimal);
        if (norm) {
          if (prev?.decimal !== undefined && !sameDecimal(prev.decimal, norm)) next.decimal = null;
          else next.decimal = norm;
        }
      }
    }
  }
  if (facts.infinity) {
    next.infinity = { ...prev?.infinity, ...facts.infinity };
  }
  if (facts.integer) {
    next.integer = {
      value: facts.integer.value,
      ...(prev?.integer?.marked || facts.integer.marked ? { marked: true } : {}),
    };
  }
  if (facts.refused) {
    next.refused = { ...prev?.refused, ...facts.refused };
  }
  if (next.angle || next.imaginaryUnit || next.infinity || next.decimal !== undefined || next.integer || next.refused) {
    table.set(node, next);
  }
  return node;
}

/** A result that dropped a term. The screen says it could not verify, in either mode. */
export function markUnverified(node: Node): Node {
  return learn(node, { refused: { unverified: true, dependsUnverified: true } });
}

export function isUnverified(node: Node): boolean {
  return factsOf(node).refused?.unverified === true;
}

/** Record that `node` has an unverified descendant (propagated at E(a, b) build time). */
export function noteDependsUnverified(node: Node): Node {
  return learn(node, { refused: { dependsUnverified: true } });
}

/**
 * True when the circuit uses a node marked unverified anywhere, not only at its root.
 * Propagated at build time in E(a, b) so this check is O(1).
 */
export function dependsOnUnverified(node: Node): boolean {
  const r = factsOf(node).refused;
  return r?.unverified === true || r?.dependsUnverified === true;
}

/** Exact mode cannot certify this node's value; float mode still shows its own. */
export function markExactUnsure(node: Node): Node {
  return learn(node, { refused: { exactUnsure: true } });
}

export function isExactUnsure(node: Node): boolean {
  return factsOf(node).refused?.exactUnsure === true;
}

/** The integer a node was built as. `ONE` is always 1. */
export function provenInteger(node: Node): bigint | undefined {
  if (node.type === "one") return BigInt(1);
  return factsOf(node).integer?.value;
}

/** Record that `node` was built as the exact integer `value`. */
export function noteProvenInt(node: Node, value: bigint): Node {
  return learn(node, { integer: { value } });
}

/** Remove any recorded integer fact from `node` (e.g. when a wider incompatible range is attached). */
export function clearProvenInt(node: Node): void {
  const prev = table.get(node);
  if (!prev || prev.integer === undefined) return;
  const next: Facts = { ...prev };
  delete next.integer;
  if (next.angle || next.imaginaryUnit || next.infinity || next.decimal !== undefined) table.set(node, next);
  else table.delete(node);
}

/** Exact evaluation reads this integer directly. The float value stays the rounded one. */
export function isMarkedExactInt(node: Node): boolean {
  return factsOf(node).integer?.marked === true;
}

/** Record an exact integer that exact evaluation reads directly. */
export function noteMarkedExactInt(node: Node, value: bigint): Node {
  return learn(node, { integer: { value, marked: true } });
}

/** Exact terminating decimal of a node, or null if unknown or poisoned. */
export function exactDecimalOf(node: Node): ExactDecimal | null {
  const known = factsOf(node).decimal;
  if (known !== undefined) return known;
  if (isUnverified(node) || isExactUnsure(node)) return null;
  const int = provenInteger(node);
  return int === undefined ? null : { n: int, s: 0 };
}

/** Record an exact decimal on `node`, poisoning if a conflicting value was already recorded. */
export function noteExactDecimal(node: Node, value: ExactDecimal): Node {
  return learn(node, { decimal: value });
}

/** Pack facts that cross the worker wire onto a wire token. */
export function packFacts(node: Node, target: WireFacts, isRoot = false): void {
  const f = factsOf(node);
  if (f.infinity?.maybe) target.inf = 1;
  if (f.integer?.marked) target.int = f.integer.value.toString();
  else if (isRoot && node.type !== "one" && f.integer !== undefined) target.pint = f.integer.value.toString();
  if (f.refused?.unverified) target.unver = 1;
  if (f.refused?.exactUnsure) target.xu = 1;
}

/** Restore facts that crossed the worker wire onto an unpacked node. */
export function unpackFacts(node: Node, source: WireFacts, isRoot = false): void {
  if (source.inf) learn(node, { infinity: { maybe: true } });
  if (source.int !== undefined) learn(node, { integer: { value: BigInt(source.int), marked: true } });
  else if (isRoot && source.pint !== undefined) learn(node, { integer: { value: BigInt(source.pint) } });
  if (source.unver) markUnverified(node);
  if (source.xu) markExactUnsure(node);
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
  const n = provenInteger(node);
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
    const da = !left ? exactDecimalOf(a) : null;
    const db = !right ? exactDecimalOf(b) : null;
    if (left && db && db.s <= 20) return scale(left, db.n, BigInt(10) ** BigInt(db.s));
    if (right && da && da.s <= 20) return scale(right, da.n, BigInt(10) ** BigInt(da.s));
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

function decimalDiv(a: ExactDecimal, b: ExactDecimal): ExactDecimal | null {
  if (b.n === BigInt(0)) return null;
  // (a.n * 10^(-a.s)) / (b.n * 10^(-b.s)) = (a.n / b.n) * 10^(b.s - a.s).
  let num = a.n;
  let den = b.n;
  if (den < BigInt(0)) {
    num = -num;
    den = -den;
  }
  // Reduce num / den by gcd.
  let x = num < BigInt(0) ? -num : num;
  let y = den;
  while (y !== BigInt(0)) {
    const next = x % y;
    x = y;
    y = next;
  }
  num /= x;
  den /= x;
  // Terminating decimal iff reduced denominator is 2^twos * 5^fives.
  let twos = 0;
  let fives = 0;
  while (den % BigInt(2) === BigInt(0)) {
    den /= BigInt(2);
    twos += 1;
  }
  while (den % BigInt(5) === BigInt(0)) {
    den /= BigInt(5);
    fives += 1;
  }
  if (den !== BigInt(1)) return null;
  const extra = Math.max(twos, fives);
  const scale = a.s - b.s + extra;
  const factor = twos >= fives ? BigInt(5) ** BigInt(twos - fives) : BigInt(2) ** BigInt(fives - twos);
  if (scale < 0) {
    if (-scale > DECIMAL_SCALE_MAX) return null;
    return normalizeDecimal({ n: num * factor * BigInt(10) ** BigInt(-scale), s: 0 });
  }
  if (scale > DECIMAL_SCALE_MAX) return null;
  return normalizeDecimal({ n: num * factor, s: scale });
}

function decimalOf(op: Op, a: Node, b: Node | undefined): ExactDecimal | null {
  const x = exactDecimalOf(a);
  if (op === "neg") return x ? normalizeDecimal({ n: -x.n, s: x.s }) : null;
  if (!b) return null;
  const y = exactDecimalOf(b);
  if (!x || !y) return null;
  if (op === "add" || op === "sub") {
    const s = Math.max(x.s, y.s);
    if (s > DECIMAL_SCALE_MAX) return null;
    const xn = x.n * BigInt(10) ** BigInt(s - x.s);
    const yn = y.n * BigInt(10) ** BigInt(s - y.s);
    return normalizeDecimal({ n: op === "sub" ? xn - yn : xn + yn, s });
  }
  if (op === "mul") {
    const s = x.s + y.s;
    if (s > DECIMAL_SCALE_MAX) return null;
    return normalizeDecimal({ n: x.n * y.n, s });
  }
  return decimalDiv(x, y);
}

/** Record exact decimal for a^b when a is an exact decimal and b is a small non-negative integer. */
export function derivePow(out: Node, a: Node, b: Node): Node {
  const x = exactDecimalOf(a);
  const p = integerOf(b);
  if (!x || p === null || p < BigInt(0) || p > BigInt(100)) return out;
  const exp = Number(p);
  if (x.s * exp > DECIMAL_SCALE_MAX) return out;
  const digits = (x.n < BigInt(0) ? -x.n : x.n).toString().length;
  if (digits * exp > DECIMAL_SCALE_MAX + 20) return out;
  const value = normalizeDecimal({ n: x.n ** p, s: x.s * exp });
  return value ? learn(out, { decimal: value }) : out;
}

function intOf(op: Op, a: Node, b: Node | undefined): bigint | undefined {
  const ia = provenInteger(a);
  if (ia === undefined) return undefined;
  if (op === "neg") return ia === BigInt(0) ? undefined : -ia;
  if (!b || op === "div") return undefined;
  const ib = provenInteger(b);
  if (ib === undefined) return undefined;
  if (op === "add") return ia + ib;
  if (op === "sub") return ia - ib;
  return ia * ib;
}

/** Record on `out` the facts that follow from the operation and its operands. Returns `out`. */
export function derive(op: Op, out: Node, a: Node, b?: Node): Node {
  const angle = angleOf(op, a, b);
  const unit = unitOf(op, a, b);
  const decimal = decimalOf(op, a, b);
  const intVal = out.type !== "input" && !isUnverified(out) && !isExactUnsure(out) ? intOf(op, a, b) : undefined;
  if (!angle && !unit && !decimal && intVal === undefined) return out;
  return learn(out, {
    ...(angle ? { angle } : {}),
    ...(unit ? { imaginaryUnit: unit } : {}),
    ...(decimal ? { decimal } : {}),
    ...(intVal !== undefined ? { integer: { value: intVal } } : {}),
  });
}
