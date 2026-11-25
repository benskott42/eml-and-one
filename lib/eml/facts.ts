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
export const RATIONAL_DIGITS_MAX = 200;

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

/**
 * Scale and series-shortcut facts (replaces seriesShortcuts, seriesErrorExps in node.ts
 * and lostTiny, decades, twoScaled, scaledShell, liftedCombines in lowering.ts).
 */
export type ScaleFact = {
  /** Series shortcut note; a vanished result that still holds one is not a certified 0. Crosses the wire as `lead`. */
  seriesShortcut?: string;
  /** Base-10 exponent of the dropped error term on a crude linear series shortcut. Crosses the wire as `se`. */
  seriesErrorExp?: number;
  /** A past-cap tiny term the 480-digit pass cannot recover. Crosses the wire as `cap`. */
  lostTiny?: boolean;
  /** Signed power-of-ten exponent of a known real, including values float64 cannot hold. Crosses the wire as `dec`. */
  decade?: number;
  /** A sum or difference lifted by a power of ten. Crosses the wire as `lift`. */
  twoScaled?: boolean;
  /** Gates built only to lift a tiny pair by a power of ten and bring it back. Crosses the wire as `shell`. */
  scaledShell?: boolean;
  /** The add or sub gate between a 10^k lift and its drop. Crosses the wire as `lc`. */
  liftedCombine?: boolean;
};

/**
 * Structure memos recording how a node was built (replaces cosArg, expArg, sqrtArg,
 * onePlus, oneMinus in library.ts and realSum, realSub, negationOf, negOf in lowering.ts).
 */
export type BuiltFromFact = {
  cosArg?: Node;
  expArg?: Node;
  sqrtArg?: Node;
  onePlus?: Node;
  oneMinus?: Node;
  realSum?: { left: Node; right: Node; gen: number };
  realSub?: { left: Node; right: Node; gen: number };
  negationOf?: Node;
  negOf?: Node;
};

export type Facts = {
  angle?: Angle;
  /** The node is i (1) or −i (−1). */
  imaginaryUnit?: 1 | -1;
  /** The node is q·i for an exact rational q (e.g. 3*i, (1/2)*i), used to derive (q·i)·π angles. */
  imagRational?: Rational;
  infinity?: InfinityFact;
  /** Exact terminating decimal n·10^(−s); null means poisoned by conflicting values on the same node. */
  decimal?: ExactDecimal | null;
  /** Exact reduced rational n/d (d > 0); null means poisoned by conflicting values on the same node. */
  rational?: Rational | null;
  /** Exact integer value; `marked: true` means exact evaluation reads it directly. */
  integer?: IntegerFact;
  /** Refusal marks for exact and float certification. */
  refused?: RefusedFact;
  /** Scale, decade, lift, and series-shortcut facts. */
  scale?: ScaleFact;
  /** True when an exact recognition returned a short program in place of the full circuit. */
  recognized?: boolean;
  /** How this node was built, for structural rewrites and cancellations. */
  builtFrom?: BuiltFromFact;
};

export type WireFacts = {
  inf?: 1;
  int?: string;
  pint?: string;
  iu?: 1 | -1;
  ang?: [string, string, "r" | "i"];
  ed?: [string, number];
  er?: [string, string];
  unver?: 1;
  xu?: 1;
  lead?: 1 | string;
  se?: number;
  cap?: 1;
  dec?: number;
  lift?: 1;
  shell?: 1;
  lc?: 1;
};

export type Op = "add" | "sub" | "mul" | "div" | "neg";

const NONE: Facts = Object.freeze({});
const table = new WeakMap<Node, Facts>();
let expressionGen = 0;

/** Advance the expression generation so per-expression realSum/realSub memos expire on isolateCircuit. */
export function resetExpressionFacts(): void {
  expressionGen += 1;
}

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

function normalizeRational(value: Rational): Rational | null {
  const q = rational(value.n, value.d);
  if (!q) return null;
  const nDigits = (q.n < BigInt(0) ? -q.n : q.n).toString().length;
  const dDigits = q.d.toString().length;
  if (nDigits > RATIONAL_DIGITS_MAX || dDigits > RATIONAL_DIGITS_MAX) return null;
  return q;
}

/** Record facts on a node. Shared finite input leaves and proven integers carry no derived angle/unit/decimal facts. */
export function learn(node: Node, facts: Facts): Node {
  const prev = table.get(node);
  const next: Facts = { ...prev };
  if (node.type !== "input") {
    if (facts.angle && provenInteger(node) === undefined && facts.integer === undefined) next.angle = facts.angle;
    if (facts.imaginaryUnit) next.imaginaryUnit = facts.imaginaryUnit;
    if (facts.imagRational) next.imagRational = facts.imagRational;
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
    if (facts.rational !== undefined && !isUnverified(node) && !isExactUnsure(node)) {
      if (facts.rational === null || prev?.rational === null) {
        next.rational = null;
      } else {
        const norm = normalizeRational(facts.rational);
        if (norm) {
          if (prev?.rational !== undefined && (prev.rational.n !== norm.n || prev.rational.d !== norm.d)) next.rational = null;
          else next.rational = norm;
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
  if (facts.scale) {
    const prevErr = prev?.scale?.seriesErrorExp;
    const nextErr = facts.scale.seriesErrorExp;
    const mergedErr = prevErr !== undefined && nextErr !== undefined ? Math.max(prevErr, nextErr) : (nextErr ?? prevErr);
    next.scale = {
      ...prev?.scale,
      ...facts.scale,
      ...(mergedErr !== undefined ? { seriesErrorExp: mergedErr } : {}),
    };
  }
  if (facts.recognized) {
    next.recognized = true;
  }
  if (facts.builtFrom) {
    next.builtFrom = { ...prev?.builtFrom, ...facts.builtFrom };
  }
  if (
    next.angle ||
    next.imaginaryUnit ||
    next.imagRational ||
    next.infinity ||
    next.decimal !== undefined ||
    next.rational !== undefined ||
    next.integer ||
    next.refused ||
    next.scale ||
    next.recognized ||
    next.builtFrom
  ) {
    table.set(node, next);
  }
  return node;
}

export function noteBuiltFrom(node: Node, built: Omit<BuiltFromFact, "realSum" | "realSub">): Node {
  return learn(node, { builtFrom: built });
}

export function noteBuiltSum(node: Node, left: Node, right: Node): Node {
  return learn(node, { builtFrom: { realSum: { left, right, gen: expressionGen } } });
}

export function noteBuiltSub(node: Node, left: Node, right: Node): Node {
  return learn(node, { builtFrom: { realSub: { left, right, gen: expressionGen } } });
}

export function builtSumOf(node: Node): { left: Node; right: Node } | undefined {
  const s = factsOf(node).builtFrom?.realSum;
  return s && s.gen === expressionGen ? s : undefined;
}

export function builtSubOf(node: Node): { left: Node; right: Node } | undefined {
  const s = factsOf(node).builtFrom?.realSub;
  return s && s.gen === expressionGen ? s : undefined;
}

/** Mark a node as produced by an exact recognition shortcut (see docs/shortcuts.md). */
export function markRecognized(node: Node): Node {
  return learn(node, { recognized: true });
}

export function isRecognized(node: Node): boolean {
  return factsOf(node).recognized === true;
}

/** "recognized exactly" when the circuit uses an exact recognition shortcut, or null. */
export function recognizedNoteFrom(root: Node): string | null {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    if (factsOf(node).recognized) return "recognized exactly";
    if (node.type === "eml") {
      if (node.a) stack.push(node.a);
      if (node.b) stack.push(node.b);
    }
  }
  return null;
}

export function markSeriesShortcut(node: Node, note = "series shortcut"): Node {
  return learn(node, { scale: { seriesShortcut: note } });
}

/** Record the exponent (base 10) of the dropped error term for a crude linear series shortcut. */
export function markSeriesError(node: Node, errExp: number): Node {
  return learn(node, { scale: { seriesErrorExp: errExp } });
}

export function seriesErrorExp(node: Node): number | undefined {
  return factsOf(node).scale?.seriesErrorExp;
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
    const err = factsOf(node).scale?.seriesErrorExp;
    if (err !== undefined && (max === undefined || err > max)) max = err;
    if (node.type === "eml") {
      if (node.a) stack.push(node.a);
      if (node.b) stack.push(node.b);
    }
  }
  return max;
}

export function isSeriesShortcut(node: Node): boolean {
  return factsOf(node).scale?.seriesShortcut !== undefined;
}

export function seriesShortcutText(node: Node): string | undefined {
  return factsOf(node).scale?.seriesShortcut;
}

export function seriesShortcutNoteFrom(root: Node): string | null {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    seen.add(node);
    const note = factsOf(node).scale?.seriesShortcut;
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

export function noteLostTiny(node: Node): Node {
  return learn(node, { scale: { lostTiny: true } });
}

export function isLostTiny(node: Node): boolean {
  return factsOf(node).scale?.lostTiny === true;
}

/** Signed power-of-ten exponent of a known real, including values float64 cannot hold. */
export function noteDecade(node: Node, exp: number): Node {
  if (Number.isFinite(exp)) learn(node, { scale: { decade: Math.trunc(exp) } });
  return node;
}

export function decadeOf(node: Node): number | undefined {
  return factsOf(node).scale?.decade;
}

/** A sum or difference lifted by a power of ten. Its small component is the value, not dust. */
export function markTwoScaled(node: Node): Node {
  return learn(node, { scale: { twoScaled: true } });
}

export function isTwoScaled(node: Node): boolean {
  return factsOf(node).scale?.twoScaled === true;
}

export function inScaledShell(node: Node): boolean {
  return factsOf(node).scale?.scaledShell === true;
}

export function noteScaledShell(node: Node): void {
  learn(node, { scale: { scaledShell: true } });
}

export function isLiftedCombine(node: Node): boolean {
  return factsOf(node).scale?.liftedCombine === true;
}

/** The worker rebuilds the circuit from the wire, so the mark travels with it. */
export function noteLiftedCombine(node: Node): void {
  learn(node, { scale: { liftedCombine: true } });
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

/** Exact reduced rational of a node (including exact decimals and proven integers), or null if unknown or poisoned. */
export function exactRationalOf(node: Node): Rational | null {
  const f = factsOf(node);
  if (f.rational !== undefined) return f.rational;
  if (isUnverified(node) || isExactUnsure(node)) return null;
  const dec = exactDecimalOf(node);
  if (!dec || dec.s > RATIONAL_DIGITS_MAX) return null;
  return normalizeRational({ n: dec.n, d: BigInt(10) ** BigInt(dec.s) });
}

/** Pack facts that cross the worker wire onto a wire token. */
export function packFacts(node: Node, target: WireFacts): void {
  const f = factsOf(node);
  if (f.infinity?.maybe) target.inf = 1;
  if (f.integer?.marked) target.int = f.integer.value.toString();
  else if (node.type !== "one" && f.integer !== undefined) target.pint = f.integer.value.toString();
  if (f.imaginaryUnit !== undefined) target.iu = f.imaginaryUnit;
  if (f.angle) target.ang = [f.angle.q.n.toString(), f.angle.q.d.toString(), f.angle.unit === "real" ? "r" : "i"];
  if (f.decimal) target.ed = [f.decimal.n.toString(), f.decimal.s];
  if (f.rational) target.er = [f.rational.n.toString(), f.rational.d.toString()];
  if (f.refused?.unverified) target.unver = 1;
  if (f.refused?.exactUnsure) target.xu = 1;
  const s = f.scale;
  if (s) {
    if (node.type === "eml") {
      if (s.twoScaled) target.lift = 1;
      if (s.scaledShell) target.shell = 1;
      if (s.liftedCombine) target.lc = 1;
    }
    if (s.seriesShortcut !== undefined) target.lead = s.seriesShortcut;
    if (s.seriesErrorExp !== undefined) target.se = s.seriesErrorExp;
    if (s.lostTiny) target.cap = 1;
    if (s.decade !== undefined) target.dec = s.decade;
  }
}

/** Restore facts that crossed the worker wire onto an unpacked node. */
export function unpackFacts(node: Node, source: WireFacts): void {
  if (source.inf) learn(node, { infinity: { maybe: true } });
  if (source.int !== undefined) learn(node, { integer: { value: BigInt(source.int), marked: true } });
  else if (source.pint !== undefined) learn(node, { integer: { value: BigInt(source.pint) } });
  if (source.iu !== undefined) learn(node, { imaginaryUnit: source.iu });
  if (source.ang) {
    learn(node, {
      angle: {
        q: { n: BigInt(source.ang[0]), d: BigInt(source.ang[1]) },
        unit: source.ang[2] === "r" ? "real" : "imag",
      },
    });
  }
  if (source.ed) learn(node, { decimal: { n: BigInt(source.ed[0]), s: source.ed[1] } });
  if (source.er) learn(node, { rational: { n: BigInt(source.er[0]), d: BigInt(source.er[1]) } });
  if (source.unver) markUnverified(node);
  if (source.xu) markExactUnsure(node);
  if (source.lift) markTwoScaled(node);
  if (source.shell) noteScaledShell(node);
  if (source.lc) noteLiftedCombine(node);
  if (source.lead !== undefined) markSeriesShortcut(node, typeof source.lead === "string" ? source.lead : undefined);
  if (source.se !== undefined) markSeriesError(node, source.se);
  if (source.cap) noteLostTiny(node);
  if (source.dec !== undefined) noteDecade(node, source.dec);
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
    const ra = !left ? exactRationalOf(a) : null;
    const rb = !right ? exactRationalOf(b) : null;
    if (left && rb && rb.d <= BigInt(1_000_000_000_000)) return scale(left, rb.n, rb.d);
    if (right && ra && ra.d <= BigInt(1_000_000_000_000)) return scale(right, ra.n, ra.d);
    const ua = factsOf(a).imaginaryUnit;
    const ub = factsOf(b).imaginaryUnit;
    if (left && ub) return turn(left, ub);
    if (right && ua) return turn(right, ua);
    const ira = !left ? factsOf(a).imagRational : undefined;
    const irb = !right ? factsOf(b).imagRational : undefined;
    if (left && irb && irb.d <= BigInt(1_000_000_000_000)) return scale(turn(left, 1), irb.n, irb.d);
    if (right && ira && ira.d <= BigInt(1_000_000_000_000)) return scale(turn(right, 1), ira.n, ira.d);
    return null;
  }
  const under = integerOf(b);
  if (left && under !== null && under !== BigInt(0)) return scale(left, BigInt(1), under);
  const rbDiv = left ? exactRationalOf(b) : null;
  if (left && rbDiv && rbDiv.n !== BigInt(0)) {
    const absN = rbDiv.n < BigInt(0) ? -rbDiv.n : rbDiv.n;
    if (absN <= BigInt(1_000_000_000_000)) return scale(left, rbDiv.d, rbDiv.n);
  }
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

function rationalOf(op: Op, a: Node, b: Node | undefined): Rational | null {
  const x = exactRationalOf(a);
  if (op === "neg") return x ? { n: -x.n, d: x.d } : null;
  if (!b) return null;
  const y = exactRationalOf(b);
  if (!x || !y) return null;
  if (op === "add") return normalizeRational({ n: x.n * y.d + y.n * x.d, d: x.d * y.d });
  if (op === "sub") return normalizeRational({ n: x.n * y.d - y.n * x.d, d: x.d * y.d });
  if (op === "mul") return normalizeRational({ n: x.n * y.n, d: x.d * y.d });
  if (y.n === BigInt(0)) return null;
  return normalizeRational({ n: x.n * y.d, d: x.d * y.n });
}

/** Record exact decimal/rational for a^b when a is an exact decimal/rational and b is a small integer. */
export function derivePow(out: Node, a: Node, b: Node): Node {
  const p = integerOf(b);
  if (p === null || p < BigInt(-100) || p > BigInt(100)) return out;
  let dec: ExactDecimal | null = null;
  const x = exactDecimalOf(a);
  if (x && p >= BigInt(0)) {
    const exp = Number(p);
    const digits = (x.n < BigInt(0) ? -x.n : x.n).toString().length;
    if (x.s * exp <= DECIMAL_SCALE_MAX && digits * exp <= DECIMAL_SCALE_MAX + 20) {
      dec = normalizeDecimal({ n: x.n ** p, s: x.s * exp });
    }
  }
  let rat: Rational | null = null;
  if (!dec) {
    const q = exactRationalOf(a);
    if (q) {
      const absP = p < BigInt(0) ? -p : p;
      const exp = Number(absP);
      const nDigits = (q.n < BigInt(0) ? -q.n : q.n).toString().length;
      const dDigits = q.d.toString().length;
      if (nDigits * exp <= RATIONAL_DIGITS_MAX && dDigits * exp <= RATIONAL_DIGITS_MAX) {
        if (p >= BigInt(0)) rat = normalizeRational({ n: q.n ** absP, d: q.d ** absP });
        else if (q.n !== BigInt(0)) rat = normalizeRational({ n: q.d ** absP, d: q.n ** absP });
      }
    }
  }
  if (!dec && !rat) return out;
  return learn(out, {
    ...(dec ? { decimal: dec } : {}),
    ...(rat ? { rational: rat } : {}),
  });
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

function imagRationalOf(op: Op, a: Node, b: Node | undefined): Rational | undefined {
  const irOf = (n: Node): Rational | undefined => {
    const f = factsOf(n);
    if (f.imagRational) return f.imagRational;
    if (f.imaginaryUnit !== undefined) return { n: BigInt(f.imaginaryUnit), d: BigInt(1) };
    return undefined;
  };
  const ia = irOf(a);
  if (op === "neg") return ia ? { n: -ia.n, d: ia.d } : undefined;
  if (!b) return undefined;
  const ib = irOf(b);
  if (op === "add" || op === "sub") {
    if (ia && ib) {
      const sign = op === "add" ? BigInt(1) : BigInt(-1);
      return normalizeRational({ n: ia.n * ib.d + sign * ib.n * ia.d, d: ia.d * ib.d }) ?? undefined;
    }
    return undefined;
  }
  if (op === "mul") {
    const ra = !ia ? exactRationalOf(a) : null;
    const rb = !ib ? exactRationalOf(b) : null;
    if (ia && rb) return normalizeRational({ n: ia.n * rb.n, d: ia.d * rb.d }) ?? undefined;
    if (ib && ra) return normalizeRational({ n: ib.n * ra.n, d: ib.d * ra.d }) ?? undefined;
    return undefined;
  }
  if (op === "div") {
    const rb = exactRationalOf(b);
    if (ia && rb && rb.n !== BigInt(0)) return normalizeRational({ n: ia.n * rb.d, d: ia.d * rb.n }) ?? undefined;
  }
  return undefined;
}

/** Record on `out` the facts that follow from the operation and its operands. Returns `out`. */
export function derive(op: Op, out: Node, a: Node, b?: Node): Node {
  const angle = angleOf(op, a, b);
  const unit = unitOf(op, a, b);
  const imagRat = unit === undefined ? imagRationalOf(op, a, b) : undefined;
  const decimal = decimalOf(op, a, b);
  const rat = decimal ? null : rationalOf(op, a, b);
  const intVal = out.type !== "input" && !isUnverified(out) && !isExactUnsure(out) ? intOf(op, a, b) : undefined;
  if (!angle && !unit && !imagRat && !decimal && !rat && intVal === undefined) return out;
  return learn(out, {
    ...(angle ? { angle } : {}),
    ...(unit ? { imaginaryUnit: unit } : {}),
    ...(imagRat ? { imagRational: imagRat } : {}),
    ...(decimal ? { decimal } : {}),
    ...(rat ? { rational: rat } : {}),
    ...(intVal !== undefined ? { integer: { value: intVal } } : {}),
  });
}
