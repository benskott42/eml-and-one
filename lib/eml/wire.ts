import { decadeOf, exactRatioOf, inScaledShell, noteExactRatio, noteOddSeries, oddSeriesOf, type SeriesCoeff, isMarkedExactInt, isTwoScaled, isWideTiny, knownValue, markExactInt, markTwoScaled, noteDecade, noteScaledShell, noteWide, normWide, tagValue, wideOf } from "./lowering";

/** v1.1: bump when a field changes meaning. The worker echoes it; a mismatch is a stale worker. */
export const WIRE_VERSION = 2;
import { E, ONE, V, input, isMaybeUnverified, isSeriesShortcut, isUnverified, markMaybeUnverified, markSeriesShortcut, markUnverified, notePrecision, precisionNoteOf, provenInteger, type Node } from "./node";

/** A circuit sent to the exact worker. PostMessage keeps signed zeros. */
export type Wire =
  | { i: number; k: "1" }
  | { i: number; k: "v"; n: string }
  | { i: number; k: "in"; re: WireNum; im: WireNum; label: string; int?: string; unver?: 1; mu?: 1 }
  | {
      i: number;
      k: "E";
      a: number;
      b: number;
      pole?: number;
      trig?: number;
      lift?: 1;
      dec?: number;
      lead?: 1;
      shell?: 1;
      /** A known point too small for 120 digits. Float64 still holds it; the range table does not survive the worker. */
      kr?: WireNum;
      ki?: WireNum;
      /** v2: a real below float64's normal range as [m, e] = m·10^e, 1 ≤ |m| < 10. Exponent, not value. */
      kx?: [number, number];
      /** Exact integer ratio n/d for a real below the normal float range. The circuit is not that value. */
      rq?: [string, string];
      /** Exact integer when the float has already rounded or overflowed. */
      int?: string;
      /** v1.1: an odd series node, [id of x, coefficients]; exact mode evaluates the polynomial. */
      os?: [number, SeriesCoeff[]];
      /** A dropped term. Exact mode must not certify the gates. */
      unver?: 1;
      /** v1.1 (item 6): a sum beside a possible infinity; only a NaN result stands. */
      mu?: 1;
    };

function exactIntDigits(node: Node): string | undefined {
  if (!isMarkedExactInt(node)) return undefined;
  const big = provenInteger(node);
  return big === undefined ? undefined : big.toString();
}

/** True when a known component is below the 120-digit floor and must travel with the circuit. */
function tinyPoint(re: number, im: number): boolean {
  const take = (part: number) => Number.isFinite(part) && part !== 0 && Math.floor(Math.log10(Math.abs(part))) <= -90;
  return take(re) || take(im);
}

export function packCircuit(root: Node): { tokens: Wire[]; root: number } {
  const tokens: Wire[] = [];
  const idOf = new Map<Node, number>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    if (idOf.has(frame.n)) continue;
    if (frame.n.type !== "eml" || !frame.n.a || !frame.n.b) {
      const i = tokens.length;
      idOf.set(frame.n, i);
      if (frame.n.type === "one") tokens.push({ i, k: "1" });
      else if (frame.n.type === "var") tokens.push({ i, k: "v", n: frame.n.name });
      else if (frame.n.type === "input") {
        const digits = exactIntDigits(frame.n);
        const tok: Wire = { i, k: "in", re: wireNum(frame.n.value.re), im: wireNum(frame.n.value.im), label: frame.n.label };
        if (digits !== undefined) tok.int = digits;
        if (isUnverified(frame.n)) tok.unver = 1;
        if (isMaybeUnverified(frame.n)) tok.mu = 1;
        tokens.push(tok);
      }
      continue;
    }
    if (!frame.seen) {
      stack.push({ n: frame.n, seen: true });
      stack.push({ n: frame.n.b, seen: false });
      stack.push({ n: frame.n.a, seen: false });
      continue;
    }
    const a = idOf.get(frame.n.a);
    const b = idOf.get(frame.n.b);
    if (a === undefined || b === undefined) continue;
    const i = tokens.length;
    idOf.set(frame.n, i);
    const note = precisionNoteOf(frame.n);
    const token: Wire = { i, k: "E", a, b };
    if (note?.kind === "pole") token.pole = idOf.get(note.arg);
    else if (note?.kind === "trig") token.trig = idOf.get(note.arg);
    if (isTwoScaled(frame.n)) token.lift = 1;
    if (inScaledShell(frame.n)) token.shell = 1;
    if (isSeriesShortcut(frame.n)) token.lead = 1;
    const decade = decadeOf(frame.n);
    if (decade !== undefined) token.dec = decade;
    const known = knownValue(frame.n);
    if (isWideTiny(frame.n)) {
      const w = wideOf(frame.n);
      if (w) token.kx = [w.m, w.e];
    }
    const ratio = exactRatioOf(frame.n);
    if (ratio) token.rq = [ratio.n.toString(), ratio.d.toString()];
    const digits = exactIntDigits(frame.n);
    if (digits !== undefined) token.int = digits;
    const poly = oddSeriesOf(frame.n);
    const polyArg = poly ? idOf.get(poly.arg) : undefined;
    if (poly && polyArg !== undefined) token.os = [polyArg, poly.coeffs];
    if (known && tinyPoint(known.re, known.im)) {
      token.kr = wireNum(known.re);
      token.ki = wireNum(known.im);
    }
    if (isUnverified(frame.n)) token.unver = 1;
    if (isMaybeUnverified(frame.n)) token.mu = 1;
    tokens.push(token);
  }
  return { tokens, root: idOf.get(root) ?? 0 };
}

// v1.1: a non-finite value (∞i from sqrt(ln 0), a carried 10^400) is sent as a string,
// because JSON (the overnight child, any JSON transport) turns Infinity and NaN into null.
// −0 is sent as "-0": JSON.stringify(-0) is "0", so the sign of -1/inf or a −0 leaf would be lost.
// postMessage keeps numbers, and readWireNum reads both forms.
export type WireNum = number | string;
export function wireNum(x: number): WireNum {
  if (Object.is(x, -0)) return "-0";
  return Number.isFinite(x) ? x : String(x);
}
export function readWireNum(x: WireNum | null): number {
  if (x == null || x === "") throw new Error("The circuit value was empty.");
  return typeof x === "number" ? x : Number(x);
}

export function unpackCircuit(tokens: Wire[], root: number): Node {
  const nodes: Node[] = [];
  for (const tok of tokens) {
    if (tok.k === "1") nodes[tok.i] = ONE;
    else if (tok.k === "v") nodes[tok.i] = V(tok.n);
    else if (tok.k === "in") {
      const leaf = input({ re: readWireNum(tok.re), im: readWireNum(tok.im) }, tok.label);
      if (tok.unver) markUnverified(leaf);
      if (tok.mu) markMaybeUnverified(leaf);
      nodes[tok.i] = tok.int !== undefined ? markExactInt(leaf, BigInt(tok.int)) : leaf;
    }
    else {
      const a = nodes[tok.a];
      const b = nodes[tok.b];
      if (!a || !b) throw new Error("The circuit was incomplete.");
      const node = E(a, b);
      nodes[tok.i] = node;
      if (tok.pole !== undefined && nodes[tok.pole]) notePrecision(node, { kind: "pole", arg: nodes[tok.pole] });
      else if (tok.trig !== undefined && nodes[tok.trig]) notePrecision(node, { kind: "trig", arg: nodes[tok.trig] });
      if (tok.lift) markTwoScaled(node);
      if (tok.shell) noteScaledShell(node);
      if (tok.lead) markSeriesShortcut(node);
      if (tok.dec !== undefined) noteDecade(node, tok.dec);
      if (tok.kr !== undefined && tok.ki !== undefined) tagValue(node, { re: readWireNum(tok.kr), im: readWireNum(tok.ki) });
      if (tok.kx) noteWide(node, normWide(tok.kx[0], tok.kx[1]));
      if (tok.rq) noteExactRatio(node, BigInt(tok.rq[0]), BigInt(tok.rq[1]));
      if (tok.int !== undefined) markExactInt(node, BigInt(tok.int));
      if (tok.os && nodes[tok.os[0]]) noteOddSeries(node, nodes[tok.os[0]], tok.os[1]);
      if (tok.unver) markUnverified(node);
      if (tok.mu) markMaybeUnverified(node);
    }
  }
  const node = nodes[root];
  if (!node) throw new Error("The circuit was incomplete.");
  return node;
}
