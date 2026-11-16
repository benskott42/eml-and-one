import { decadeOf, inScaledShell, isLostTiny, isMarkedExactInt, isTwoScaled, knownValue, markExactInt, markTwoScaled, noteDecade, noteLostTiny, noteScaledShell, tagValue } from "./lowering";
import { E, ONE, V, input, isSeriesShortcut, isUnverified, markSeriesShortcut, markUnverified, notePrecision, precisionNoteOf, provenInteger, type Node } from "./node";

/** A circuit sent to the exact worker. PostMessage keeps signed zeros. */
export type Wire =
  | { i: number; k: "1" }
  | { i: number; k: "v"; n: string }
  | { i: number; k: "in"; re: number; im: number; label: string; int?: string; unver?: 1 }
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
      /** A past-cap power, or a sum of two float underflows. A vanished result is not certified. */
      cap?: 1;
      /** A known point too small for 120 digits. Float64 still holds it; the range table does not survive the worker. */
      kr?: number;
      ki?: number;
      /** Exact integer when the float has already rounded or overflowed. */
      int?: string;
      /** A dropped term. Exact mode must not certify the gates. */
      unver?: 1;
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
        const token: Wire = { i, k: "in", re: frame.n.value.re, im: frame.n.value.im, label: frame.n.label };
        const digits = exactIntDigits(frame.n);
        if (digits !== undefined) token.int = digits;
        if (isUnverified(frame.n)) token.unver = 1;
        tokens.push(token);
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
    if (isLostTiny(frame.n)) token.cap = 1;
    const decade = decadeOf(frame.n);
    if (decade !== undefined) token.dec = decade;
    const known = knownValue(frame.n);
    if (known && tinyPoint(known.re, known.im)) {
      token.kr = known.re;
      token.ki = known.im;
    }
    const digits = exactIntDigits(frame.n);
    if (digits !== undefined) token.int = digits;
    if (isUnverified(frame.n)) token.unver = 1;
    tokens.push(token);
  }
  return { tokens, root: idOf.get(root) ?? 0 };
}

export function unpackCircuit(tokens: Wire[], root: number): Node {
  const nodes: Node[] = [];
  for (const tok of tokens) {
    if (tok.k === "1") nodes[tok.i] = ONE;
    else if (tok.k === "v") nodes[tok.i] = V(tok.n);
    else if (tok.k === "in") {
      const node = input({ re: tok.re, im: tok.im }, tok.label);
      if (tok.unver) markUnverified(node);
      nodes[tok.i] = tok.int !== undefined ? markExactInt(node, BigInt(tok.int)) : node;
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
      if (tok.cap) noteLostTiny(node);
      if (tok.dec !== undefined) noteDecade(node, tok.dec);
      if (tok.kr !== undefined && tok.ki !== undefined) tagValue(node, { re: tok.kr, im: tok.ki });
      if (tok.int !== undefined) markExactInt(node, BigInt(tok.int));
      if (tok.unver) markUnverified(node);
    }
  }
  const node = nodes[root];
  if (!node) throw new Error("The circuit was incomplete.");
  return node;
}
