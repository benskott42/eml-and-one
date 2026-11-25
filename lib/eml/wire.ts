import { packFacts, unpackFacts } from "./facts";
import { decadeOf, inScaledShell, isLiftedCombine, isLostTiny, isTwoScaled, knownValue, markTwoScaled, noteDecade, noteLiftedCombine, noteLostTiny, noteScaledShell, tagValue } from "./lowering";
import { E, ONE, V, input, markSeriesError, markSeriesShortcut, notePrecision, precisionNoteOf, seriesErrorExp, seriesShortcutText, type Node } from "./node";

/** A circuit sent to the exact worker. PostMessage keeps signed zeros. */
export type Wire =
  | { i: number; k: "1" }
  | { i: number; k: "v"; n: string }
  | { i: number; k: "in"; re: number; im: number; label: string; int?: string; unver?: 1; xu?: 1; lead?: string; se?: number; cap?: 1; dec?: number; nfr?: -1 | 1; nfi?: -1 | 1; inf?: 1 }
  | {
      i: number;
      k: "E";
      a: number;
      b: number;
      pole?: number;
      trig?: number;
      /** asinh argument, or the two terms of an add whose range is unknown. */
      asinh?: number;
      addL?: number;
      addR?: number;
      lift?: 1;
      dec?: number;
      lead?: 1 | string;
      /** Base-10 exponent of the dropped error term on a crude linear series shortcut. */
      se?: number;
      shell?: 1;
      /** The add or sub gate between a 10^k lift and its drop; exact mode sizes its cancellation. */
      lc?: 1;
      /** A past-cap power, or a sum of two float underflows. A vanished result is not certified. */
      cap?: 1;
      /** A known point too small for 120 digits. Float64 still holds it; the range table does not survive the worker. */
      kr?: number;
      ki?: number;
      /** Exact integer when the float has already rounded or overflowed. */
      int?: string;
      /** The root's integer as the compiler built it; exact mode checks the gates against it. */
      pint?: string;
      /** A dropped term. Exact mode must not certify the gates. */
      unver?: 1;
      /** Exact mode cannot certify this value; float keeps its own. */
      xu?: 1;
      /** Built from a ln 0, pole, or division by 0: an ∞ − ∞ here can be the value. */
      inf?: 1;
    };

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
        // JSON drops Infinity, which is how the fresh worker receives a circuit.
        // PostMessage keeps it, and nfr/nfi say the same thing either way.
        const re = frame.n.value.re;
        const im = frame.n.value.im;
        const token: Wire = {
          i,
          k: "in",
          re: Number.isFinite(re) ? re : 0,
          im: Number.isFinite(im) ? im : 0,
          label: frame.n.label,
        };
        if (re === Infinity) token.nfr = 1;
        else if (re === -Infinity) token.nfr = -1;
        if (im === Infinity) token.nfi = 1;
        else if (im === -Infinity) token.nfi = -1;
        const leadNote = seriesShortcutText(frame.n);
        if (leadNote !== undefined) token.lead = leadNote;
        const se = seriesErrorExp(frame.n);
        if (se !== undefined) token.se = se;
        if (isLostTiny(frame.n)) token.cap = 1;
        const decade = decadeOf(frame.n);
        if (decade !== undefined) token.dec = decade;
        packFacts(frame.n, token);
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
    else if (note?.kind === "asinh") token.asinh = idOf.get(note.arg);
    else if (note?.kind === "add") {
      token.addL = idOf.get(note.left);
      token.addR = idOf.get(note.right);
    }
    if (isTwoScaled(frame.n)) token.lift = 1;
    if (inScaledShell(frame.n)) token.shell = 1;
    if (isLiftedCombine(frame.n)) token.lc = 1;
    const leadNote = seriesShortcutText(frame.n);
    if (leadNote !== undefined) token.lead = leadNote;
    const se = seriesErrorExp(frame.n);
    if (se !== undefined) token.se = se;
    if (isLostTiny(frame.n)) token.cap = 1;
    const decade = decadeOf(frame.n);
    if (decade !== undefined) token.dec = decade;
    const known = knownValue(frame.n);
    if (known && tinyPoint(known.re, known.im)) {
      token.kr = known.re;
      token.ki = known.im;
    }
    packFacts(frame.n, token, frame.n === root);
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
      const re = tok.nfr === 1 ? Infinity : tok.nfr === -1 ? -Infinity : tok.re;
      const im = tok.nfi === 1 ? Infinity : tok.nfi === -1 ? -Infinity : tok.im;
      const node = input({ re, im }, tok.label);
      if (tok.lead !== undefined) markSeriesShortcut(node, tok.lead);
      if (tok.se !== undefined) markSeriesError(node, tok.se);
      if (tok.cap) noteLostTiny(node);
      if (tok.dec !== undefined) noteDecade(node, tok.dec);
      unpackFacts(node, tok);
      nodes[tok.i] = node;
    }
    else {
      const a = nodes[tok.a];
      const b = nodes[tok.b];
      if (!a || !b) throw new Error("The circuit was incomplete.");
      const node = E(a, b);
      nodes[tok.i] = node;
      if (tok.pole !== undefined && nodes[tok.pole]) notePrecision(node, { kind: "pole", arg: nodes[tok.pole] });
      else if (tok.trig !== undefined && nodes[tok.trig]) notePrecision(node, { kind: "trig", arg: nodes[tok.trig] });
      else if (tok.asinh !== undefined && nodes[tok.asinh]) notePrecision(node, { kind: "asinh", arg: nodes[tok.asinh] });
      else if (tok.addL !== undefined && tok.addR !== undefined && nodes[tok.addL] && nodes[tok.addR]) {
        notePrecision(node, { kind: "add", left: nodes[tok.addL], right: nodes[tok.addR] });
      }
      if (tok.lift) markTwoScaled(node);
      if (tok.shell) noteScaledShell(node);
      if (tok.lc) noteLiftedCombine(node);
      if (tok.lead !== undefined) markSeriesShortcut(node, typeof tok.lead === "string" ? tok.lead : undefined);
      if (tok.se !== undefined) markSeriesError(node, tok.se);
      if (tok.cap) noteLostTiny(node);
      if (tok.dec !== undefined) noteDecade(node, tok.dec);
      if (tok.kr !== undefined && tok.ki !== undefined) tagValue(node, { re: tok.kr, im: tok.ki });
      unpackFacts(node, tok, tok.i === root);
    }
  }
  const node = nodes[root];
  if (!node) throw new Error("The circuit was incomplete.");
  return node;
}
