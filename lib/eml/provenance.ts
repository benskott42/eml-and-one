import table from "./best-known.json";
import { onCircuitIsolate, type Node, circuitStats } from "./node";

/**
 * Labels recorded while a circuit is built. They are not recovered by
 * matching a finished word, because that calls 2*2 a square.
 * The map is replaced on each outer isolate so a cached integer is
 * labelled again the next time its builder runs.
 */
export type LabelKind = "expr" | "gadget" | "literal" | "record" | "construction" | "builder";

export type Hole = { name: string; node: Node };

export type Label = {
  kind: LabelKind;
  text: string;
  gadgetId?: string;
  template?: string;
  holes?: Hole[];
  status?: string;
  provenMinimal?: boolean;
  opaque?: boolean;
};

let labels = new WeakMap<Node, Label[]>();

onCircuitIsolate(() => {
  labels = new WeakMap();
});

function pushLabel(node: Node, label: Label): void {
  const current = labels.get(node);
  if (!current) {
    labels.set(node, [label]);
    return;
  }
  const same = current.findIndex((item) => item.kind === label.kind && item.text === label.text && item.gadgetId === label.gadgetId);
  if (same >= 0) current[same] = label;
  else current.push(label);
}

export function labelsOf(node: Node): Label[] {
  return labels.get(node) ?? [];
}

export function noteGadget(node: Node, id: string, template: string, holes: Hole[]): Node {
  pushLabel(node, { kind: "gadget", text: id, gadgetId: id, template, holes });
  return node;
}

export function noteProgram(node: Node, id: string): Node {
  const template = table.programs[id as keyof typeof table.programs];
  if (template && /[xy]/.test(template)) return node;
  const status = table.records[id as keyof typeof table.records];
  if (status) {
    const provenMinimal = /proven minimal/i.test(status) && !/not proven/i.test(status);
    pushLabel(node, { kind: "record", text: id, status, provenMinimal });
    return node;
  }
  pushLabel(node, { kind: "construction", text: id });
  return node;
}

export function noteLiteral(node: Node, text: string): Node {
  pushLabel(node, { kind: "literal", text });
  return node;
}

export function noteExpr(node: Node, text: string): Node {
  pushLabel(node, { kind: "expr", text });
  return node;
}

/** A direct eml rewrite, shown as one block instead of its internal gates. */
export function noteBuilder(node: Node, name: string): Node {
  pushLabel(node, { kind: "builder", text: name, opaque: true });
  return node;
}

const RANK: Record<LabelKind, number> = {
  expr: 0,
  gadget: 1,
  literal: 2,
  record: 3,
  construction: 4,
  builder: 5,
};

export function lengthOf(node: Node): bigint {
  if (node.type !== "eml") return BigInt(1);
  return circuitStats(node).rpnLength;
}

export type Outline = {
  node: Node;
  start: bigint;
  end: bigint;
  length: bigint;
  label: Label | null;
  gadgetId: string | null;
  hole: string | null;
  name: string;
  opaque: boolean;
  repeat: boolean;
  record: Label | null;
  children: Outline[];
};

function chosen(node: Node): Label | null {
  const all = labelsOf(node);
  if (all.length === 0) return null;
  const opaque = all.find((label) => label.opaque);
  if (opaque) return opaque;
  const gadget = all.find((label) => label.kind === "gadget" && label.holes && label.holes.length > 0);
  if (gadget) return gadget;
  return [...all].sort((a, b) => RANK[a.kind] - RANK[b.kind])[0] ?? null;
}

function displayName(label: Label | null): string {
  if (!label) return "circuit";
  if (label.gadgetId) return label.gadgetId;
  return label.text;
}

const memo = new Map<number, Outline>();

function relative(node: Node, seen: Set<number>): Outline {
  const hit = memo.get(node.id);
  if (hit) return hit;
  const length = lengthOf(node);
  const label = chosen(node);
  const repeat = seen.has(node.id);
  const nextSeen = new Set(seen);
  nextSeen.add(node.id);
  let children: Outline[] = [];
  if (label?.kind === "gadget" && label.template && label.holes && !label.opaque) {
    children = holesFromTemplate(label.template, label.holes, nextSeen);
  } else if (label && !label.opaque && node.type === "eml" && node.a && node.b && label.kind === "expr") {
    children = bubble(node, nextSeen);
  } else if (!label && node.type === "eml" && node.a && node.b) {
    children = bubble(node, nextSeen);
  }
  const outline: Outline = {
    node,
    start: BigInt(0),
    end: length,
    length,
    label,
    gadgetId: labelsOf(node).find((item) => item.gadgetId)?.gadgetId ?? null,
    hole: null,
    name: displayName(label),
    opaque: label?.opaque === true,
    record: labelsOf(node).find((item) => item.kind === "record") ?? null,
    repeat,
    children,
  };
  memo.set(node.id, outline);
  return outline;
}

function holesFromTemplate(template: string, holes: Hole[], seen: Set<number>): Outline[] {
  const parts: Outline[] = [];
  let offset = BigInt(0);
  let index = 0;
  for (const ch of template) {
    if (ch === "x" || ch === "y") {
      const hole = holes[index];
      index += 1;
      if (!hole) continue;
      const already = seen.has(hole.node.id);
      const child = place(relative(hole.node, seen), offset, hole.name, already);
      seen.add(hole.node.id);
      parts.push(child);
      offset += child.length;
    } else {
      offset += BigInt(1);
    }
  }
  return parts;
}

function bubble(node: Node, seen: Set<number>): Outline[] {
  if (node.type !== "eml" || !node.a || !node.b) return [];
  const leftRepeat = seen.has(node.a.id);
  const left = relative(node.a, seen);
  seen.add(node.a.id);
  const rightRepeat = seen.has(node.b.id);
  const right = relative(node.b, seen);
  seen.add(node.b.id);
  const parts: Outline[] = [];
  if (left.label) parts.push(place(left, BigInt(0), null, leftRepeat));
  else for (const child of left.children) parts.push(place(child, child.start, child.hole, child.repeat));
  const shift = left.length;
  if (right.label) parts.push(place(right, shift, null, rightRepeat));
  else for (const child of right.children) parts.push(place(child, shift + child.start, child.hole, child.repeat));
  return parts;
}

function place(source: Outline, offset: bigint, hole: string | null, repeat: boolean): Outline {
  const moved = shiftBy(source, offset - source.start);
  return { ...moved, hole: hole ?? source.hole, repeat: repeat || source.repeat };
}

/** Every start in a subtree shares one coordinate system, so a move is one delta. */
function shiftBy(source: Outline, shift: bigint): Outline {
  if (shift === BigInt(0)) return source;
  return {
    ...source,
    start: source.start + shift,
    end: source.end + shift,
    children: source.children.map((child) => shiftBy(child, shift)),
  };
}

export type PressOutline = {
  tooLong: boolean;
  presses: bigint;
  root: Outline;
};

/** Lazy outline. Offsets are bigint press indexes, 0-based, end exclusive. */
export function pressSpans(root: Node): PressOutline {
  memo.clear();
  const presses = lengthOf(root);
  const outline = relative(root, new Set());
  return { tooLong: presses > BigInt(20_000), presses, root: outline };
}

export function spanCovers(outline: Outline): boolean {
  let cursor = outline.start;
  for (const child of outline.children) {
    if (child.start < cursor || child.end > outline.end || child.start < outline.start) return false;
    if (!spanCovers(child)) return false;
    cursor = child.end;
  }
  return outline.end >= cursor && outline.end - outline.start === outline.length;
}

const MAX_WORD = 20_000;

export function pressWord(node: Node): { oneE: string; bits: string; presses: bigint; copyable: boolean } {
  const presses = lengthOf(node);
  if (presses > BigInt(MAX_WORD)) return { oneE: "", bits: "", presses, copyable: false };
  const tokens = tokensOf(node, Number(presses));
  if (!tokens) return { oneE: "", bits: "", presses, copyable: false };
  const oneE = tokens.map((token) => (token === "E" ? "E" : token)).join("");
  const bits = tokens.map((token) => (token === "E" ? "0" : token)).join("");
  return { oneE, bits, presses, copyable: true };
}

function tokensOf(node: Node, budget: number): string[] | null {
  const tokens: string[] = [];
  const stack: { n: Node; seen: boolean }[] = [{ n: node, seen: false }];
  const visiting = new Set<Node>();
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!frame.seen) {
      if (n.type !== "eml" || !n.a || !n.b) {
        const token = n.type === "one" ? "1" : n.type === "var" ? n.name : n.type === "input" ? n.label : "";
        if (!token) return null;
        tokens.push(token);
        if (tokens.length > budget) return null;
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

const QUALIFIER = "(lower cut, ln 0 = −∞ where used)";

function shortest(label: Label | null): string | null {
  if (!label || label.kind !== "record" || !label.provenMinimal) return null;
  return `the shortest possible ${QUALIFIER}`;
}

/**
 * Sentences from the top two label levels. A numeric result is the
 * calculator's own text, never a name guessed from the digits.
 * A displayed 0 is not narrated.
 */
export function explainOutline(root: Outline, presses: bigint, typed: string, result: string): { full: string; line: string } {
  const gadget = root.gadgetId;
  const count = presses.toString();
  const trimmed = result.trim();
  const safeResult = !trimmed || trimmed === "0" || trimmed === "−0" || trimmed === "computing" || trimmed === "—" ? null : trimmed;
  const substantial = root.children.filter((child) => child.length > BigInt(1));
  const noted = (substantial.length ? substantial : root.children).slice(0, 2);
  const childNotes = noted.map((child) => {
    const record = child.record ?? (child.label?.kind === "record" ? child.label : null);
    const short = shortest(record);
    const count = child.length.toString();
    return short ? `${child.name} from 1s (${count} presses, ${short})` : `${child.name} (${count} presses)`;
  });
  const sameTwice = root.children.length === 2 && root.children[0]?.name === root.children[1]?.name && root.children[1]?.repeat;
  const glue = sameTwice ? presses - root.children[0]!.length - root.children[1]!.length : null;
  const op = gadget === "mul" ? "×" : gadget === "add" ? "+" : gadget === "sub" ? "−" : gadget === "div" ? "÷" : gadget;
  const fullParts = [`You typed ${typed || root.name}.`];
  if (root.opaque) {
    fullParts.push(`This is one ${root.name} block of ${count} presses.`);
  } else if (op && sameTwice && childNotes[0]) {
    const gadgetName = gadget === "mul" ? "multiply" : gadget === "add" ? "add" : gadget === "sub" ? "subtract" : gadget === "div" ? "divide" : gadget;
    const article = /^[aeiou]/i.test(gadgetName ?? "") ? "an" : "a";
    fullParts.push(`The calculator has no ${op} key, so it rewrote it using only 1 and EML: it built ${childNotes[0]}, did that twice, and wrapped both in ${article} ${gadgetName} gadget${glue !== null ? ` (${glue.toString()} more presses)` : ""}.`);
  } else if (op) {
    fullParts.push(`The calculator has no ${op} key, so it rewrote it using only 1 and EML${childNotes.length ? `: ${childNotes.join("; ")}` : ""}.`);
  } else if (childNotes.length) {
    fullParts.push(`It is built from ${childNotes.join("; ")}.`);
  }
  fullParts.push(safeResult ? `That's ${count} presses in total, and the result is ${safeResult}.` : `That's ${count} presses in total.`);
  const full = fullParts.join(" ");
  const line = safeResult ? `${typed || root.name} → ${safeResult} in ${count} presses.` : `${typed || root.name} in ${count} presses.`;
  return { full, line };
}

export function explainCircuit(node: Node, typed: string, result: string): { full: string; line: string } {
  const view = pressSpans(node);
  return explainOutline(view.root, view.presses, typed, result);
}

export type SequenceSnapshot = {
  oneE: string;
  bits: string;
  presses: string;
  copyable: boolean;
  tooLong: boolean;
  outline: Outline;
};

/** Call while the builder labels are still in place. A later isolate drops them. */
export function snapshotSequence(node: Node): SequenceSnapshot {
  const word = pressWord(node);
  const spans = pressSpans(node);
  return {
    oneE: word.oneE,
    bits: word.bits,
    presses: word.presses.toString(),
    copyable: word.copyable,
    tooLong: spans.tooLong,
    outline: spans.root,
  };
}
