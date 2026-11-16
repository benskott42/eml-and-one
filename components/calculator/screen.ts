import { type C } from "@/lib/eml/complex";
import { exactScreen, finiteLossMessage, underflowDisclosure, FLOAT_DIFFERS } from "@/lib/eml/history";
import { scalarNode, seriesShortcutNote } from "@/lib/eml/library";
import { EmlError, EmlLimitError, SINGULAR_LN0, type Node, circuitStats, describe, evaluateReport, isPure, rpnTokens } from "@/lib/eml/node";
import { agreementNote, compileExpression } from "@/lib/eml/parse";
import { formatC, isUsable } from "@/lib/eml/format";
import { pressPreviewForNode } from "@/lib/eml/presses";
import { programNumberText } from "@/lib/eml/programIndex";

export type Mode = "float" | "exact";

export type Entry = {
  value: C;
  text: string;
  singular: string | null;
  mode: Mode;
  node: Node;
  caption: string;
  bound?: Record<string, C>;
  touchedLn0?: boolean;
  overflowed?: boolean;
  underflowed?: boolean;
  nearCut?: boolean;
  pendingExact?: boolean;
  cancelled?: boolean;
  floatDiffers?: boolean;
  exactBeside?: string;
  notice?: string | null;
  watch?: number;
  cutHits?: number;
};

export type Model = {
  stack: Entry[];
  tape: string[];
  note: string | null;
  error: string | null;
};

export const EMPTY: Model = { stack: [], tape: [], note: null, error: null };

export function failure(err: unknown): string {
  if (err instanceof EmlError) return err.message;
  if (err instanceof Error && err.message) return err.message;
  return "That calculation failed.";
}

function isOneAndE(token: string): boolean {
  return token === "1" || token === "E" || token === "x" || token === "y";
}

/** Nested eml text whose leaves are only 1, x, and y — no repaired numbers. */
function pureDescribe(text: string): boolean {
  const leaves = text.split(/eml|[(),\s]+/).filter(Boolean);
  return leaves.length > 0 && leaves.every((leaf) => leaf === "1" || leaf === "x" || leaf === "y");
}

export function programText(node: Node): string | null {
  if (node.type !== "eml") return null;
  const stats = circuitStats(node);
  const summary = `K ${stats.rpnLength} · ${stats.dagGates} shared · depth ${stats.depth}`;
  if (stats.dagGates <= 12 && stats.depth <= 10 && stats.rpnLength <= BigInt(48)) {
    const tokens = rpnTokens(node, 48);
    if (tokens && tokens.every(isOneAndE)) return `${tokens.join(" ")} · ${summary}`;
    const nested = describe(node);
    if (nested && pureDescribe(nested)) return nested;
  }
  return summary;
}

export function runNode(node: Node, mode: Mode): Pick<Entry, "value" | "text" | "singular" | "mode" | "touchedLn0" | "overflowed" | "underflowed" | "nearCut" | "pendingExact" | "notice"> {
  if (node.type === "one") {
    return { value: { re: 1, im: 0 }, text: "1", singular: null, mode, touchedLn0: false, overflowed: false, underflowed: false, nearCut: false, pendingExact: false, notice: null };
  }
  if (mode === "exact") {
    const blank = exactScreen("computing");
    return {
      value: { re: Number.NaN, im: Number.NaN },
      text: blank.text,
      singular: null,
      mode,
      touchedLn0: false,
      overflowed: false,
      underflowed: false,
      nearCut: false,
      pendingExact: true,
      notice: null,
    };
  }
  try {
    const report = evaluateReport(node, {}, { maxNodes: 80_000 });
    return {
      value: report.value,
      text: formatC(report.value),
      singular: report.singular,
      mode,
      touchedLn0: report.touchedLn0,
      overflowed: report.overflowed,
      underflowed: report.underflowed,
      nearCut: report.nearCut,
      pendingExact: false,
      notice: null,
    };
  } catch (err) {
    if (!(err instanceof EmlLimitError)) throw err;
    return {
      value: { re: Number.NaN, im: Number.NaN },
      text: "—",
      singular: null,
      mode,
      touchedLn0: false,
      overflowed: false,
      underflowed: false,
      nearCut: false,
      pendingExact: false,
      notice: "couldn't verify",
    };
  }
}

function programFlags(item: Entry): string | null {
  const bits: string[] = [];
  if (item.value.re === Infinity) bits.push("+∞");
  else if (item.value.re === -Infinity) bits.push("−∞");
  if (item.value.im === Infinity) bits.push("+∞i");
  else if (item.value.im === -Infinity) bits.push("−∞i");
  if (item.touchedLn0) bits.push("ln 0");
  return bits.length ? bits.join(" · ") : null;
}

export function shownSingular(item: Entry): string | null {
  if (
    item.singular === SINGULAR_LN0 &&
    Number.isFinite(item.value.re) &&
    Number.isFinite(item.value.im)
  ) {
    return null;
  }
  return item.singular;
}

export function noteFor(item: Entry): string | null {
  const number = programNumberText(item.node);
  const bits = [
    programText(item.node),
    number,
    number ? programFlags(item) : null,
    item.pendingExact ? exactScreen("computing").note : null,
    item.cancelled ? exactScreen("cancelled").note : null,
    item.floatDiffers && item.exactBeside ? `${FLOAT_DIFFERS} · ${item.exactBeside}` : null,
    item.notice,
    item.overflowed ? "overflow" : null,
    underflowDisclosure(item.value, item.underflowed === true),
    item.nearCut ? "on or very near the branch cut" : null,
    seriesShortcutNote(item.node),
    isPure(item.node) ? "pure" : null,
    shownSingular(item),
    agreementNote(item.caption, item.value, item.bound ?? {}, item.text),
  ].filter(Boolean);
  return bits.length ? bits.join(" · ") : null;
}

export function resultError(item: Entry): string | null {
  if (item.pendingExact || item.cancelled) return null;
  // (10^400+1)/7 is finite in exact arithmetic and only overflows as a float.
  // The printed exact value stays, without a second "left the finite numbers".
  return finiteLossMessage({
    usable: isUsable(item.value),
    notice: item.notice,
    singular: shownSingular(item),
    mode: item.mode,
    text: item.text,
  });
}

let watchSerial = 1;

export function entry(node: Node, caption: string, mode: Mode): Entry {
  return { node, caption, watch: watchSerial++, ...runNode(node, mode) };
}

export function readScalar(text: string): Node {
  const trimmed = text.trim();
  try {
    return scalarNode(trimmed);
  } catch {
    return compileExpression(trimmed, {});
  }
}

export function valuesOf(xText: string, yText: string): Record<string, C> {
  const bound: Record<string, C> = {};
  try {
    bound.x = evaluateReport(readScalar(xText)).value;
  } catch {
    /* the field is not a value yet */
  }
  try {
    bound.y = evaluateReport(readScalar(yText)).value;
  } catch {
    /* the field is not a value yet */
  }
  return bound;
}

export function clip(text: string, max = 72): string {
  return text.length <= max ? text : `${text.slice(0, max - 1)}…`;
}

export function unaryCaption(id: string, label: string, arg: string): string {
  if (id === "inv") return `1/(${arg})`;
  if (id === "minus") return `−(${arg})`;
  if (id === "sqr") return `(${arg})²`;
  if (id === "sqrt") return `√(${arg})`;
  return `${label}(${arg})`;
}

export function shortcutTitle(node: Node, hint?: string): string {
  const presses = pressPreviewForNode(node);
  const lead = hint ? `${hint}. ` : "";
  if (!presses) return `${lead}Shortcut for the 1 and EML keys.`;
  return `${lead}Presses ${presses.preview}${presses.truncated ? ` (${presses.presses} presses)` : ""}`;
}

export function binaryCaption(id: string, x: string, y: string): string {
  if (id === "add") return `${x} + ${y}`;
  if (id === "sub") return `${x} − ${y}`;
  if (id === "mul") return `${x} × ${y}`;
  if (id === "div") return `${x} ÷ ${y}`;
  if (id === "pow") return `${x}^${y}`;
  if (id === "log") return `log(${x}, ${y})`;
  if (id === "avg") return `avg(${x}, ${y})`;
  if (id === "hypot") return `hypot(${x}, ${y})`;
  return `${x} ${id} ${y}`;
}
