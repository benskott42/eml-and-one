// What one stack row holds, how it is computed, and the note under the screen.
import { type C } from "@/lib/eml/complex";
import { formatC, isUsable } from "@/lib/eml/format";
import { exactRationalOf } from "@/lib/eml/facts";
import { recognizedNote, seriesShortcutNote } from "@/lib/eml/library";
import {
  EmlError,
  EmlLimitError,
  SINGULAR_LN0,
  type Node,
  circuitStats,
  describe,
  evaluateReport,
  rpnTokens,
} from "@/lib/eml/node";
import { agreementNote } from "@/lib/eml/parse";
import { exactScreen, finiteLossMessage, underflowDisclosure } from "@/lib/eml/history";
import { programIndexDigits, programNumberText } from "@/lib/eml/programIndex";
import { readScalar } from "@/components/keyTables";

export type Mode = "float" | "exact";

export type Entry = {
  value: C;
  text: string;
  singular: string | null;
  mode: Mode;
  node: Node;
  caption: string;
  bound?: Record<string, C>;
  boundNodes?: Record<string, Node>;
  /** True when the caption combines items with conflicting x/y bindings, so referenceExpression cannot match it. */
  skipAgreement?: boolean;
  /** True when exact/float evaluation refused to certify this entry (kept separate from user notices like rotation). */
  unverified?: boolean;
  /** Exact-mode true ±∞ flags from Decimal (distinct from float64 overflow in `value`). */
  exactInfRe?: -1 | 0 | 1;
  exactInfIm?: -1 | 0 | 1;
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

function programText(node: Node): string | null {
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

function runNode(node: Node, mode: Mode, env: Record<string, C> = {}): Pick<Entry, "value" | "text" | "singular" | "mode" | "touchedLn0" | "overflowed" | "underflowed" | "nearCut" | "pendingExact" | "unverified" | "notice"> {
  if (node.type === "one") {
    return { value: { re: 1, im: 0 }, text: "1", singular: null, mode, touchedLn0: false, overflowed: false, underflowed: false, nearCut: false, pendingExact: false, unverified: false, notice: null };
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
      unverified: false,
      notice: null,
    };
  }
  try {
    const report = evaluateReport(node, env, { maxNodes: 80_000 });
    if (report.unverified) {
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
        unverified: true,
        notice: null,
      };
    }
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
      unverified: false,
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
      unverified: true,
      notice: null,
    };
  }
}

function programFlags(item: Entry): string | null {
  const bits: string[] = [];
  if (item.mode === "exact") {
    // In exact mode, item.value is exactToFloat and overflows to ±Infinity for finite values > 1e308.
    // Use exactInfRe/exactInfIm (or text fallback for synthetic workers) so finite exp(800) never says "+∞".
    const infRe = item.exactInfRe ?? (item.text.includes("∞") && item.value.re === Infinity ? 1 : item.text.includes("−∞") && item.value.re === -Infinity ? -1 : 0);
    const infIm = item.exactInfIm ?? (item.text.includes("∞i") && item.value.im === Infinity ? 1 : item.text.includes("∞i") && item.value.im === -Infinity ? -1 : 0);
    if (infRe === 1) bits.push("+∞");
    else if (infRe === -1) bits.push("−∞");
    if (infIm === 1) bits.push("+∞i");
    else if (infIm === -1) bits.push("−∞i");
  } else {
    if (item.value.re === Infinity) bits.push("+∞");
    else if (item.value.re === -Infinity) bits.push("−∞");
    if (item.value.im === Infinity) bits.push("+∞i");
    else if (item.value.im === -Infinity) bits.push("−∞i");
  }
  if (item.touchedLn0) bits.push("ln 0");
  return bits.length ? bits.join(" · ") : null;
}

function agreementText(caption: string, value: C, variables: Record<string, C>, text: string): string | null {
  return agreementNote(caption, value, variables, text);
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

/**
 * The parts of the note that depend only on the circuit. Circuits are immutable,
 * so they are read in one walk and kept per node: the note is rebuilt on every
 * exact result, swap, drop, undo, and mode switch, and the program number on
 * every render, and each of those used to walk the circuit several times.
 */
type CircuitFacts = { program: string | null; number: string | null; pure: boolean; digits?: string | null };
const circuitFacts = new WeakMap<Node, CircuitFacts>();

function leafKinds(root: Node): { pure: boolean; constant: boolean } {
  let pure = true;
  let constant = true;
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length && (pure || constant)) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    if (n.type === "eml") {
      if (!n.a || !n.b) return { pure: false, constant: false };
      stack.push(n.a, n.b);
    } else if (n.type !== "one") {
      constant = false;
      if (n.type === "input") pure = false;
    }
  }
  return { pure, constant };
}

function factsOf(node: Node): CircuitFacts {
  let facts = circuitFacts.get(node);
  if (!facts) {
    const { pure, constant } = leafKinds(node);
    facts = { program: programText(node), number: constant ? programNumberText(node) : null, pure };
    if (!constant) facts.digits = null;
    circuitFacts.set(node, facts);
  }
  return facts;
}

/** Every digit of the program number, or null when the circuit has none. */
export function programDigits(node: Node): string | null {
  const facts = factsOf(node);
  if (facts.digits === undefined) facts.digits = programIndexDigits(node);
  return facts.digits;
}

export function isUnverifiedEntry(item: Entry): boolean {
  return item.unverified === true || item.notice?.split(" · ").includes("couldn't verify") === true;
}

/** Exact reduced fraction `= n/d` for non-terminating rationals (e.g. 1/3 -> `= 1/3`), or null. */
export function exactFractionNote(node: Node): string | null {
  const q = exactRationalOf(node);
  if (!q || q.d <= BigInt(1)) return null;
  // Skip terminating decimals (denominator 2^a * 5^b) that already print cleanly in decimal.
  let d = q.d;
  while (d % BigInt(2) === BigInt(0)) d /= BigInt(2);
  while (d % BigInt(5) === BigInt(0)) d /= BigInt(5);
  if (d === BigInt(1)) return null;
  const absN = q.n < BigInt(0) ? -q.n : q.n;
  if (absN.toString().length > 12 || q.d.toString().length > 12) return null;
  const sign = q.n < BigInt(0) ? "−" : "";
  return `= ${sign}${absN.toString()}/${q.d.toString()}`;
}

export function noteFor(item: Entry): string | null {
  const facts = factsOf(item.node);
  const number = facts.number;
  const unverified = isUnverifiedEntry(item);
  // floatDiffers and shownSingular are rendered in their own .ti-lcd-flag lines above .ti-lcd-note.
  const bits = [
    facts.program,
    number,
    number ? programFlags(item) : null,
    item.pendingExact ? exactScreen("computing").note : null,
    item.cancelled ? exactScreen("cancelled").note : null,
    unverified && !item.notice?.split(" · ").includes("couldn't verify") ? "couldn't verify" : null,
    !item.pendingExact && !item.cancelled && !unverified ? exactFractionNote(item.node) : null,
    item.notice,
    item.overflowed ? "overflow" : null,
    underflowDisclosure(item.value, item.underflowed === true),
    item.nearCut ? "on or very near the branch cut" : null,
    seriesShortcutNote(item.node),
    recognizedNote(item.node),
    facts.pure ? "pure" : null,
    !item.pendingExact && !item.cancelled && !unverified && !item.skipAgreement
      ? agreementText(item.caption, item.value, item.bound ?? {}, item.text)
      : null,
  ].filter(Boolean);
  return bits.length ? bits.join(" · ") : null;
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

/** True when `text` is a single primary expression (atom, parenthesized group, or function call). */
function isAtomicCaption(text: string): boolean {
  const s = text.trim();
  if (!s) return true;
  if (/^(?:[0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?|[A-Za-zπ√][A-Za-z0-9]*)$/.test(s)) return true;
  // Balanced outer parentheses: "(...)" or function call "fn(...)" or "√(...)".
  const open = s.indexOf("(");
  if (open === -1 || !s.endsWith(")")) return false;
  if (open > 0 && !/^[A-Za-z√][A-Za-z0-9]*$/.test(s.slice(0, open))) return false;
  let depth = 0;
  for (let i = open; i < s.length; i += 1) {
    if (s[i] === "(") depth += 1;
    else if (s[i] === ")") {
      depth -= 1;
      if (depth === 0 && i < s.length - 1) return false;
    }
  }
  return depth === 0;
}

/** Lowest-precedence top-level binary operator in `text` (outside parentheses), or null. */
function topLevelOps(text: string): Set<string> {
  const ops = new Set<string>();
  let depth = 0;
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i];
    if (ch === "(") depth += 1;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (depth === 0) {
      if (ch === "+" || ch === "×" || ch === "*" || ch === "÷" || ch === "/" || ch === "^") ops.add(ch);
      else if ((ch === "-" || ch === "−") && i > 0 && text[i - 1] !== "e" && text[i - 1] !== "E") ops.add("−");
    }
  }
  return ops;
}

function wrapCaption(text: string, need: boolean): string {
  return need && !isAtomicCaption(text) ? `(${text})` : text;
}

export function binaryCaption(id: string, x: string, y: string): string {
  const lx = x.trim();
  const ly = y.trim();
  const xOps = topLevelOps(lx);
  const yOps = topLevelOps(ly);
  const xAddSub = xOps.has("+") || xOps.has("−");
  const yAddSub = yOps.has("+") || yOps.has("−");
  const yMulDiv = yOps.has("×") || yOps.has("*") || yOps.has("÷") || yOps.has("/");
  const yUnaryMinus = ly.startsWith("-") || ly.startsWith("−");
  const xUnaryMinus = lx.startsWith("-") || lx.startsWith("−");
  if (id === "add") return `${lx} + ${wrapCaption(ly, yUnaryMinus)}`;
  if (id === "sub") return `${lx} − ${wrapCaption(ly, yAddSub || yUnaryMinus)}`;
  if (id === "mul") return `${wrapCaption(lx, xAddSub)} × ${wrapCaption(ly, yAddSub || yUnaryMinus)}`;
  if (id === "div") return `${wrapCaption(lx, xAddSub)} ÷ ${wrapCaption(ly, yAddSub || yMulDiv || yUnaryMinus)}`;
  if (id === "pow") return `${wrapCaption(lx, !isAtomicCaption(lx) || xUnaryMinus)}^${wrapCaption(ly, !isAtomicCaption(ly) || yUnaryMinus)}`;
  if (id === "log") return `log(${lx}, ${ly})`;
  if (id === "avg") return `avg(${lx}, ${ly})`;
  if (id === "hypot") return `hypot(${lx}, ${ly})`;
  return `${lx} ${id} ${ly}`;
}

let watchSerial = 1;

export function resultError(item: Entry): string | null {
  if (item.pendingExact || item.cancelled) return null;
  // (10^400+1)/7 is finite in exact arithmetic and only overflows as a float.
  // The printed exact value stays, without a second "left the finite numbers".
  return finiteLossMessage({
    usable: isUsable(item.value),
    unverified: isUnverifiedEntry(item),
    notice: item.notice,
    singular: shownSingular(item),
    mode: item.mode,
    text: item.text,
  });
}

/** bound holds the x and y values a word of x and y leaves reads, in float as in exact. */
export function entry(
  node: Node,
  caption: string,
  mode: Mode,
  bound?: Record<string, C>,
  boundNodes?: Record<string, Node>,
  skipAgreement?: boolean,
): Entry {
  const item: Entry = { node, caption, watch: watchSerial++, ...runNode(node, mode, bound) };
  if (bound) item.bound = bound;
  if (boundNodes) item.boundNodes = boundNodes;
  if (skipAgreement) item.skipAgreement = true;
  return item;
}

export function valuesOf(xText: string, yText: string): Record<string, C> {
  const bound: Record<string, C> = {};
  try {
    bound.x = evaluateReport(readScalar(xText, "x")).value;
  } catch {
    /* the field is not a value yet */
  }
  try {
    bound.y = evaluateReport(readScalar(yText, "y")).value;
  } catch {
    /* the field is not a value yet */
  }
  return bound;
}
