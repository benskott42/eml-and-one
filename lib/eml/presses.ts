/**
 * The button-press spelling of a program.
 * The 1 key is the bit 1, the EML key is the bit 0, and x or y stay as letters.
 */
import { type Node, circuitStats, rpnTokens } from "./node";

const PRESS_LIMIT = 30;
const MAX_EXPAND = 20_000;

export type PressPreview = {
  full: string;
  preview: string;
  presses: bigint;
  truncated: boolean;
  usesVariables: boolean;
  copyable: boolean;
};

/** Map one RPN token onto the press alphabet. Anything else is not a button program. */
export function encodePressToken(token: string): string | null {
  if (token === "1") return "1";
  if (token === "E") return "0";
  if (token === "x" || token === "y") return token;
  return null;
}

export function encodePresses(tokens: readonly string[]): string | null {
  let out = "";
  for (const token of tokens) {
    const bit = encodePressToken(token);
    if (bit === null) return null;
    out += bit;
  }
  return out;
}

/** At most `limit` characters, then an ellipsis. The press count is the full length. */
export function previewPresses(full: string, presses = BigInt(full.length), limit = PRESS_LIMIT): PressPreview {
  const cap = BigInt(limit);
  const truncated = presses > cap || BigInt(full.length) > cap;
  const body = full.length > limit ? full.slice(0, limit) : full;
  return {
    full,
    preview: truncated ? `${body}…` : body,
    presses,
    truncated,
    usesVariables: /[xy]/.test(full),
    copyable: BigInt(full.length) === presses,
  };
}

function leafKind(node: Node): "buttons" | "variables" | "foreign" {
  const seen = new Set<number>();
  let named = false;
  const stack: Node[] = [node];
  while (stack.length) {
    const current = stack.pop();
    if (!current || seen.has(current.id)) continue;
    seen.add(current.id);
    if (current.type === "one") continue;
    if (current.type === "var" && (current.name === "x" || current.name === "y")) {
      named = true;
      continue;
    }
    if (current.type === "eml" && current.a && current.b) {
      stack.push(current.a, current.b);
      continue;
    }
    return "foreign";
  }
  return named ? "variables" : "buttons";
}

function leadingTokens(node: Node, limit: number): string[] | null {
  const tokens: string[] = [];
  const visiting = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: node, seen: false }];
  while (stack.length && tokens.length < limit) {
    const frame = stack.pop();
    if (!frame) break;
    const current = frame.n;
    if (!frame.seen) {
      if (current.type !== "eml" || !current.a || !current.b) {
        const token = current.type === "one" ? "1" : current.type === "var" ? current.name : current.type === "input" ? current.label : "";
        if (!token) return null;
        tokens.push(token);
        continue;
      }
      if (visiting.has(current)) return null;
      visiting.add(current);
      stack.push({ n: current, seen: true });
      stack.push({ n: current.b, seen: false });
      stack.push({ n: current.a, seen: false });
      continue;
    }
    visiting.delete(current);
    tokens.push("E");
  }
  return tokens;
}

/** Press spelling of a circuit, or null when a leaf is not 1, x, y, or EML. */
export function pressPreviewForNode(node: Node, limit = PRESS_LIMIT): PressPreview | null {
  const kind = leafKind(node);
  if (kind === "foreign") return null;
  let length = BigInt(0);
  try {
    length = circuitStats(node).rpnLength;
  } catch {
    return null;
  }
  if (length > BigInt(MAX_EXPAND)) {
    const tokens = leadingTokens(node, limit);
    if (!tokens) return null;
    const prefix = encodePresses(tokens);
    if (prefix === null) return null;
    const shown = previewPresses(prefix, length, limit);
    // The prefix can end before the first x or y. The leaves say whether the string has one.
    return { ...shown, usesVariables: kind === "variables", copyable: false };
  }
  const tokens = rpnTokens(node, Number(length));
  if (!tokens) return null;
  const full = encodePresses(tokens);
  if (full === null) return null;
  return previewPresses(full, length, limit);
}
