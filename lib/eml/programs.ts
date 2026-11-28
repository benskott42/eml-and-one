import table from "./best-known.json";
import { EmlError, onCircuitIsolate, type Node, nodeFromRpn, substitute } from "./node";

/**
 * 1-and-EML programs, measured by K (RPN length).
 * Lengths that are proven minimal say so in best-known.json. Anything else
 * there is shortest known. A record that uses ln 0 = −∞ says so. None of
 * these records depend on Schanuel's conjecture.
 * i (K 57), π (K 93), and √2 (K 61) are constructions, not search records.
 * ln 2 at K 25 is proved minimal. −2, ±1/2, and 3 have the same value under both branch
 * conventions. A program is used by the library only after lib/eml/check.ts
 * accepts it under the lower-bank branch (arg = −π on a negative real).
 * minus, sub, add, sqrt, and pow are the short words, not the full
 * operations. Their domains are the notes in best-known.json.
 */
export const SHORT_PROGRAMS: Readonly<Record<string, string>> = Object.freeze({ ...table.programs });

const cache = new Map<string, Node>();
onCircuitIsolate(() => cache.clear());

export function compactTokens(rpn: string): string[] {
  const tokens: string[] = [];
  for (const ch of rpn) {
    if (ch === "1" || ch === "x" || ch === "y" || ch === "E") tokens.push(ch);
    else throw new EmlError(`Unknown RPN symbol ${ch}.`);
  }
  return tokens;
}

export function nodeFromCompact(rpn: string): Node {
  return nodeFromRpn(compactTokens(rpn));
}

export function programNode(id: string): Node {
  if (!Object.hasOwn(SHORT_PROGRAMS, id)) throw new EmlError(`Unknown program ${id}.`);
  const rpn = SHORT_PROGRAMS[id];
  if (!rpn) throw new EmlError(`Unknown program ${id}.`);
  const hit = cache.get(id);
  if (hit) return hit;
  const node = nodeFromCompact(rpn);
  cache.set(id, node);
  return node;
}

export function applyProgram(id: string, bindings: Record<string, Node> = {}): Node {
  return substitute(programNode(id), bindings);
}

export function programK(id: string): number {
  if (!Object.hasOwn(SHORT_PROGRAMS, id)) throw new EmlError(`Unknown program ${id}.`);
  const rpn = SHORT_PROGRAMS[id];
  if (!rpn) throw new EmlError(`Unknown program ${id}.`);
  return rpn.length;
}
