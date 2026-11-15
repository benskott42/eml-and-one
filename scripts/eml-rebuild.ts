/**
 * Evaluate circuits in a fresh process.
 *
 * The parent sends a DAG of tokens. This file imports the library itself, so
 * none of the parent's WeakMaps or hash-cons tables are visible. `raw` is
 * eml() on those tokens and never calls evaluate(), so a side table inside
 * evaluate cannot change it.
 */
import { readFileSync } from "node:fs";
import { eml } from "../lib/eml/complex";
import { exactEvaluate } from "../lib/eml/exact";
import { E, ONE, V, evaluate, input, type Node } from "../lib/eml/node";

type Packed = { k: "n"; v: number; s: 0 | 1 } | { k: "inf"; s: 0 | 1 } | { k: "nan" };
type Tok =
  | { id: number; op: "1" }
  | { id: number; op: "var"; name: string }
  | { id: number; op: "in"; re: Packed; im: Packed; label: string }
  | { id: number; op: "E"; a: number; b: number };
type Case = { id: number; tokens: Tok[]; env: Record<string, { re: Packed; im: Packed }> };

function unpack(p: Packed): number {
  if (p.k === "nan") return Number.NaN;
  if (p.k === "inf") return p.s ? Number.NEGATIVE_INFINITY : Number.POSITIVE_INFINITY;
  if (p.s && p.v === 0) return -0;
  return p.v;
}

function pack(n: number): Packed {
  if (Number.isNaN(n)) return { k: "nan" };
  if (n === Infinity) return { k: "inf", s: 0 };
  if (n === -Infinity) return { k: "inf", s: 1 };
  if (Object.is(n, -0)) return { k: "n", v: 0, s: 1 };
  return { k: "n", v: n, s: 0 };
}

function envOf(raw: Case["env"]): Record<string, { re: number; im: number }> {
  const env: Record<string, { re: number; im: number }> = {};
  for (const [name, value] of Object.entries(raw)) env[name] = { re: unpack(value.re), im: unpack(value.im) };
  return env;
}

function build(tokens: Tok[]): Node {
  const nodes = new Map<number, Node>();
  for (const tok of tokens) {
    if (tok.op === "1") nodes.set(tok.id, ONE);
    else if (tok.op === "var") nodes.set(tok.id, V(tok.name));
    else if (tok.op === "in") nodes.set(tok.id, input({ re: unpack(tok.re), im: unpack(tok.im) }, tok.label));
    else {
      const a = nodes.get(tok.a);
      const b = nodes.get(tok.b);
      if (!a || !b) throw new Error(`Missing child of ${tok.id}.`);
      nodes.set(tok.id, E(a, b));
    }
  }
  const root = tokens.length ? nodes.get(tokens[tokens.length - 1]!.id) : undefined;
  if (!root) throw new Error("The token list was empty.");
  return root;
}

function rawValue(tokens: Tok[], env: Record<string, { re: number; im: number }>): { re: number; im: number } {
  const values = new Map<number, { re: number; im: number }>();
  for (const tok of tokens) {
    if (tok.op === "1") values.set(tok.id, { re: 1, im: 0 });
    else if (tok.op === "var") {
      const bound = env[tok.name];
      if (!bound) throw new Error(`Missing ${tok.name}.`);
      values.set(tok.id, bound);
    } else if (tok.op === "in") values.set(tok.id, { re: unpack(tok.re), im: unpack(tok.im) });
    else {
      const a = values.get(tok.a);
      const b = values.get(tok.b);
      if (!a || !b) throw new Error(`Missing child of ${tok.id}.`);
      values.set(tok.id, eml(a, b));
    }
  }
  const root = tokens.length ? values.get(tokens[tokens.length - 1]!.id) : undefined;
  if (!root) throw new Error("The token list was empty.");
  return root;
}

function exactKey(z: { re: { isNaN(): boolean; toString(): string }; im: { isNaN(): boolean; toString(): string } }): string {
  return `${z.re.isNaN() ? "nan" : z.re.toString()}\0${z.im.isNaN() ? "nan" : z.im.toString()}`;
}

const body = readFileSync(0, "utf8");
const cases = JSON.parse(body) as Case[];
const results = cases.map((item) => {
  try {
    const env = envOf(item.env);
    const node = build(item.tokens);
    const value = evaluate(node, env, { maxNodes: 400_000 });
    const raw = rawValue(item.tokens, env);
    const exact = exactEvaluate(node, env, { maxNodes: 400_000 });
    return {
      id: item.id,
      float: { re: pack(value.re), im: pack(value.im) },
      raw: { re: pack(raw.re), im: pack(raw.im) },
      exact: exactKey(exact),
    };
  } catch (err) {
    return { id: item.id, error: err instanceof Error ? err.message : String(err) };
  }
});
process.stdout.write(JSON.stringify(results));
