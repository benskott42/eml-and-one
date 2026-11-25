import { c, casinh, close, eml } from "../complex";
import { circuitStats, E, evaluate, evaluateReport, input, isPure, type Node, nodeFromRpn, rpnTokens, SINGULAR_POLE, SINGULAR_PRECISION, SINGULAR_TRIG, V } from "../node";
import { compileExpression, referenceExpression } from "../parse";
import type { CheckContext, CheckModule } from "./_types";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { relClose, repoRoot, tsxCli } from "./_helpers";
import { beyondFloatBound, exactClose, exactEvaluate, exactReport, exactToFloat, formatExact } from "../exact";
import { tArcsin, tArsinh, tExp } from "../library";
import { formatC } from "../format";
import { modeRequest } from "../history";
import { domainAdd, domainSub } from "../lowering";

/**
 * Fuzz generators, variable/differential suites, fresh-circuit isolation, and subprocess rebuild checks.
 */
/** Block 37's seeded random sources. The isolate rebuild (block 43) uses them too. */
function fuzzSources(): string[] {
  let seed = 20261115;
  const rand = () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const atoms = ["0", "1", "2", "0.5", "-1", "e", "1e-300", "1e-15", "1e-9", "1e-5", "1e200", "1e300", "-1e200"];
  const bins = ["+", "-", "*", "/"];
  const uns = ["sin", "cos", "exp", "sqrt"];
  const nest = (depth: number): string => {
    const roll = rand();
    if (depth <= 0 || roll < 0.5) return atoms[Math.floor(rand() * atoms.length)] ?? "1";
    if (roll < 0.75) {
      const fn = uns[Math.floor(rand() * uns.length)] ?? "exp";
      return `${fn}(${nest(depth - 1)})`;
    }
    const op = bins[Math.floor(rand() * bins.length)] ?? "+";
    return `(${nest(depth - 1)}${op}${nest(depth - 1)})`;
  };
  return Array.from({ length: 20 }, () => nest(2));
}

/** Block 39's seeded points. The isolate rebuild (block 43) uses them too. */
function differentialCases(): { source: string; env: { x: { re: number; im: number }; y: { re: number; im: number } } }[] {
  const cases: { source: string; env: { x: { re: number; im: number }; y: { re: number; im: number } } }[] = [];
  let seed = 11;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const exprs = ["x-y", "x+y", "asinh(x)", "arcsin(x)", "tan(x)", "hypot(x,y)", "avg(x,y)", "0-0"];
  for (let i = 0; i < 24; i += 1) {
    const source = exprs[i % exprs.length] ?? "x-y";
    const env = {
      x: c(rand() * 4 - 2, rand() * 2 - 1),
      y: c(rand() * 4 - 2, rand() * 2 - 1),
    };
    if (source === "tan(x)") env.x = c(rand(), 2 + rand() * 3);
    cases.push({ source, env });
  }
  return cases;
}

function freshCircuit(root: Node): Node {
  let id = 8_000_000;
  const seen = new Map<Node, Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame || seen.has(frame.n)) continue;
    if (frame.n.type === "one") {
      seen.set(frame.n, { type: "one", id: id++ });
      continue;
    }
    if (frame.n.type === "var") {
      seen.set(frame.n, { type: "var", name: frame.n.name, id: id++ });
      continue;
    }
    if (frame.n.type === "input") {
      seen.set(frame.n, { type: "input", value: { re: frame.n.value.re, im: frame.n.value.im }, label: frame.n.label, id: id++ });
      continue;
    }
    if (!frame.seen) {
      stack.push({ n: frame.n, seen: true });
      if (frame.n.b) stack.push({ n: frame.n.b, seen: false });
      if (frame.n.a) stack.push({ n: frame.n.a, seen: false });
      continue;
    }
    const a = frame.n.a ? seen.get(frame.n.a) : undefined;
    const b = frame.n.b ? seen.get(frame.n.b) : undefined;
    if (!a || !b) continue;
    seen.set(frame.n, { type: "eml", a, b, id: id++ });
  }
  return seen.get(root) ?? { type: "one", id: id++ };
}
function sharesStructure(a: Node, b: Node): boolean {
  const left = new Set<Node>();
  const stack: Node[] = [a];
  const seen = new Set<Node>();
  while (stack.length) {
    const n = stack.pop();
    if (!n || seen.has(n)) continue;
    seen.add(n);
    left.add(n);
    if (n.type === "eml") stack.push(n.a, n.b);
  }
  const right: Node[] = [b];
  const seenRight = new Set<Node>();
  while (right.length) {
    const n = right.pop();
    if (!n || seenRight.has(n)) continue;
    seenRight.add(n);
    if (left.has(n)) return true;
    if (n.type === "eml") right.push(n.a, n.b);
  }
  return false;
}
function samePoint(a: { re: number; im: number }, b: { re: number; im: number }): boolean {
  if (Number.isNaN(a.re) || Number.isNaN(a.im) || Number.isNaN(b.re) || Number.isNaN(b.im)) {
    return Number.isNaN(a.re) && Number.isNaN(a.im) && Number.isNaN(b.re) && Number.isNaN(b.im);
  }
  return Object.is(a.re, b.re) && Object.is(a.im, b.im);
}
/** Block 40's samples. The isolate rebuild (block 43) uses them too. */
const freshSamples = [
  "2-1e10*i",
  "1-800",
  "(1+2^-52)-1",
  "(2^53+1)-2^53",
  "sqrt(2)^2-2",
  "tan(1+800*i)",
  "0*(-1)",
  "1/(0*(-1))",
  "exp(inf)-exp(inf)",
  "inf-(1/0)",
  "asinh(0)",
  "asinh(-1e155)",
  "10^400/7",
  "3+1e16*i",
  "1e40+i",
  "1e300+i",
  "(1+1e-15)-1",
];

/** Block 41's points and seeded random sources. The isolate rebuild (block 43) uses them too. */
const wideSpan = [0, 1e-12, 1e-3, 0.5, 2, 80, 1e6, -1e5, 1e-300, 1e-15, 1e-9, 1e-5, 1e200, 1e300, -1e200];
function wideFuzzSources(): string[] {
  let seed = 11;
  const rand = () => {
    seed = (seed * 1103515245 + 12345) & 0x7fffffff;
    return seed / 0x7fffffff;
  };
  const atoms = ["0", "1", "2", "0.5", "-1", "e", "10", "1e-300", "1e-15", "1e-9", "1e-5", "1e200", "1e300", "-1e200"];
  const bins = ["+", "-", "*", "/"];
  const uns = ["sin", "cos", "exp", "sqrt", "asinh"];
  const nest = (depth: number): string => {
    const roll = rand();
    if (depth <= 0 || roll < 0.45) return atoms[Math.floor(rand() * atoms.length)] ?? "1";
    if (roll < 0.7) return `${uns[Math.floor(rand() * uns.length)] ?? "exp"}(${nest(depth - 1)})`;
    const op = bins[Math.floor(rand() * bins.length)] ?? "+";
    return `(${nest(depth - 1)}${op}${nest(depth - 1)})`;
  };
  return Array.from({ length: 30 }, () => nest(3));
}

type PackedNum = { k: "n"; v: number; s: 0 | 1 } | { k: "inf"; s: 0 | 1 } | { k: "nan" };
function packNum(n: number): PackedNum {
  if (Number.isNaN(n)) return { k: "nan" };
  if (n === Infinity) return { k: "inf", s: 0 };
  if (n === -Infinity) return { k: "inf", s: 1 };
  if (Object.is(n, -0)) return { k: "n", v: 0, s: 1 };
  return { k: "n", v: n, s: 0 };
}
function unpackNum(p: PackedNum): number {
  if (p.k === "nan") return Number.NaN;
  if (p.k === "inf") return p.s ? Number.NEGATIVE_INFINITY : Number.POSITIVE_INFINITY;
  if (p.s && p.v === 0) return -0;
  return p.v;
}
function exactKey(z: { re: { isNaN(): boolean; toString(): string }; im: { isNaN(): boolean; toString(): string } }): string {
  return `${z.re.isNaN() ? "nan" : z.re.toString()}\0${z.im.isNaN() ? "nan" : z.im.toString()}`;
}
type RebuildTok =
  | { id: number; op: "1" }
  | { id: number; op: "var"; name: string }
  | { id: number; op: "in"; re: PackedNum; im: PackedNum; label: string }
  | { id: number; op: "E"; a: number; b: number };
function dagTokens(root: Node): RebuildTok[] {
  const out: RebuildTok[] = [];
  const seen = new Set<Node>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (seen.has(n)) continue;
    if (n.type !== "eml" || !n.a || !n.b) {
      seen.add(n);
      if (n.type === "one") out.push({ id: n.id, op: "1" });
      else if (n.type === "var") out.push({ id: n.id, op: "var", name: n.name });
      else if (n.type === "input") out.push({ id: n.id, op: "in", re: packNum(n.value.re), im: packNum(n.value.im), label: n.label });
      continue;
    }
    if (!frame.seen) {
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    seen.add(n);
    out.push({ id: n.id, op: "E", a: n.a.id, b: n.b.id });
  }
  return out;
}

type IsolateCase = { source: string; env: Record<string, { re: number; im: number }> };
function compiles(source: string, vars: Record<string, Node>): boolean {
  try {
    compileExpression(source, vars);
    return true;
  } catch {
    return false;
  }
}
/**
 * Each case rebuilt from its DAG tokens in a fresh process must match the live
 * float and exact values. The cases are the ones blocks 37, 39, 40 and 41 test
 * (the sources that compile), built again here so that every shard checks all of
 * them, whichever blocks share its process.
 */
function isolateRebuild(ctx: CheckContext, cases: IsolateCase[]): void {
  const payload = cases.map((item, id) => {
    const node = compileExpression(item.source, { x: V("x"), y: V("y") });
    const env: Record<string, { re: PackedNum; im: PackedNum }> = {};
    for (const [name, value] of Object.entries(item.env)) env[name] = { re: packNum(value.re), im: packNum(value.im) };
    return { id, source: item.source, tokens: dagTokens(node), env, live: item.env };
  });
  const child = spawnSync(process.execPath, [tsxCli, path.join(repoRoot, "scripts/eml-rebuild.ts")], {
    input: JSON.stringify(payload.map(({ id, tokens, env }) => ({ id, tokens, env }))),
    encoding: "utf8",
    cwd: repoRoot,
    maxBuffer: 64 * 1024 * 1024,
    timeout: 180_000,
  });
  if (child.status !== 0 || !child.stdout) {
    ctx.fail("FAIL isolate rebuild", child.status, child.stderr?.slice(0, 500), child.stdout?.slice(0, 200));
  } else {
    const results = JSON.parse(child.stdout) as Array<{
      id: number;
      error?: string;
      float?: { re: PackedNum; im: PackedNum };
      raw?: { re: PackedNum; im: PackedNum };
      exact?: string;
    }>;
    for (const result of results) {
      const item = payload[result.id];
      if (!item) {
        ctx.fail("FAIL isolate id", result.id);
        continue;
      }
      if (result.error || !result.float || !result.raw || result.exact === undefined) {
        ctx.fail("FAIL isolate", item.source, result.error);
        continue;
      }
      const node = compileExpression(item.source, { x: V("x"), y: V("y") });
      const live = evaluate(node, item.live, { maxNodes: 400_000 });
      const fresh = result.float;
      const raw = result.raw;
      if (!samePoint(live, { re: unpackNum(fresh.re), im: unpackNum(fresh.im) }) || !samePoint(live, { re: unpackNum(raw.re), im: unpackNum(raw.im) })) {
        ctx.fail("FAIL isolate float", item.source, live, fresh, raw);
      }
      const exact = exactKey(exactEvaluate(node, item.live, { maxNodes: 400_000 }));
      if (exact !== result.exact) {
        ctx.fail("FAIL isolate exact", item.source, exact, result.exact);
      }
    }
  }
}

const checks: CheckModule[] = [
  {
    id: 37,
    weight: 15823,
    run(ctx) {
      for (const source of fuzzSources()) {
        try {
          const node = compileExpression(source, {});
          const got = evaluate(node);
          const ref = referenceExpression(source, {});
          const exact = exactToFloat(exactEvaluate(node));
          if (!ref || ![got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite)) continue;
          const huge = source.includes("1e200") || source.includes("1e300");
          const flagged = huge && evaluateReport(node).singular !== null;
          if (!flagged && (!close(got, ref, 1e-4) || !close(exact, ref, 1e-4))) {
            ctx.fail("FAIL fuzz", source, got, exact, ref);
          }
        } catch (err) {
          ctx.fail("FAIL fuzz threw", source, err);
        }
      }
    },
  },
  {
    id: 38,
    weight: 15173,
    run(ctx) {
      const variableCases: Array<[string, Record<string, { re: number; im: number }>, { re: number; im: number }]> = [
        ["x-y", { x: c(1), y: c(0) }, c(1)],
        ["x-y", { x: c(0), y: c(0) }, c(0)],
        ["x+y", { x: c(0), y: c(0) }, c(0)],
        ["asinh(x)", { x: c(-2) }, c(Math.asinh(-2))],
        ["asinh(x)", { x: c(0) }, c(0)],
        ["asinh(x)", { x: c(0, 0.5) }, c(0, Math.PI / 6)],
        ["asinh(x)", { x: c(0, 2) }, casinh(c(0, 2))],
        ["asinh(x)", { x: c(0, -2) }, casinh(c(0, -2))],
        ["asinh(x)", { x: c(0, 3) }, casinh(c(0, 3))],
        ["asinh(x)", { x: c(0, -3) }, casinh(c(0, -3))],
        ["asinh(x)", { x: c(-3, 0.5) }, casinh(c(-3, 0.5))],
        ["arcsin(x)", { x: c(0.5) }, c(Math.asin(0.5))],
        ["arcsin(x)", { x: c(1) }, c(Math.PI / 2)],
        ["hypot(x,y)", { x: c(0), y: c(0) }, c(0)],
        ["avg(x,y)", { x: c(0), y: c(0) }, c(0)],
        ["tan(x)", { x: c(1, 800) }, c(0, 1)],
      ];
      for (const [source, env, want] of variableCases) {
        const node = compileExpression(source, { x: V("x"), y: V("y") });
        const got = evaluate(node, env);
        const exact = exactToFloat(exactEvaluate(node, env));
        if (!close(got, want, 1e-8) || !close(exact, want, 1e-6)) {
          ctx.fail("FAIL variable", source, env, got, exact, want);
        }
      }
      const tinyAsinh = [1e-5, -1e-5, 1e-9, -1e-9, 1e-12, -1e-12, 1e-15, -1e-15];
      for (const x of tinyAsinh) {
        const literal = compileExpression(`asinh(${x})`, {});
        const got = evaluate(literal);
        const exact = exactToFloat(exactEvaluate(literal));
        const want = c(Math.asinh(x));
        if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9) || Math.abs(got.im) > 1e-12 * Math.max(Math.abs(x), 1e-30)) {
          ctx.fail("FAIL tiny asinh literal", x, got, exact, want);
        }
        const variable = compileExpression("asinh(x)", { x: V("x") });
        const report = evaluateReport(variable, { x: c(x) });
        const exactVar = exactToFloat(exactEvaluate(variable, { x: c(x) }));
        const underflow = Math.abs(x) < 1e-12;
        if (underflow) {
          if (report.singular !== SINGULAR_PRECISION || !relClose(exactVar, want, 1e-9)) {
            ctx.fail("FAIL tiny asinh variable", x, report.singular, report.value, exactVar, want);
          }
        } else if (
          report.singular === SINGULAR_PRECISION ||
          !relClose(exactVar, want, 1e-9) ||
          (!relClose(report.value, want, 1e-4) && !beyondFloatBound(report.value, exactVar))
        ) {
          ctx.fail("FAIL tiny asinh variable", x, report.singular, report.value, exactVar, want);
        }
      }
      const axisAsinh: Array<[string, { re: number; im: number }]> = [
        ["asinh(2*i)", c(0, 2)],
        ["asinh(-2*i)", c(0, -2)],
        ["asinh(3*i)", c(0, 3)],
        ["asinh(-3*i)", c(0, -3)],
      ];
      for (const [source, z] of axisAsinh) {
        const want = casinh(z);
        const literal = compileExpression(source, {});
        const lit = evaluate(literal);
        const litExact = exactToFloat(exactEvaluate(literal));
        if (!relClose(lit, want, 1e-9) || !relClose(litExact, want, 1e-9)) {
          ctx.fail("FAIL imag-axis asinh literal", source, lit, litExact, want);
        }
        const variable = compileExpression("asinh(x)", { x: V("x") });
        const varFloat = evaluate(variable, { x: z });
        const varExact = exactToFloat(exactEvaluate(variable, { x: z }));
        if (!relClose(varFloat, want, 1e-9) || !relClose(varExact, want, 1e-9)) {
          ctx.fail("FAIL imag-axis asinh variable", source, varFloat, varExact, want);
        }
      }
      const moderate = evaluateReport(tArsinh(V("x")), { x: c(-2) });
      if (moderate.singular === SINGULAR_PRECISION || !close(moderate.value, c(Math.asinh(-2)), 1e-8)) {
        ctx.fail("FAIL asinh(-2) was flagged", moderate.singular, moderate.value);
      }
      for (const [source, want] of [
        ["1e-20+1e-20", 2e-20],
        ["1e-18+1.4e-20", 1e-18 + 1.4e-20],
        ["1e-10+1e-10", 2e-10],
      ] as const) {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const exact = exactToFloat(exactEvaluate(node));
        if (!relClose(got, c(want), 1e-9) || !relClose(exact, c(want), 1e-9)) {
          ctx.fail("FAIL tiny add", source, got, exact, want);
        }
      }
      const tinySum = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(1e-20), y: c(1e-20) });
      const tinyMix = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(1e-18), y: c(1.4e-20) });
      const zeroSum = evaluateReport(compileExpression("x+y", { x: V("x"), y: V("y") }), { x: c(0), y: c(0) });
      if (tinySum.singular !== SINGULAR_PRECISION || tinyMix.singular !== SINGULAR_PRECISION || zeroSum.singular === SINGULAR_PRECISION || zeroSum.value.re !== 0) {
        ctx.fail("FAIL unknown tiny add flag", tinySum, tinyMix, zeroSum);
      }
      const arcCases: Array<[Node, Record<string, { re: number; im: number }>]> = [
        [compileExpression("arcsin(-1)", {}), {}],
        [compileExpression("arcsin(x)", { x: V("x") }), { x: c(-1) }],
        [tArcsin(input(c(-1), "-1")), {}],
      ];
      for (const [node, env] of arcCases) {
        const got = evaluate(node, env);
        const variable = Object.keys(env).length > 0;
        const tol = variable ? 1e-7 : 1e-12;
        if (Math.abs(got.re + Math.PI / 2) > tol || Math.abs(got.im) > tol) {
          ctx.fail("FAIL arcsin(-1)", variable ? "variable" : "literal", got);
        }
      }
      const arcExact = exactToFloat(exactEvaluate(compileExpression("arcsin(-1)", {})));
      if (Math.abs(arcExact.re + Math.PI / 2) > 1e-9 || Math.abs(arcExact.im) > 1e-9) {
        ctx.fail("FAIL exact arcsin(-1)", arcExact);
      }
      const infFold = evaluateReport(compileExpression("(1+1/0)-1/0", {}));
      const infExact = exactReport(compileExpression("(1+1/0)-1/0", {}));
      const infIsOne = infFold.value.re === 1 && infFold.value.im === 0;
      const infExactIsOne = infExact.value.re.eq(1) && infExact.value.im.eq(0);
      if (infIsOne || infExactIsOne || !Number.isNaN(infFold.value.re) || !infExact.value.re.isNaN() || !infFold.singular || !infExact.singular) {
        ctx.fail("FAIL (1+∞)-∞", infFold.value, infFold.singular, formatExact(infExact.value), infExact.singular);
      }
      const varFold = evaluateReport(compileExpression("(x+y)-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(Infinity) });
      const varExact = exactReport(compileExpression("(x+y)-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(Infinity) });
      const foldedBack = varFold.value.re === 1 && varFold.value.im === 0;
      const exactBack = varExact.value.re.eq(1) && varExact.value.im.eq(0);
      if (foldedBack || exactBack || !Number.isNaN(varFold.value.re) || !varExact.value.re.isNaN() || !varFold.singular || !varExact.singular) {
        ctx.fail("FAIL (x+∞)-∞", varFold.value, varFold.singular, formatExact(varExact.value), varExact.singular);
      }
      const finiteFold = evaluate(compileExpression("(1+2)-2", {}));
      if (finiteFold.re !== 1 || finiteFold.im !== 0) {
        ctx.fail("FAIL finite cancellation", finiteFold);
      }
      const noisy = formatC(evaluate(compileExpression("2-1e10*i", {})));
      const tangent = formatC(evaluate(compileExpression("tan(pi/2)", {})));
      if (noisy.includes("2.000000") || !noisy.startsWith("2 − ") || tangent.includes("7")) {
        ctx.fail("FAIL display rounding", noisy, tangent);
      }
      let mode: "float" | "exact" = "float";
      const queued: Array<"float" | "exact"> = [];
      const click = (next: "float" | "exact", busy: boolean) => {
        const step = modeRequest(mode, next, busy);
        if (step.queue) queued.push(next);
        else mode = step.current;
      };
      click("exact", false);
      click("float", false);
      if (mode !== "float") {
        ctx.fail("FAIL two mode clicks in one turn", mode);
      }
      mode = "float";
      queued.length = 0;
      click("exact", true);
      click("float", true);
      for (const next of queued) click(next, false);
      if (mode !== "float" || queued.length !== 2) {
        ctx.fail("FAIL queued mode clicks", mode, queued);
      }
      const outside = evaluateReport(compileExpression("x-y", { x: V("x"), y: V("y") }), {
        x: c(1),
        y: c(0, 80 * Math.PI),
      });
      if (outside.overflowed || !close(outside.value, c(1, -80 * Math.PI), 1e-6)) {
        ctx.fail("FAIL scaled rotSub outside the old strip", outside);
      }
      const knownSub = domainSub(input(c(2, 0.5), "a"), input(c(1, 4), "b"));
      const knownStats = circuitStats(knownSub);
      if (knownStats.rpnLength !== BigInt(131) || !close(evaluate(knownSub), c(1, -3.5), 1e-8)) {
        ctx.fail("FAIL in-strip sub should be unscaled rotSub", knownStats.rpnLength.toString(), evaluate(knownSub));
      }
      // No known range, so both stay scaled. Sub is K 565. Add builds k from b and is K 655.
      const varSubK = circuitStats(domainSub(V("x"), V("y"))).rpnLength;
      const varAddK = circuitStats(domainAdd(V("x"), V("y"))).rpnLength;
      if (varSubK !== BigInt(565) || varAddK !== BigInt(655)) {
        ctx.fail("FAIL variable sub/add K", varSubK.toString(), varAddK.toString());
      }
      const specials = Math.sqrt(Math.exp(2 * Math.E) - 1);
      const specialPoints = [c(specials), c(-specials), c(0, specials), c(0, -specials)];
      for (const b of specialPoints) {
        const node = domainSub(input(c(1), "a"), V("y"));
        const got = evaluateReport(node, { y: b });
        const exact = exactToFloat(exactEvaluate(node, { y: b }));
        const want = c(1 - b.re, -b.im);
        if (!got.touchedLn0 || !close(got.value, want, 1e-8) || !close(exact, want, 1e-8)) {
          ctx.fail("FAIL scaled sub at e^e", b, got.value, exact, want, got.touchedLn0);
        }
      }
      const literals = ["asinh(0.5*i)", "asinh(-2*i)", "asinh(-3+0.5*i)"];
      for (const source of literals) {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const ref = referenceExpression(source, {});
        const exact = exactToFloat(exactEvaluate(node));
        if (!ref || !close(got, ref, 1e-6) || !close(exact, ref, 1e-6)) {
          ctx.fail("FAIL literal", source, got, exact, ref);
        }
      }
      const vanished = compileExpression("5-exp(-inf)", {});
      const vanishedFloat = evaluate(vanished);
      const vanishedExact = exactToFloat(exactEvaluate(vanished));
      if (!close(vanishedFloat, c(5), 1e-8) || !close(vanishedExact, c(5), 1e-8)) {
        ctx.fail("FAIL 5-exp(-inf)", vanishedFloat, vanishedExact);
      }
      const quarter = evaluate(tExp(input({ re: Infinity, im: Math.PI / 2 }, "quarter")));
      const quarterExact = exactEvaluate(tExp(input({ re: Infinity, im: Math.PI / 2 }, "quarter")));
      if (quarter.re !== 0 || quarter.im !== Infinity || !quarterExact.re.isZero() || !quarterExact.im.isPos()) {
        ctx.fail("FAIL exp(+inf + i pi/2)", quarter, quarterExact.re.toString(), quarterExact.im.toString());
      }
    },
  },
  {
    id: 39,
    weight: 3339,
    run(ctx) {
      for (const { source, env } of differentialCases()) {
        try {
          const node = compileExpression(source, { x: V("x"), y: V("y") });
          const got = evaluate(node, env);
          const ref = referenceExpression(source, env);
          const exact = exactToFloat(exactEvaluate(node, env));
          if (!ref || ![got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite)) continue;
          if (!close(got, ref, 1e-4) || !close(exact, ref, 1e-4)) {
            ctx.fail("FAIL differential", source, env, got, exact, ref);
          }
        } catch (err) {
          ctx.fail("FAIL differential threw", source, err);
        }
        const raw = E(V("x"), V("y"));
        const got = evaluate(raw, env);
        const ref = eml(env.x, env.y);
        const exact = exactToFloat(exactEvaluate(raw, env));
        if ([got.re, got.im, ref.re, ref.im, exact.re, exact.im].every(Number.isFinite) && (!close(got, ref, 1e-6) || !close(exact, ref, 1e-6))) {
          ctx.fail("FAIL raw eml", env, got, exact, ref);
        }
      }
    },
  },
  {
    id: 40,
    weight: 3315,
    run(ctx) {
      for (const source of freshSamples) {
        const node = compileExpression(source, {});
        const copy = freshCircuit(node);
        if (copy === node || sharesStructure(node, copy)) {
          ctx.fail("FAIL fresh circuit returned the cached node", source);
        }
        const live = evaluate(node);
        const again = evaluate(copy);
        if (!samePoint(live, again)) {
          ctx.fail("FAIL fresh float", source, live, again);
        }
        const exactLive = exactEvaluate(node);
        const exactAgain = exactEvaluate(copy);
        const exactSame =
          exactLive.re.isNaN() && exactAgain.re.isNaN()
            ? exactLive.im.isNaN() && exactAgain.im.isNaN()
            : exactLive.re.eq(exactAgain.re) && exactLive.im.eq(exactAgain.im);
        if (!exactSame) {
          ctx.fail("FAIL fresh exact", source, formatExact(exactLive), formatExact(exactAgain));
        }
        if (isPure(node)) {
          const tokens = rpnTokens(node, 100_000);
          if (tokens) {
            const pressed = nodeFromRpn(tokens);
            if (!samePoint(evaluate(pressed), live)) {
              ctx.fail("FAIL press string", source);
            }
          }
        }
      }
      const shown = formatExact(exactEvaluate(compileExpression("10^400/7", {}), {}, { maxNodes: 400_000 }));
      if (shown.includes("0000000000") || !shown.includes("10^")) {
        ctx.fail("FAIL 10^400/7 text", shown);
      }
      const neg = evaluate(tArsinh(V("x")), { x: c(-1e5) });
      const neg8 = evaluate(tArsinh(V("x")), { x: c(-1e8) });
      if (!close(neg, c(Math.asinh(-1e5)), 1e-8) || neg.im !== 0 && Math.abs(neg.im) > 1e-8) {
        ctx.fail("FAIL variable asinh(-1e5)", neg);
      }
      if (!close(neg8, c(Math.asinh(-1e8)), 1e-8) || (neg8.im !== 0 && Math.abs(neg8.im) > 1e-8)) {
        ctx.fail("FAIL variable asinh(-1e8)", neg8);
      }
      const signed = evaluate(compileExpression("0*(-1)", {}));
      const reciprocal = evaluate(compileExpression("1/(0*(-1))", {}));
      if (!Object.is(signed.re, -0) || reciprocal.re !== -Infinity) {
        ctx.fail("FAIL signed zero", signed, reciprocal);
      }
      const gap = exactEvaluate(compileExpression("exp(inf)-exp(inf)", {}));
      if (!gap.re.isNaN() || !gap.im.isNaN()) {
        ctx.fail("FAIL exact exp(inf)-exp(inf)", formatExact(gap));
      }
      const ulp = evaluate(compileExpression("(1+2^-52)-1", {}));
      if (!close(ulp, c(2 ** -52), 1e-9) || Math.abs(ulp.im) > 0) {
        ctx.fail("FAIL (1+2^-52)-1", ulp);
      }
    },
  },
  {
    id: 41,
    weight: 42,
    run(ctx) {
      for (const x of wideSpan) {
        for (const source of ["x-y", "asinh(x)"]) {
          const env = { x: c(x), y: c(x === 0 ? 800 : -x) };
          const node = compileExpression(source, { x: V("x"), y: V("y") });
          const copy = freshCircuit(node);
          if (!samePoint(evaluate(node, env), evaluate(copy, env))) {
            ctx.fail("FAIL wide fresh", source, x);
          }
        }
      }
      for (const source of wideFuzzSources()) {
        try {
          const node = compileExpression(source, {});
          const got = evaluate(node);
          const copy = evaluate(freshCircuit(node));
          if (!samePoint(got, copy)) {
            ctx.fail("FAIL fuzz fresh", source, got, copy);
          }
          const ref = referenceExpression(source, {});
          if (!ref) continue;
          const kind = (z: { re: number; im: number }) =>
            Number.isNaN(z.re) || Number.isNaN(z.im) ? "nan" : Number.isFinite(z.re) && Number.isFinite(z.im) ? "fin" : "inf";
          if (kind(got) !== kind(ref)) {
            ctx.fail("FAIL fuzz class", source, got, ref);
          } else if (kind(got) === "fin" && !close(got, ref, 1e-5) && !((source.includes("1e200") || source.includes("1e300")) && evaluateReport(node).singular)) {
            ctx.fail("FAIL fuzz", source, got, ref);
          }
        } catch (err) {
          ctx.fail("FAIL fuzz threw", source, err);
        }
      }
    },
  },
  {
    id: 42,
    weight: 3598,
    run(ctx) {
      const both = (name: string, source: string, re: number, im = 0, tol = 1e-6) => {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 400_000 }));
        if (!close(got, c(re, im), tol) || !close(exact, c(re, im), tol)) {
          ctx.fail("FAIL", name, got, exact, "want", re, im);
        }
      };
      both("asin(3+4i)", "arcsin(3+4*i)", 0.6339838656391766, 2.305509031243477);
      both("asin(-3+4i)", "arcsin(-3+4*i)", -0.6339838656391766, 2.305509031243477);
      both("asin(1+800i)", "arcsin(1+800*i)", 0.0012499983724006398, 7.377760080100202, 1e-5);
      const asinVar = compileExpression("arcsin(x)", { x: V("x") });
      const asinVarGot = evaluate(asinVar, { x: c(3, 4) });
      const asinVarExact = exactToFloat(exactEvaluate(asinVar, { x: c(3, 4) }));
      if (!close(asinVarGot, c(0.6339838656391766, 2.305509031243477), 1e-6) || !close(asinVarExact, c(0.6339838656391766, 2.305509031243477), 1e-6)) {
        ctx.fail("FAIL asin variable 3+4i", asinVarGot, asinVarExact);
      }
      both("asin above the cut", "arcsin(2+1e-18*i)", Math.PI / 2, Math.acosh(2), 1e-5);
      both("asin(1e6)", "arcsin(1e6)", Math.PI / 2, -Math.acosh(1e6), 1e-6);
      const asinTiny = evaluate(compileExpression("arcsin(1e-300)", {}));
      const asinTinyExact = exactEvaluate(compileExpression("arcsin(1e-300)", {}));
      if (!relClose(asinTiny, c(1e-300), 1e-9) || !exactClose(asinTinyExact, "1e-300", 0, 12)) {
        ctx.fail("FAIL arcsin(1e-300)", asinTiny, asinTinyExact.re.toString());
      }
      both("asinh(i)", "asinh(i)", 0, Math.PI / 2, 1e-9);
      both("asinh(-i)", "asinh(-i)", 0, -Math.PI / 2, 1e-9);
      both("asinh(-1e6 i)", "asinh(-1e6*i)", -Math.acosh(1e6), -Math.PI / 2, 1e-6);
      both("artanh(2)", "artanh(2)", Math.log(3) / 2, -Math.PI / 2, 1e-6);
      both("sinh tiny imag", "sinh(1e-10*i)", 0, 1e-10, 1e-8);
      const atanhTiny = evaluate(compileExpression("artanh(1e-20)", {}));
      if (!relClose(atanhTiny, c(1e-20), 1e-6)) {
        ctx.fail("FAIL artanh(1e-20)", atanhTiny);
      }
      const acosOne = evaluate(compileExpression("arccos(1)", {}));
      if (acosOne.re !== 0 || Object.is(acosOne.re, -0) || acosOne.im !== 0) {
        ctx.fail("FAIL arccos(1)", acosOne);
      }
      both("arccos(-1)", "arccos(-1)", Math.PI, 0, 1e-8);
      both("arccos(1e8)", "arccos(1e8)", 0, Math.acosh(1e8), 1e-5);
      const subCancel = evaluate(compileExpression("1-(1-2^-52)", {}));
      const subOther = evaluate(compileExpression("(1-2^-52)-1", {}));
      const subSum = evaluate(compileExpression("1-(1+2^-52)", {}));
      const ulp = 2 ** -52;
      if (!relClose(subCancel, c(ulp), 1e-8) || !relClose(subOther, c(-ulp), 1e-8) || !relClose(subSum, c(-ulp), 1e-8)) {
        ctx.fail("FAIL ulp cancellation", subCancel, subOther, subSum);
      }
      const tinySub = evaluate(compileExpression("3e-20-1e-20", {}));
      if (!relClose(tinySub, c(2e-20), 1e-6)) {
        ctx.fail("FAIL tiny sub", tinySub);
      }
      for (const source of ["exp(-200)", "1e-31", "1e-300"]) {
        const shown = formatExact(exactEvaluate(compileExpression(source, {}), {}, { maxNodes: 200_000 }));
        if (shown === "0" || shown === "−0") {
          ctx.fail("FAIL exact tiny snapped", source, shown);
        }
      }
      const wide = formatExact(exactEvaluate(compileExpression("2-1e16*i", {}), {}, { maxNodes: 200_000 }));
      if (!wide.includes("2") || !wide.includes("10^16")) {
        ctx.fail("FAIL exact per-component", wide);
      }
      const loggedText = formatC(evaluate(compileExpression("ln(-0)", {})));
      if (loggedText === "undefined" || !loggedText.includes("∞") || !loggedText.includes("i")) {
        ctx.fail("FAIL ln(-0) text", loggedText);
      }
      if (!formatC(c(1, 1e-16)).endsWith("≈")) {
        ctx.fail("FAIL tidy mark", formatC(c(1, 1e-16)));
      }
      const gap = compileExpression("exp(exp(800))-exp(exp(800))", {});
      const gapFloat = evaluateReport(gap);
      const gapExact = exactReport(gap, {}, { maxNodes: 200_000 });
      if (!Number.isNaN(gapFloat.value.re) || !gapExact.value.re.isNaN()) {
        ctx.fail("FAIL exp(exp(800)) difference", gapFloat.value, formatExact(gapExact.value));
      }
      const recip = evaluate(compileExpression("1/(0/-1)", {}));
      const recipSqrt = evaluate(compileExpression("1/sqrt(-0)", {}));
      if (recip.re !== -Infinity || recipSqrt.re !== -Infinity) {
        ctx.fail("FAIL signed zero reciprocal", recip, recipSqrt);
      }
      const hugeDiv = evaluateReport(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 });
      if (hugeDiv.value.re !== Infinity) {
        ctx.fail("FAIL (10^400+1)/7", hugeDiv.value, hugeDiv.singular);
      }
      const pole = evaluateReport(compileExpression("tan(pi/2)", {}));
      const bigSin = evaluateReport(compileExpression("sin(1e12)", {}));
      const safeSin = evaluateReport(compileExpression("sin(1+800*i)", {}));
      if (pole.singular !== SINGULAR_POLE || bigSin.singular !== SINGULAR_TRIG || safeSin.singular === SINGULAR_TRIG) {
        ctx.fail("FAIL trig flags", pole.singular, bigSin.singular, safeSin.singular, safeSin.value);
      }
      const bigExact = exactReport(compileExpression("tan(1e100)", {}), {}, { maxNodes: 200_000 });
      const cosExact = exactReport(compileExpression("cos(1e100)", {}), {}, { maxNodes: 200_000 });
      if (bigExact.singular !== SINGULAR_TRIG || cosExact.singular !== SINGULAR_TRIG) {
        ctx.fail("FAIL exact large trig", bigExact.singular, formatExact(bigExact.value), cosExact.singular, formatExact(cosExact.value));
      }
    },
  },
  {
    id: 43,
    weight: 28957,
    run(ctx) {
      isolateRebuild(ctx, fuzzSources().filter((source) => compiles(source, {})).map((source) => ({ source, env: {} })));
    },
  },
  {
    id: 69,
    weight: 5945,
    run(ctx) {
      isolateRebuild(ctx, differentialCases().filter(({ source }) => compiles(source, { x: V("x"), y: V("y") })));
    },
  },
  {
    id: 70,
    weight: 6430,
    run(ctx) {
      isolateRebuild(ctx, freshSamples.map((source) => ({ source, env: {} })));
    },
  },
  {
    id: 71,
    weight: 26683,
    run(ctx) {
      isolateRebuild(ctx, wideSpan.flatMap((x) => ["x-y", "asinh(x)"].map((source) => ({ source, env: { x: c(x), y: c(x === 0 ? 800 : -x) } }))));
    },
  },
  {
    id: 72,
    weight: 15963,
    run(ctx) {
      isolateRebuild(ctx, wideFuzzSources().filter((source) => compiles(source, {})).map((source) => ({ source, env: {} })));
    },
  },
];

export default checks;
