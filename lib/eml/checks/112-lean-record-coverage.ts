import { exactReport, exactToFloat } from "../exact";
import { LEAN_VERIFIED_THEOREMS } from "../export";
import { SHORT_PROGRAMS, nodeFromCompact } from "../programs";
import type { CheckModule } from "./_types";

/**
 * Every closed word in best-known.json has a Lean theorem link, and each link's
 * `lean` value term agrees with the exact engine's value of its word. The Lean
 * bridge (scripts/lean-bridge-check.ts) proves the word evaluates to exactly that
 * term, so the chain is: Lean proof = stored term ≈ what the calculator computes.
 */

type Cx = { re: number; im: number };
const cx = (re: number, im = 0): Cx => ({ re, im });
const add = (a: Cx, b: Cx): Cx => cx(a.re + b.re, a.im + b.im);
const sub = (a: Cx, b: Cx): Cx => cx(a.re - b.re, a.im - b.im);
const mul = (a: Cx, b: Cx): Cx => cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
const div = (a: Cx, b: Cx): Cx => {
  const d = b.re * b.re + b.im * b.im;
  return cx((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
};
const cexp = (a: Cx): Cx => cx(Math.exp(a.re) * Math.cos(a.im), Math.exp(a.re) * Math.sin(a.im));
/** Principal log, as Mathlib's Complex.log (Arg in (−π, π]). */
const clog = (a: Cx): Cx => cx(Math.log(Math.hypot(a.re, a.im)), Math.atan2(a.im, a.re));

/**
 * A numeric reading of the small Lean term language the theorems use: numerals,
 * `Real.pi`, `Complex.I`, `Complex.exp`, `Complex.log`, `Real.sqrt`, `Real.log`,
 * `+ - * /`, type ascriptions `(t : ℂ)`, and `EmlExt.finite` / `EmlExt.negInf`.
 * Null for anything else, so an unknown form fails loudly instead of passing.
 */
export function evalLeanTerm(text: string): Cx | "negInf" | null {
  const tokens = text.match(/\d+(?:\.\d+)?|[A-Za-z_][\w.]*|[()+\-*/:ℂ]/g) ?? [];
  let i = 0;
  const peek = () => tokens[i];
  const take = () => tokens[i++];
  const UNARY: Record<string, (a: Cx) => Cx> = {
    "Complex.exp": cexp,
    "Complex.log": clog,
    "Real.sqrt": (a) => cx(Math.sqrt(a.re)),
    "Real.log": (a) => cx(Math.log(a.re)),
    "EmlExt.finite": (a) => a,
  };
  const CONST: Record<string, Cx> = { "Real.pi": cx(Math.PI), "Complex.I": cx(0, 1) };
  function primary(): Cx {
    const t = take();
    if (t === undefined) throw new Error("end of term");
    if (/^\d/.test(t)) return cx(Number(t));
    if (t in CONST) return CONST[t] as Cx;
    if (t in UNARY) return (UNARY[t] as (a: Cx) => Cx)(primary());
    if (t === "(") {
      const v = expr();
      if (peek() === ":") {
        take();
        if (take() !== "ℂ") throw new Error("only ℂ ascriptions");
      }
      if (take() !== ")") throw new Error("missing )");
      return v;
    }
    throw new Error(`unknown token ${t}`);
  }
  function unary(): Cx {
    if (peek() === "-") {
      take();
      const v = unary();
      return cx(-v.re, -v.im);
    }
    return primary();
  }
  function term(): Cx {
    let v = unary();
    while (peek() === "*" || peek() === "/") v = take() === "*" ? mul(v, unary()) : div(v, unary());
    return v;
  }
  function expr(): Cx {
    let v = term();
    while (peek() === "+" || peek() === "-") v = take() === "+" ? add(v, term()) : sub(v, term());
    return v;
  }
  if (text.trim() === "EmlExt.negInf") return "negInf";
  try {
    const v = expr();
    return i === tokens.length ? v : null;
  } catch {
    return null;
  }
}

const close = (a: number, b: number) => Math.abs(a - b) <= 1e-10 * Math.max(1, Math.abs(a), Math.abs(b));

const checkModule: CheckModule = {
  id: 112,
  weight: 300,
  run(ctx) {
    const linked = new Set(Object.keys(LEAN_VERIFIED_THEOREMS));
    const missing = Object.entries(SHORT_PROGRAMS)
      .filter(([, word]) => !/[xy]/.test(word) && !linked.has(word))
      .map(([id, word]) => `${id} (K ${word.length})`);
    if (missing.length > 0) ctx.fail(`FAIL stored words with no Lean theorem link: ${missing.join(", ")}`);

    for (const [word, ref] of Object.entries(LEAN_VERIFIED_THEOREMS)) {
      const want = evalLeanTerm(ref.lean);
      if (want === null) {
        ctx.fail(`FAIL Lean value term not understood: ${ref.theorem} ${ref.lean}`);
        continue;
      }
      const report = exactReport(nodeFromCompact(word));
      const got = exactToFloat(report.value);
      if (want === "negInf") {
        if (!(got.re === Number.NEGATIVE_INFINITY)) ctx.fail(`FAIL ${ref.theorem} engine ${got.re} + ${got.im}i, Lean −∞`);
        continue;
      }
      if (report.unverified || !close(got.re, want.re) || !close(got.im, want.im)) {
        ctx.fail(`FAIL ${ref.theorem} engine ${report.unverified ? "unverified" : `${got.re} + ${got.im}i`}, Lean ${ref.lean} = ${want.re} + ${want.im}i`);
      }
    }
  },
};

export default checkModule;
