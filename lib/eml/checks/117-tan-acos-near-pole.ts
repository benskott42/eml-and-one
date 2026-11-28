import Decimal from "decimal.js";
import { exactReport, formatExact, type ExactReport } from "../exact";
import { reportUnpacked } from "../packed-eval";
import { compileExpression } from "../parse";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * tan(acos(x)) for a small positive x is the real number cot(asin(x)).
 * The exp form of tan dropped x² near π/2, so exact mode certified a spurious
 * imaginary part (tan(acos(10^(−30))) was 10^30 − 10^(−60)i, tan(acos(10^(−60)))
 * was 10^60 − i) and, once x fell inside the quarter-turn snap, a pole
 * (tan(acos(10^(−120))) was undefined). The true values are 10^30, 10^60 and 10^120.
 *
 * A later reading of a real offset of an odd multiple of π/2 must not certify
 * the lost square as an imaginary part. tanh(acosh(−10^(−130)) + 10^(−130))
 * stays the two-part value 5×10^129 − 5×10^129 i.
 * Each probe is refused or certified true, on the app path and the worker wire.
 * The named rows run as check 117. The dense quarter-turn sweep is the same
 * rule, split into checks 119–121 so one CI shard does not re-read every offset.
 */
const D = Decimal.clone({ precision: 40 });

type Want = { pole: true } | { re: Decimal; im: Decimal; must?: boolean };

const probes: string[] = [
  "tan(-pi/2-1e-64)",
  "tan(3*pi/2-1e-130)",
  "tan(5*pi/2-1e-130)",
  "tanh(acosh(-1e-130)+1e-130)",
  "tan(-pi/2-1e-65)",
  "tan(-pi/2-1e-63)",
  "tan(-pi/2+1e-64)",
  "tan(3*pi/2+1e-130)",
  "tan(3*pi/2-1e-129)",
  "tan(3*pi/2-1e-131)",
  "tan(7*pi/2-1e-130)",
  "tan(-5*pi/2-1e-130)",
  "tan(-3*pi/2-1e-130)",
  "tan(pi/2-1e-130)",
  "tan(-pi/2+1e-90)",
  "tan(1001*pi/2+1e-200)",
  "tan(pi/2+1e-400+1e-400*i)",
  "tan(acos(-1e-60))-1/1e-60",
  "tan(atan(1/1e-150)+pi/2)",
  "tan(acos(-1e-100))*1e-100",
  "tan(acos(-1e-60))^2",
  "1/tanh(acosh(1e-400))",
  "tan(1001*pi/2+1e-50)",
  "tanh(i*pi/2+1e-350+1e-350*i)",
  "1/tan(acos(-1e-150))",
  "tan(3*pi/2-1e-100)",
  "tan(acos(1e-20))+tan(acos(-1e-20))",
  "1/tanh(acosh(1e-300))",
  "tan(acos(-1e-100*i))",
  "tan(acos(-1e-120))+tan(acos(--1e-120))",
  "tan(-3*pi/2+1e-55)",
  "tan(-pi/2-1e-60)",
  "tan(pi/2-1e-350-1e-350*i)",
  "tan(-pi/2-1e-100)",
  "sin(acos(-1e-100))",
  "tan(1001*pi/2+1e-80)",
  "tan(acos(-1e-150))+tan(acos(--1e-150))",
  "tan(acos(-1e-130))+tan(acos(--1e-130))",
  "tan(acos(-1e-100))+tan(acos(--1e-100))",
  "tan(pi/2-1e-400-1e-400*i)",
  "tan(3*pi/2+1e-90)",
  "tan(acos(1e-30))",
  "tan(acos(1e-60))",
  "tan(acos(1e-120))",
  "tan(acos(1e-130))",
  "tan(acos(1e-250))",
  "tanh(acosh(1e-240))",
  "tan(pi/2)",
  "tanh(i*pi/2)",
  "sin(2/exp(200))",
  "sqrt(1+1e-130)-1-0.5e-130",
];

const named = new Set(probes);
const dense: string[] = [];
for (const hi of [70, 140]) {
  const lo = hi === 70 ? 60 : 120;
  for (let k = lo; k <= hi; k += 1) {
    for (const angle of ["3*pi/2", "-pi/2", "-3*pi/2"]) {
      const src = `tan(${angle}-1e-${k})`;
      if (!named.has(src)) dense.push(src);
    }
  }
}

function num(sign: string | undefined, exp: string | undefined): Decimal {
  if (!exp) return new D(0);
  return new D(`${sign ?? "+"}1e-${exp}`);
}

function cdiv(ar: Decimal, ai: Decimal, br: Decimal, bi: Decimal): { re: Decimal; im: Decimal } {
  const den = br.mul(br).plus(bi.mul(bi));
  return { re: ar.mul(br).plus(ai.mul(bi)).div(den), im: ai.mul(br).minus(ar.mul(bi)).div(den) };
}

function csqrt(re: Decimal, im: Decimal): { re: Decimal; im: Decimal } {
  if (im.isZero()) {
    return re.gte(0) ? { re: re.sqrt(), im: new D(0) } : { re: new D(0), im: re.neg().sqrt() };
  }
  const mag = re.mul(re).plus(im.mul(im)).sqrt();
  const outRe = mag.plus(re).div(2).sqrt();
  const outIm = mag.minus(re).div(2).sqrt();
  return { re: outRe, im: im.isNegative() ? outIm.neg() : outIm };
}

/** tan(acos(z)) = sqrt(1 − z²) / z. */
function tanAcos(re: Decimal, im: Decimal): { re: Decimal; im: Decimal } {
  const z2re = re.mul(re).minus(im.mul(im));
  const z2im = re.mul(im).mul(2);
  const root = csqrt(new D(1).minus(z2re), z2im.neg());
  return cdiv(root.re, root.im, re, im);
}

function leaf(tok: string): { re: Decimal; im: Decimal } {
  let sign = 1;
  let s = tok;
  while (s.startsWith("+") || s.startsWith("-")) {
    if (s.startsWith("-")) sign = -sign;
    s = s.slice(1);
  }
  const imag = s.endsWith("*i");
  const mag = new D(imag ? s.slice(0, -2) : s).mul(sign);
  return imag ? { re: new D(0), im: mag } : { re: mag, im: new D(0) };
}

/** tan of an odd multiple of π/2 plus a small offset is −cot of that offset. */
function quarterTurn(n: Decimal, re: Decimal, im: Decimal): Want {
  if (re.isZero() && im.isZero()) return { pole: true };
  if (n.div(2).trunc().mul(2).eq(n)) throw new Error(`even multiple ${n.toString()}`);
  const den = re.mul(re).plus(im.mul(im));
  return { re: re.neg().div(den), im: im.div(den) };
}

function wantOf(src: string): Want {
  if (src === "tanh(acosh(-1e-130)+1e-130)") return { re: new D("5e129"), im: new D("-5e129"), must: true };
  if (src === "tan(pi/2)" || src === "tanh(i*pi/2)") return { pole: true };
  if (src === "sin(2/exp(200))") return { re: new D(2).div(new D(200).exp()), im: new D(0) };
  if (src === "sqrt(1+1e-130)-1-0.5e-130") return { re: new D("-1.25e-261"), im: new D(0) };
  let m = src.match(/^tan\(([-+]?)(?:(\d+)\*)?pi\/2(?:([+-])1e-(\d+))?(?:([+-])1e-(\d+)\*i)?\)$/);
  if (m) {
    const n = new D(`${m[1] ?? ""}${m[2] ?? "1"}`);
    return quarterTurn(n, num(m[3], m[4]), num(m[5], m[6]));
  }
  m = src.match(/^tanh\(i\*pi\/2([+-])1e-(\d+)([+-])1e-(\d+)\*i\)$/);
  if (m) {
    const re = num(m[1], m[2]);
    const im = num(m[3], m[4]);
    const den = re.mul(re).plus(im.mul(im));
    return { re: re.div(den), im: im.neg().div(den) };
  }
  m = src.match(/^tanh\(acosh\(([^)]+)\)\)$/);
  if (m) {
    const z = leaf(m[1]);
    const root = csqrt(z.re.mul(z.re).minus(z.im.mul(z.im)).minus(1), z.re.mul(z.im).mul(2));
    return cdiv(root.re, root.im, z.re, z.im);
  }
  m = src.match(/^1\/tanh\(acosh\(([^)]+)\)\)$/);
  if (m) {
    const z = leaf(m[1]);
    const root = csqrt(z.re.mul(z.re).minus(z.im.mul(z.im)).minus(1), z.re.mul(z.im).mul(2));
    return cdiv(z.re, z.im, root.re, root.im);
  }
  m = src.match(/^tan\(acos\(([^)]+)\)\)$/);
  if (m) return tanAcos(leaf(m[1]).re, leaf(m[1]).im);
  m = src.match(/^tan\(acos\(([^)]+)\)\)\+tan\(acos\(([^)]+)\)\)$/);
  if (m) {
    const a = tanAcos(leaf(m[1]).re, leaf(m[1]).im);
    const b = tanAcos(leaf(m[2]).re, leaf(m[2]).im);
    return { re: a.re.plus(b.re), im: a.im.plus(b.im) };
  }
  m = src.match(/^tan\(acos\(([^)]+)\)\)-1\/1e-(\d+)$/);
  if (m) {
    const a = tanAcos(leaf(m[1]).re, leaf(m[1]).im);
    return { re: a.re.minus(new D(`1e${m[2]}`)), im: a.im };
  }
  m = src.match(/^tan\(acos\(([^)]+)\)\)\*1e-(\d+)$/);
  if (m) {
    const a = tanAcos(leaf(m[1]).re, leaf(m[1]).im);
    const scale = new D(`1e-${m[2]}`);
    return { re: a.re.mul(scale), im: a.im.mul(scale) };
  }
  m = src.match(/^tan\(acos\(([^)]+)\)\)\^2$/);
  if (m) {
    const a = tanAcos(leaf(m[1]).re, leaf(m[1]).im);
    return { re: a.re.mul(a.re).minus(a.im.mul(a.im)), im: a.re.mul(a.im).mul(2) };
  }
  m = src.match(/^1\/tan\(acos\(([^)]+)\)\)$/);
  if (m) {
    const a = tanAcos(leaf(m[1]).re, leaf(m[1]).im);
    return cdiv(new D(1), new D(0), a.re, a.im);
  }
  m = src.match(/^tan\(atan\(1\/1e-(\d+)\)\+pi\/2\)$/);
  if (m) return { re: new D(`-1e-${m[1]}`), im: new D(0) };
  m = src.match(/^sin\(acos\(([^)]+)\)\)$/);
  if (m) {
    const z = leaf(m[1]);
    return csqrt(new D(1).minus(z.re.mul(z.re).minus(z.im.mul(z.im))), z.re.mul(z.im).mul(2).neg());
  }
  throw new Error(`no truth for ${src}`);
}

function asD(part: Decimal): Decimal {
  if (!part.isFinite()) return new D(NaN);
  if (part.isZero()) return new D(0);
  return new D(part.toExponential(30));
}

/** Same part rule as the reviewer's judge: a certified 0 is a real 0, not a dropped digit. */
function partsAgree(gotRe: Decimal, gotIm: Decimal, want: { re: Decimal; im: Decimal }): boolean {
  const re = asD(gotRe);
  const im = asD(gotIm);
  const scale = D.max(want.re.abs(), want.im.abs(), new D("1e-300"));
  const tol = new D("1e-10");
  const floor = scale.mul("1e-470");
  const part = (g: Decimal, x: Decimal) => {
    if (g.sub(x).abs().div(scale).gt(tol)) return false;
    if (g.isZero()) return x.abs().lte(floor);
    return g.sub(x).abs().lte(tol.mul(D.max(x.abs(), floor)));
  };
  return part(re, want.re) && part(im, want.im);
}

function complaint(rep: ExactReport, want: Want): string | null {
  if (rep.unverified) return "must" in want && want.must ? "refused" : null;
  const finite = rep.value.re.isFinite() && rep.value.im.isFinite();
  if ("pole" in want) return finite ? "finite at a pole" : null;
  if (!finite) return "non-finite";
  if (!partsAgree(rep.value.re, rep.value.im, want)) {
    return formatExact(rep.value).replace(/\u200b/g, "");
  }
  return null;
}

function runProbes(ctx: { fail: (message: string, ...details: unknown[]) => void }, sources: string[]) {
  const seen = new Set<string>();
  for (const src of sources) {
    if (seen.has(src)) continue;
    seen.add(src);
    const want = wantOf(src);
    const deadline = () => performance.now() + 40_000;
    const direct = exactReport(compileExpression(src, {}), {}, { maxNodes: 200_000, deadline: deadline() });
    const packed = packCircuit(compileExpression(src, {}));
    const wire = reportUnpacked(packed.tokens, packed.root, 80_000).report;
    for (const [path, rep] of [
      ["app", direct],
      ["wire", wire],
    ] as const) {
      const why = complaint(rep, want);
      if (why) ctx.fail(`FAIL ${src} ${path} ${why}`);
    }
    if (!direct.unverified && !wire.unverified) {
      const appText = formatExact(direct.value).replace(/\u200b/g, "");
      const wireText = formatExact(wire.value).replace(/\u200b/g, "");
      if (appText !== wireText) ctx.fail(`FAIL ${src} app/wire disagree app=${appText} wire=${wireText}`);
    }
  }
}

const checkModule: CheckModule = {
  id: 117,
  weight: 555000,
  run(ctx) {
    const rows: [string, string][] = [
      ["tan(acos(1e-30))", "1×10^30"],
      ["tan(acos(1e-60))", `1${"0".repeat(60)}`],
      ["tan(acos(1e-120))", "1×10^120"],
    ];
    for (const [src, want] of rows) {
      const rep = exactReport(compileExpression(src, {}), {}, { maxNodes: 200_000 });
      const got = formatExact(rep.value).replace(/\u200b/g, "");
      if (rep.unverified || got !== want) {
        ctx.fail(`FAIL ${src} got=${rep.unverified ? "unverified" : got} want=${want}`);
      }
    }
    // x² for x = 10^(−250) does not fit in 480 digits, so the lost square must not
    // be certified as a real 1 beside 10^250. A refusal, or the real value, is honest.
    const past = exactReport(compileExpression("tan(acos(1e-250))", {}), {}, { maxNodes: 200_000 });
    const pastText = formatExact(past.value).replace(/\u200b/g, "");
    if (!past.unverified && pastText.includes("i")) {
      ctx.fail(`FAIL tan(acos(1e-250)) certified a spurious imaginary part: ${pastText}`);
    }
    runProbes(ctx, probes);
  },
};

// The dense quarter-turn sweep is the same probe set. It is split so one CI
// shard is not asked to re-read every offset: each row is still app and wire.
const denseModules: CheckModule[] = [0, 1, 2].map((part) => ({
  id: 119 + part,
  weight: part === 0 ? 268000 : part === 1 ? 263000 : 262000,
  run(ctx) {
    runProbes(
      ctx,
      dense.filter((_, i) => i % 3 === part),
    );
  },
}));

const checks: CheckModule[] = [checkModule, ...denseModules];

export default checks;
