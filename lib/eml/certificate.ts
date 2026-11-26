import Decimal from "decimal.js";
import { binaryToRpn, maxBinaryProgram, minBinaryProgram, nextBinaryProgram } from "./binary";
import { ballEnclose, type BallCompOut, type BallOut } from "./exact-ball";
import { nodeFromRpn } from "./node";
import { catalan } from "./programIndex";

export type ProgramVerdict =
  | "ball-separated"
  | "exact-infinite"
  | "indeterminate"
  | "exact-hit"
  | "open";

export type ProgramWitness = {
  k: number;
  hex: string;
  rpn: string;
  verdict: ProgramVerdict;
  detail: string;
};

export type MinimalityCertificate = {
  targetLabel: string;
  targetRe: string;
  targetIm: string;
  maxK: number;
  precision: number;
  expectedPrograms: number;
  totalPrograms: number;
  counts: Record<ProgramVerdict, number>;
  exactHits: ProgramWitness[];
  openPrograms: ProgramWitness[];
  /** True iff every program up to maxK was rigorously decided with 0 open and 0 hits. */
  provedAbsent: boolean;
};

const DU = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_UP, minE: -9e15, maxE: 9e15 });
const DD = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_DOWN, minE: -9e15, maxE: 9e15 });
const ZERO_U = new DU(0);
const ZERO_D = new DD(0);
const up = (x: Decimal) => new DU(x.abs()).add(ZERO_U);
const dn = (x: Decimal) => new DD(x.abs()).add(ZERO_D);

function compSeparated(comp: BallCompOut, target: Decimal, epsU: Decimal): { separated: boolean; margin: string } {
  if (!comp.v.isFinite()) return { separated: true, margin: "inf" };
  const diff = comp.v.sub(target);
  const errUp = comp.r.add(up(diff).mul(epsU));
  const distDn = dn(diff);
  if (distDn.gt(errUp)) {
    return { separated: true, margin: distDn.sub(errUp).toExponential(2) };
  }
  return { separated: false, margin: "0" };
}

function compExactHit(comp: BallCompOut, target: Decimal, epsU: Decimal): boolean {
  if (!comp.v.isFinite()) return false;
  if (comp.exact) return comp.v.eq(target);
  const diff = comp.v.sub(target);
  const errUp = up(diff).add(comp.r).add(up(diff).mul(epsU));
  return errUp.lte(new DU(10).pow(-40));
}

function classifyBalls(
  balls: BallOut[],
  targetRe: Decimal,
  targetIm: Decimal,
  epsU: Decimal,
): { verdict: ProgramVerdict; detail: string } {
  // Every branch must agree for exclusion.
  if (balls.every((b) => !b.re.v.isFinite() || !b.im.v.isFinite())) {
    return { verdict: "exact-infinite", detail: "all branches infinite" };
  }
  const margins: string[] = [];
  let allSeparated = true;
  for (const b of balls) {
    const sRe = compSeparated(b.re, targetRe, epsU);
    const sIm = compSeparated(b.im, targetIm, epsU);
    if (!sRe.separated && !sIm.separated) {
      allSeparated = false;
      break;
    }
    margins.push(sRe.separated ? `re>${sRe.margin}` : `im>${sIm.margin}`);
  }
  if (allSeparated) {
    return { verdict: "ball-separated", detail: margins[0] ?? "separated" };
  }
  if (balls.length === 1 && balls[0] && compExactHit(balls[0].re, targetRe, epsU) && compExactHit(balls[0].im, targetIm, epsU)) {
    return { verdict: "exact-hit", detail: "enclosure contains target to >40 digits" };
  }
  return { verdict: "open", detail: "ball contains target" };
}

/**
 * Exhaustively enumerate every valid constant EML program of odd length
 * 1, 3, ..., maxK (exactly sum_{n=0}^{(maxK-1)/2} C_n Catalan trees) and
 * certify exclusion from (targetRe, targetIm) using directed-rounding ball arithmetic.
 */
export function generateMinimalityCertificate(
  targetLabel: string,
  targetRe: Decimal.Value,
  targetIm: Decimal.Value,
  maxK: number,
  precision = 80,
): MinimalityCertificate {
  if (!Number.isInteger(maxK) || maxK < 1 || maxK % 2 === 0) {
    throw new RangeError("maxK must be a positive odd integer.");
  }
  const B = Decimal.clone({ precision, rounding: Decimal.ROUND_HALF_UP, minE: -9e15, maxE: 9e15 });
  const tRe = new B(targetRe);
  const tIm = new B(targetIm);
  const epsU = new DU(10).pow(1 - precision);

  const maxGates = (maxK - 1) >> 1;
  let expectedPrograms = 0;
  for (let n = 0; n <= maxGates; n += 1) {
    expectedPrograms += Number(catalan(n));
  }

  const counts: Record<ProgramVerdict, number> = {
    "ball-separated": 0,
    "exact-infinite": 0,
    indeterminate: 0,
    "exact-hit": 0,
    open: 0,
  };
  const exactHits: ProgramWitness[] = [];
  const openPrograms: ProgramWitness[] = [];
  let totalPrograms = 0;

  for (let n = 0; n <= maxGates; n += 1) {
    const k = 2 * n + 1;
    const lo = minBinaryProgram(n);
    const hi = maxBinaryProgram(n);
    let cur = lo;
    while (cur <= hi) {
      const bits = cur.toString(2);
      const rpn = binaryToRpn(bits);
      const hex = `0x${cur.toString(16)}`;
      const node = nodeFromRpn(rpn.split(""));
      const enc = ballEnclose(node, {}, precision, { maxNodes: 50_000 });
      let verdict: ProgramVerdict;
      let detail: string;
      if (!enc.ok) {
        if (enc.reason === "indeterminate") {
          verdict = "indeterminate";
          detail = "provably indeterminate (∞ − ∞ or non-finite imaginary exp)";
        } else {
          verdict = "open";
          detail = enc.reason;
        }
      } else {
        const res = classifyBalls(enc.balls, tRe, tIm, epsU);
        verdict = res.verdict;
        detail = res.detail;
      }
      counts[verdict] += 1;
      if (verdict === "exact-hit") exactHits.push({ k, hex, rpn, verdict, detail });
      if (verdict === "open") openPrograms.push({ k, hex, rpn, verdict, detail });
      totalPrograms += 1;
      cur = cur === hi ? hi + BigInt(1) : nextBinaryProgram(cur + BigInt(1));
    }
  }

  return {
    targetLabel,
    targetRe: tRe.toString(),
    targetIm: tIm.toString(),
    maxK,
    precision,
    expectedPrograms,
    totalPrograms,
    counts,
    exactHits,
    openPrograms,
    provedAbsent: totalPrograms === expectedPrograms && counts.open === 0 && exactHits.length === 0,
  };
}
