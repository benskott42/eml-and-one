import Decimal from "decimal.js";
import { ballOps, enclose } from "./enclose";
import { E, ONE, input, type Node } from "./node";

/**
 * Containment checks for the 300-digit balls in enclose.ts (outside review 2026-11-21,
 * B3/B4/B6). The reference is decimal.js at 400 digits, which resolves errors at
 * 10^(−300) relative; a difference under 10^(−380) of the value is reference noise.
 * Float inputs enter as their shortest decimal, the same string the ball reads.
 * Before the fix: 654/3010 exp points, 814/2004 ln points, the stretch balls and the
 * cut-edge ball were outside their balls.
 */
const R = Decimal.clone({ precision: 400, minE: -9e15, maxE: 9e15 });
const NOISE = new R(10).pow(-380);
type Ball = ReturnType<typeof ballOps.point>;

function outside(center: Decimal, radius: Decimal, truth: Decimal): boolean {
  const err = truth.sub(new R(center.toString())).abs();
  if (err.lte(NOISE.mul(R.max(truth.abs(), 1)))) return false;
  return err.gt(new R(radius.toString()));
}
function missed(ball: Ball, re: Decimal, im: Decimal): boolean {
  return outside(ball.re, ball.rr, re) || outside(ball.im, ball.ir, im);
}
function rExp(re: Decimal, im: Decimal): [Decimal, Decimal] {
  const m = re.exp();
  return [m.mul(im.cos()), m.mul(im.sin())];
}
/** eml's log: a negative real takes the lower bank, −π. */
function rLn(re: Decimal, im: Decimal): [Decimal, Decimal] {
  const mag = re.mul(re).add(im.mul(im)).sqrt();
  const arg = im.isZero() && re.isNeg() ? R.acos(-1).neg() : R.atan2(im, re);
  return [mag.ln(), arg];
}
function lcg(seed: number): () => number {
  let s = seed;
  return () => (s = (s * 1103515245 + 12345) % 2147483648) / 2147483648;
}
const pointBall = (re: Decimal.Value, im: Decimal.Value, rr: Decimal.Value = 0, ir: Decimal.Value = 0): Ball => {
  const b = ballOps.point(re, im);
  return { ...b, rr: new Decimal(rr), ir: new Decimal(ir) };
};

export type EncloseSample = { expPoints: number; lnPoints: number; circlePoints: number; leaves: number };
/** The full sets from the review (3010 exp points, 2004 ln points, 626 circuits). */
export const FULL_SAMPLE: EncloseSample = { expPoints: 3000, lnPoints: 1500, circlePoints: 500, leaves: 8 };
/** check.ts runs a prefix of the same sequences; scripts/enclose-containment.ts runs FULL_SAMPLE. */
export const CHECK_SAMPLE: EncloseSample = { expPoints: 300, lnPoints: 120, circlePoints: 60, leaves: 7 };

export function runEncloseChecks(sample: EncloseSample = CHECK_SAMPLE): number {
  let failed = 0;
  // B3: exp of float points, through the op and through the public E(x, 1).
  const rnd = lcg(12345);
  const pts: Array<[number, number]> = [];
  for (let i = 0; i < sample.expPoints; i += 1) pts.push([(rnd() - 0.5) * 6, (rnd() - 0.5) * 20]);
  for (const k of [1, 3, 5, 101, 1e5 + 1]) pts.push([0, (k * Math.PI) / 2], [1.5, (k * Math.PI) / 2]);
  let expMiss = 0;
  let pubMiss = 0;
  for (const [a, b] of pts) {
    const [tr, ti] = rExp(new R(a), new R(b));
    if (missed(ballOps.cexp(ballOps.point(a, b)), tr, ti)) expMiss += 1;
    if (missed(enclose(E(input({ re: a, im: b }, "x"), ONE)), tr, ti)) pubMiss += 1;
  }
  if (expMiss || pubMiss) {
    failed += 1;
    console.log(`FAIL enclose exp points outside: op ${expMiss}/${pts.length}, E(x,1) ${pubMiss}/${pts.length}`);
  }
  // B3: the stretch e^d − 1 for a radius below and near one unit of the 300th place.
  for (const ir of ["1e-310", "3.4e-299", "1.9e-298"]) {
    const out = ballOps.cexp(pointBall(0, "1e-20", 0, ir));
    const [tr, ti] = rExp(new R(0), new R("1e-20").add(ir));
    if (missed(out, tr, ti)) {
      failed += 1;
      console.log("FAIL enclose exp stretch", ir, out.ir.toExponential(3));
    }
  }
  // B6: ln of float points, including |z| near 1 where ln|z| is tiny.
  const rnd2 = lcg(777);
  const lpts: Array<[number, number]> = [[0.6, 0.8], [0.28, 0.96], [0.8, 0.6], [Math.SQRT1_2, Math.SQRT1_2]];
  for (let i = 0; i < sample.lnPoints; i += 1) lpts.push([(rnd2() - 0.5) * 8, (rnd2() - 0.5) * 8]);
  for (let i = 0; i < sample.circlePoints; i += 1) {
    const t = rnd2() * 6.28;
    lpts.push([Math.cos(t), Math.sin(t)]);
  }
  let lnMiss = 0;
  for (const [a, b] of lpts) {
    const out = ballOps.cln(ballOps.point(a, b));
    if (out.cut || out.overflow) continue;
    const [tr, ti] = rLn(new R(a), new R(b));
    if (missed(out, tr, ti)) lnMiss += 1;
  }
  if (lnMiss) {
    failed += 1;
    console.log(`FAIL enclose ln points outside: ${lnMiss}/${lpts.length}`);
  }
  // B4: a ball resting on the negative axis from above holds −1 + 0i (−π) and points near +π.
  const edge = pointBall(-1, "1e-10", 0, "1e-10");
  if (!ballOps.straddlesCut(edge) || !ballOps.cln(edge).cut) {
    failed += 1;
    console.log("FAIL enclose cut edge imLo = 0 not a cut");
  }
  if (!ballOps.straddlesCut(pointBall(-1, 0, 0, "1e-10"))) {
    failed += 1;
    console.log("FAIL enclose straddling ball not a cut");
  }
  // imHi = 0 and below: every value is on the lower bank with the axis, so no cut.
  for (const im of ["-1e-10", "-2e-10"]) {
    if (ballOps.straddlesCut(pointBall(-1, im, 0, "1e-10"))) {
      failed += 1;
      console.log("FAIL enclose lower-bank ball called a cut", im);
    }
  }
  // End to end: every pure circuit with up to 8 leaves.
  failed += pureCircuits(sample.leaves);
  return failed;
}

function pureCircuits(maxLeaves: number): number {
  const byN: string[][] = [[], ["1"]];
  for (let n = 2; n <= maxLeaves; n += 1) {
    const list: string[] = [];
    for (let k = 1; k < n; k += 1) for (const a of byN[k]) for (const b of byN[n - k]) list.push(`${a}${b}E`);
    byN.push(list);
  }
  let checked = 0;
  let miss = 0;
  const first: string[] = [];
  for (const rpn of byN.flat()) {
    const nodes: Node[] = [];
    const vals: Array<[Decimal, Decimal] | null> = [];
    for (const ch of rpn) {
      if (ch === "1") {
        nodes.push(ONE);
        vals.push([new R(1), new R(0)]);
        continue;
      }
      const b = nodes.pop() as Node;
      const a = nodes.pop() as Node;
      nodes.push(E(a, b));
      const vb = vals.pop() ?? null;
      const va = vals.pop() ?? null;
      if (!va || !vb || va[0].gt(1e5) || (vb[0].isZero() && vb[1].isZero())) {
        vals.push(null);
        continue;
      }
      const [er, ei] = rExp(va[0], va[1]);
      const [lr, li] = rLn(vb[0], vb[1]);
      vals.push(er.isFinite() ? [er.sub(lr), ei.sub(li)] : null);
    }
    const truth = vals[0];
    const ball = enclose(nodes[0]);
    if (!truth || ball.cut || ball.overflow || !ball.rr.isFinite() || !ball.ir.isFinite()) continue;
    checked += 1;
    if (missed(ball, truth[0], truth[1])) {
      miss += 1;
      if (first.length < 3) first.push(rpn);
    }
  }
  if (miss || checked < (maxLeaves >= 8 ? 400 : 100)) {
    console.log(`FAIL enclose pure circuits ≤ ${maxLeaves} leaves: ${miss} outside of ${checked}`, first.join(" "));
    return 1;
  }
  return 0;
}
