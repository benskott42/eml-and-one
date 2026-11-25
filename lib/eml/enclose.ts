import Decimal from "decimal.js";
import { EmlError, type Node } from "./node";

/**
 * A complex ball around a circuit value. Centers are evaluated at 300 digits
 * (ROUND_HALF_UP), while radii use directed upward rounding (DU, ROUND_UP) and
 * lower bounds use directed downward rounding (DD, ROUND_DOWN), following
 * docs/design/ball-soundness.md. `cut` means some logarithm saw a ball that
 * touches or crosses the negative-real axis. That ball does not choose a branch.
 */
export type Ball = { re: Decimal; im: Decimal; rr: Decimal; ir: Decimal; overflow: boolean; cut: boolean };

const PRECISION = 300;
const D = Decimal.clone({ precision: PRECISION, rounding: Decimal.ROUND_HALF_UP });
const DU = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_UP });
const DD = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_DOWN });

const ZERO_U = new DU(0);
const ZERO_D = new DD(0);
const ONE_U = new DU(1);
const ONE_D = new DD(1);
const EPS_U = new DU(10).pow(1 - PRECISION);
const DU_BUMP = new DU("1.000000000000000001");

function up(x: Decimal): Decimal {
  return new DU(x.abs()).add(ZERO_U);
}

function dn(x: Decimal): Decimal {
  return new DD(x.abs()).add(ZERO_D);
}

function u(x: Decimal): Decimal {
  if (!x.isFinite() || x.isZero()) return ZERO_U;
  return up(x).mul(EPS_U);
}

function point(re: Decimal.Value, im: Decimal.Value = 0): Ball {
  return { re: new D(re), im: new D(im), rr: ZERO_U, ir: ZERO_U, overflow: false, cut: false };
}

function bad(): Ball {
  return { re: new D(NaN), im: new D(NaN), rr: new DU(Infinity), ir: new DU(Infinity), overflow: true, cut: false };
}

function cutBall(): Ball {
  return { re: new D(NaN), im: new D(NaN), rr: new DU(Infinity), ir: new DU(Infinity), overflow: false, cut: true };
}

function cadd(a: Ball, b: Ball): Ball {
  if (a.cut || b.cut) return cutBall();
  if (a.overflow || b.overflow) return bad();
  const re = a.re.add(b.re);
  const im = a.im.add(b.im);
  const rr = a.rr.add(b.rr).add(u(re));
  const ir = a.ir.add(b.ir).add(u(im));
  return {
    re,
    im,
    rr,
    ir,
    overflow: !re.isFinite() || !im.isFinite() || !rr.isFinite() || !ir.isFinite(),
    cut: false,
  };
}

function csub(a: Ball, b: Ball): Ball {
  return cadd(a, { ...b, re: b.re.neg(), im: b.im.neg() });
}

function cexp(z: Ball): Ball {
  if (z.cut) return cutBall();
  if (z.overflow || !z.re.isFinite() || !z.im.isFinite()) return bad();
  let mag: Decimal;
  let c: Decimal;
  let s: Decimal;
  try {
    mag = z.re.exp();
    if (!mag.isFinite()) return bad();
    c = z.im.cos();
    s = z.im.sin();
  } catch {
    return bad();
  }
  const re = mag.mul(c);
  const im = mag.mul(s);
  const rho = z.rr.add(z.ir);
  const magUp = up(mag).mul(ONE_U.add(EPS_U.mul(2)));
  // Polynomial bound e^ρ − 1 ≤ ρ(1 + ρ) for ρ ≤ 1 avoids exp(ρ) − 1 cancellation;
  // for ρ > 1, e^ρ − 1 ≤ ρ·e^ρ · DU_BUMP. Charge 8u·M↑ on both parts.
  const eRho = rho.isZero()
    ? ZERO_U
    : rho.lte(1)
      ? rho.mul(ONE_U.add(rho))
      : rho.mul(rho.exp()).mul(DU_BUMP);
  const rad = magUp.mul(eRho.add(EPS_U.mul(8)));
  if (!re.isFinite() || !im.isFinite() || !rad.isFinite()) return bad();
  return { re, im, rr: rad, ir: rad, overflow: false, cut: false };
}

/**
 * The rectangle touches or crosses the negative real axis from above
 * (imLo ≤ 0 < imHi and reLo < 0). Exact center-vs-radius comparisons only.
 */
function straddlesCut(z: Ball): boolean {
  if (!z.re.isFinite() || !z.im.isFinite() || !z.rr.isFinite() || !z.ir.isFinite()) return false;
  // imLo ≤ 0 ⟺ im ≤ ir; imHi > 0 ⟺ im > −ir; reLo < 0 ⟺ re < rr.
  const imLoLeZero = z.im.lte(z.ir);
  const imHiGtZero = z.im.gt(z.ir.neg());
  const reLoLtZero = z.re.lt(z.rr);
  return imLoLeZero && imHiGtZero && reLoLtZero;
}

function cln(z: Ball): Ball {
  if (z.cut) return cutBall();
  if (z.overflow || !z.re.isFinite() || !z.im.isFinite()) return bad();
  // Contains 0 ⟺ |x| ≤ rr and |y| ≤ ir.
  if (z.re.abs().lte(z.rr) && z.im.abs().lte(z.ir)) return bad();
  if (straddlesCut(z)) return cutBall();
  const rho = z.rr.add(z.ir);
  // Lower bound on dist(0, Z) computed on DD: max(|x|−rr, |y|−ir, 0).
  const dx = z.re.abs().gt(z.rr) ? dn(z.re).sub(new DU(z.rr)) : ZERO_D;
  const dy = z.im.abs().gt(z.ir) ? dn(z.im).sub(new DU(z.ir)) : ZERO_D;
  const d = DD.max(dx, dy);
  if (!d.isFinite() || d.lte(0)) return bad();
  const mag2 = z.re.mul(z.re).add(z.im.mul(z.im));
  if (!mag2.isFinite() || mag2.lte(0)) return bad();
  const re = mag2.ln().div(2);
  const negPi = D.acos(-1).neg();
  const im = z.im.isZero() && z.re.isNeg() ? negPi : D.atan2(z.im, z.re);
  const lip = rho.div(d);
  const rr = lip.add(EPS_U.mul(ONE_U.add(up(re).mul(2))));
  const ir = lip.add(EPS_U.mul(2));
  return {
    re,
    im,
    rr,
    ir,
    overflow: !re.isFinite() || !im.isFinite() || !rr.isFinite() || !ir.isFinite(),
    cut: false,
  };
}

function cemi(x: Ball, y: Ball): Ball {
  return csub(cexp(x), cln(y));
}

/** Outward ball for a pure circuit. Overflow anywhere in the dag sets the flag. */
export function enclose(root: Node): Ball {
  const memo = new Map<Node, Ball>();
  const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
  const visiting = new Set<Node>();
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (!n) throw new EmlError("Could not evaluate this circuit.");
    if (memo.has(n)) continue;
    if (n.type === "one") {
      memo.set(n, point(1));
      continue;
    }
    if (n.type === "input") {
      memo.set(n, point(n.value.re, n.value.im));
      continue;
    }
    if (n.type === "var") throw new EmlError("An enclosure needs a value for every variable.");
    if (!n.a || !n.b) throw new EmlError("Could not evaluate this circuit.");
    if (!frame.seen) {
      if (visiting.has(n)) throw new EmlError("Could not evaluate this circuit.");
      visiting.add(n);
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    visiting.delete(n);
    const a = memo.get(n.a);
    const b = memo.get(n.b);
    if (!a || !b) throw new EmlError("Could not evaluate this circuit.");
    memo.set(n, cemi(a, b));
  }
  const out = memo.get(root);
  if (!out) throw new EmlError("Could not evaluate this circuit.");
  return out;
}

function exactGoal(target: number): Decimal {
  if (target === Math.PI) return D.acos(-1);
  if (target === -Math.PI) return D.acos(-1).neg();
  if (target === Math.E) return D.exp(1);
  return new D(target);
}

/** The whole interval lies inside a 240-digit neighborhood of the target. */
function certifies(center: Decimal, radius: Decimal, target: number): boolean {
  const goal = exactGoal(target);
  const tol = new DD(10).pow(-240);
  const scale = DD.max(dn(goal), ONE_D);
  const diff = center.sub(goal);
  return up(diff).add(u(diff)).add(radius).lte(scale.mul(tol));
}

/**
 * A float target carries about one ulp of its own rounding. Zero does not:
 * a target of 0 is the exact integer 0. Separation has to clear that slack
 * and the ball radius. 10^(−15) is a few ulps, far inside the old 10^(−9)
 * test that accepted −1 + 10^(−1 000 000).
 */
function separated(center: Decimal, radius: Decimal, target: number): boolean {
  const goal = exactGoal(target);
  const slack = target === 0 ? ZERO_U : new DU(Math.max(1, Math.abs(target))).mul("1e-15");
  const diff = center.sub(goal);
  return dn(diff).gt(radius.add(slack).add(u(diff)));
}

/**
 * `equal` when every point of the ball agrees with the target to 240 digits.
 * A zero part certifies only inside 10^(−240), which a rounding radius at
 * this precision can meet and a hidden residue cannot. `unequal` when the
 * target lies strictly outside the ball, past a float ulp. A ball that
 * contains the target and something else, or that straddled the cut, is
 * `unknown`.
 */
export function ballVerdict(ball: Ball, targetRe: number, targetIm: number): "equal" | "unequal" | "unknown" {
  if (ball.cut || ball.overflow) return "unknown";
  if (!ball.re.isFinite() || !ball.im.isFinite() || !ball.rr.isFinite() || !ball.ir.isFinite()) return "unknown";
  if (certifies(ball.re, ball.rr, targetRe) && certifies(ball.im, ball.ir, targetIm)) return "equal";
  if (separated(ball.re, ball.rr, targetRe) || separated(ball.im, ball.ir, targetIm)) return "unequal";
  return "unknown";
}

/** True only when the enclosure certifies 240-digit agreement with the target. */
export function ballConfirms(ball: Ball, targetRe: number, targetIm: number): boolean {
  return ballVerdict(ball, targetRe, targetIm) === "equal";
}
