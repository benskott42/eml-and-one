import Decimal from "decimal.js";
import { EmlError, type Node } from "./node";

/**
 * A complex ball around a circuit value. The radii bound the rounding of
 * this working precision: a cancellation that is not an identity blows the
 * radius up. `cut` means some logarithm saw a ball that meets both sides of
 * the negative-real axis. That ball does not choose a branch.
 * Working precision sits above 240 digits so an exact identity has a radius
 * smaller than one unit in the 240th place, and the ball can certify it.
 */
export type Ball = { re: Decimal; im: Decimal; rr: Decimal; ir: Decimal; overflow: boolean; cut: boolean };

const D = Decimal.clone({ precision: 300 });
/**
 * Radii are rounded away from zero (up, for a nonnegative radius), and a radius
 * denominator toward zero (down). Centers keep round-half-up. decimal.js has no
 * directed transcendentals, so each exp, ln, sqrt, cos, sin and atan2 is padded by
 * whole ulps of its operands below, not only by an ulp of its result.
 */
const DU = Decimal.clone({ precision: 300, rounding: Decimal.ROUND_UP });
const DD = Decimal.clone({ precision: 300, rounding: Decimal.ROUND_DOWN });
/** One unit in the 299th place: an ulp of any value in [1, 10), as an absolute bound for |x| ≤ 1 times 10. */
const ULP1 = new DU(10).pow(1 - DU.precision);

function u(x: Decimal): Decimal {
  if (!x.isFinite() || x.isZero()) return new DU(0);
  return new DU(10).pow(x.e + 1 - D.precision);
}

/** a + b + … rounded up. */
function upSum(...terms: Decimal[]): Decimal {
  let acc = new DU(0);
  for (const t of terms) acc = acc.add(t);
  return acc;
}

function point(re: Decimal.Value, im: Decimal.Value = 0): Ball {
  return { re: new D(re), im: new D(im), rr: new D(0), ir: new D(0), overflow: false, cut: false };
}

function bad(): Ball {
  return { re: new D(NaN), im: new D(NaN), rr: new D(Infinity), ir: new D(Infinity), overflow: true, cut: false };
}

function cutBall(): Ball {
  return { re: new D(NaN), im: new D(NaN), rr: new D(Infinity), ir: new D(Infinity), overflow: false, cut: true };
}

function cadd(a: Ball, b: Ball): Ball {
  if (a.cut || b.cut) return cutBall();
  if (a.overflow || b.overflow) return bad();
  const re = a.re.add(b.re);
  const im = a.im.add(b.im);
  return {
    re,
    im,
    rr: upSum(a.rr, b.rr, u(re)),
    ir: upSum(a.ir, b.ir, u(im)),
    overflow: !re.isFinite() || !im.isFinite(),
    cut: false,
  };
}

function csub(a: Ball, b: Ball): Ball {
  return cadd(a, { ...b, re: b.re.neg(), im: b.im.neg() });
}

function cexp(z: Ball): Ball {
  if (z.cut) return cutBall();
  if (z.overflow || !z.re.isFinite() || !z.im.isFinite()) return bad();
  const mag = z.re.exp();
  if (!mag.isFinite()) return bad();
  const c = z.im.cos();
  const s = z.im.sin();
  const re = mag.mul(c);
  const im = mag.mul(s);
  // |exp(z + δ) − exp(z)| ≤ e^(Re z + rr)·(e^d − 1) for |δ| ≤ d = rr + ir, and e^d − 1 ≤ d·e^d.
  // exp(d) − 1 at 300 digits rounded to 0 for d < 10^(−300) and lost a digit near 3·10^(−299).
  const disk = upSum(z.rr, z.ir);
  const grow = new DU(z.re).add(z.rr).exp().mul(new DU(1).add(ULP1));
  const stretch = disk.isZero() ? new DU(0) : grow.mul(disk).mul(disk.exp());
  // mag and cos/sin each carry up to an ulp. |c|, |s| ≤ 1, so each product is off by at
  // most mag·10^(−299) per factor, plus its own rounding. u(re) alone missed that when
  // |re| fell a decade below mag (654 of 3010 float points outside the ball).
  const trig = new DU(mag).mul(ULP1).mul(3);
  return { re, im, rr: upSum(stretch, trig, u(re)), ir: upSum(stretch, trig, u(im)), overflow: false, cut: false };
}

/**
 * The imag interval meets the axis from above and the real interval meets (−∞, 0).
 * The negative axis itself is the lower bank (−π), so a ball with imLo ≤ 0 < imHi
 * holds values on both sides of the jump. imLo = 0 exactly was missed: re = −1,
 * im = 10^(−10) ± 10^(−10) gave +π while −1 + 0i in the ball is −π.
 * imLo ≤ imHi ≤ 0 stays on the lower bank and is not a cut.
 */
function straddlesCut(z: Ball): boolean {
  if (!z.re.isFinite() || !z.im.isFinite() || !z.rr.isFinite() || !z.ir.isFinite()) return false;
  const imLo = new DD(z.im).sub(z.ir);
  const imHi = new DU(z.im).add(z.ir);
  // decimal.js calls +0 positive, so compare with 0 rather than isPos().
  if (imLo.gt(0) || !imHi.gt(0)) return false;
  return new DD(z.re).sub(z.rr).isNeg() || z.re.sub(z.rr).isNeg();
}

function cln(z: Ball): Ball {
  if (z.cut) return cutBall();
  if (z.overflow) return bad();
  const mag2 = z.re.mul(z.re).add(z.im.mul(z.im));
  const reach = z.rr.add(z.ir);
  if (mag2.sqrt().lte(reach)) return bad();
  if (straddlesCut(z)) return cutBall();
  const mag = mag2.sqrt();
  const re = mag.ln();
  const negPi = D.acos(-1).neg();
  const im = z.im.isZero() && z.re.isNeg() ? negPi : D.atan2(z.im, z.re);
  // The squares, their sum and the root are each rounded: |mag| is off by a relative
  // 3·10^(−299) at most, and ln turns that into an absolute 3·10^(−299). u(re) alone missed it
  // when ln|z| is tiny: ln(√½ + √½ i) was off by 3·10^15 of its radius.
  const room = new DD(mag).sub(reach);
  const spread = new DU(reach).div(room);
  const roundRe = ULP1.mul(4);
  const roundIm = u(im).mul(2);
  const rr = upSum(spread, roundRe, u(re));
  const ir = upSum(spread, new DU(z.ir).abs().add(z.rr).div(new DD(mag)), roundIm);
  return { re, im, rr, ir, overflow: !re.isFinite() || !im.isFinite(), cut: false };
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
  const tol = new D(10).pow(-240);
  const scale = D.max(goal.abs(), 1);
  return center.sub(goal).abs().add(radius).lte(scale.mul(tol));
}

/**
 * A float target carries about one ulp of its own rounding. Zero does not:
 * a target of 0 is the exact integer 0. Separation has to clear that slack
 * and the ball radius. 10^(−15) is a few ulps, far inside the old 10^(−9)
 * test that accepted −1 + 10^(−1 000 000).
 */
function separated(center: Decimal, radius: Decimal, target: number): boolean {
  // The same goal as certifies: π, −π and e are the constants, not their floats.
  const goal = exactGoal(target);
  const slack = target === 0 ? new D(0) : new D(Math.max(1, Math.abs(target))).mul("1e-15");
  return center.sub(goal).abs().gt(radius.add(slack));
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

/** The ball operations, for the containment checks. */
export const ballOps = { point, cexp, cln, cemi, straddlesCut };
