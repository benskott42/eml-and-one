import Decimal from "decimal.js";
import { isMarkedExactInt } from "./lowering";
import { provenInteger, type Node } from "./node";

/**
 * A rigorous enclosure of a circuit's value, used to confirm a result that a
 * size rule would refuse. Each component is a center and a radius that bounds
 * the distance to the true value of the gates, read the way exact mode reads
 * them: exp(x) − ln(y), Arg = −π on the negative real axis, ln(±0) = −∞ with the
 * zero's signs, exp(−∞ + iθ) a signed 0, and exp(+∞ + iθ) on an axis when cos θ
 * or sin θ is under 10^(−15). Every rounding and each operand's own radius widen
 * it, so a term absorbed into a large value and cancelled later leaves a radius
 * as large as that value: (π + e^400) − e^400 − π is not confirmed at any
 * precision below about 400 digits.
 *
 * A component with `exact` is known exactly: its true value is the center,
 * signed zeros and ±∞ included. An imaginary part can also be an exact multiple
 * of π (`q`): ln of an exact negative real is −iπ, and exp of i·kπ/2 lies exactly
 * on an axis.
 *
 * Circuits build 0 from identities such as e − ln(exp(e)), and then take ln of
 * that 0, so rounding alone cannot follow them. A ball also carries a key: its
 * exact value as an integer combination of atoms (a leaf, exp of a key, ln of a
 * key). Keys that subtract to the empty combination are an exact 0. Two identities
 * hold under this cut: ln(exp(X)) = X when Im X lies in [−π, π), and
 * exp(ln(Y)) = Y when Y is finite and not 0.
 *
 * Where a ball meets the negative real axis, ln has two candidates (Arg near −π
 * and near +π), and exp(±∞ + iθ) one per sign the angle allows. Every candidate
 * is carried; candidates that exp brings back together are merged. The value is
 * confirmed only if every candidate confirms it.
 *
 * decimal.js rounds +, −, ×, √ correctly and exp, ln, sin, cos and atan2 to
 * within an ulp; each is counted here as up to 10 ulps.
 */
type Comp = { v: Decimal; r: Decimal; exact: boolean; q?: number };
type Ball = { re: Comp; im: Comp; key?: number };

class BallFail extends Error {}

export type BallValue = { re: Decimal | number; im: Decimal | number };

const MAX_BRANCHES = 8;

/**
 * True when every enclosure candidate at `precision` digits shows each nonzero
 * component of `value` correct to `agree` digits and each zero component exactly 0.
 * A 0 the keys cannot prove (circuits also build 0 through products such as
 * exp(a)·exp(−a), and only the gates' snap makes it exact) leaves the ball unable
 * to take its ln, and the value is not confirmed.
 */
export function ballConfirmsValue(
  root: Node,
  env: Record<string, BallValue>,
  value: { re: Decimal; im: Decimal },
  precision: number,
  agree: number,
  budget: { maxNodes?: number; deadline?: number } = {},
): boolean {
  const maxNodes = budget.maxNodes ?? 400_000;
  const deadline = budget.deadline ?? 0;
  const P = Math.max(precision, 40);
  const B = Decimal.clone({ precision: P, minE: -9e15, maxE: 9e15 });
  const eps = new B(10).pow(1 - P);
  const ten = eps.mul(10);
  const pi = B.acos(-1);
  const piLow = pi.mul(new B(1).sub(ten));
  const zero = new B(0);
  const ZERO: Comp = { v: zero, r: zero, exact: true };
  const NEG_ZERO: Comp = { v: new B(-0), r: zero, exact: true };
  const signedZero = (neg: boolean): Comp => (neg ? NEG_ZERO : ZERO);
  const infinite = (neg: boolean): Comp => ({ v: new B(neg ? -Infinity : Infinity), r: zero, exact: true });
  const isExactZero = (c: Comp) => c.exact && c.v.isZero();
  const isInf = (c: Comp) => !c.v.isFinite() && !c.v.isNaN();
  const zeroVector = (x: Ball) => isExactZero(x.re) && isExactZero(x.im);
  const fail = (): never => {
    throw new BallFail();
  };
  /** Rounding of one correctly rounded result: an ulp of `w`. */
  const ulp = (w: Decimal) => w.abs().mul(eps);

  // Keys: interned integer combinations of atoms.
  const ids = new Map<string, number>();
  const combos: Map<number, number>[] = [];
  const keyOf = (combo: Map<number, number>): number => {
    const text = [...combo.entries()]
      .filter(([, c]) => c !== 0)
      .sort((x, y) => x[0] - y[0])
      .map(([a, c]) => `${a}:${c}`)
      .join(";");
    let id = ids.get(`C${text}`);
    if (id === undefined) {
      id = combos.length;
      ids.set(`C${text}`, id);
      combos.push(new Map([...combo.entries()].filter(([, c]) => c !== 0)));
    }
    return id;
  };
  const EMPTY = keyOf(new Map());
  const atomIds = new Map<string, number>();
  const atom = (text: string): number => {
    let a = atomIds.get(text);
    if (a === undefined) {
      a = atomIds.size + 1;
      atomIds.set(text, a);
    }
    return keyOf(new Map([[a, 1]]));
  };
  const keyDiff = (a: number, b: number): number => {
    const out = new Map(combos[a]);
    for (const [k, c] of combos[b] ?? []) out.set(k, (out.get(k) ?? 0) - c);
    return keyOf(out);
  };
  /** The ball each exp atom was taken of, and each ln atom of. */
  const expArg = new Map<number, Ball>();
  const lnArg = new Map<number, Ball>();

  const zeroBall = (re: Comp, im: Comp): Ball => {
    const key = !re.v.isNeg() && !im.v.isNeg() ? EMPTY : atom(`Z${re.v.isNeg() ? "-" : "+"}${im.v.isNeg() ? "-" : "+"}`);
    return { re, im, key };
  };

  const fromQ = (q: number): Comp => {
    if (q === 0) return ZERO;
    const v = pi.mul(q);
    return { v, r: v.abs().mul(ten), exact: false, q };
  };

  const subComp = (a: Comp, b: Comp): Comp => {
    if (isInf(a) || isInf(b)) {
      if (isInf(a) && isInf(b)) {
        if (a.v.isNeg() === b.v.isNeg()) fail();
        return a;
      }
      return isInf(a) ? a : infinite(!b.v.isNeg());
    }
    // Signed zeros follow IEEE subtraction, as decimal.js and exact mode do.
    if (isExactZero(a) && isExactZero(b)) {
      const v = a.v.sub(b.v);
      return v.isNeg() === a.v.isNeg() ? a : { v, r: zero, exact: true };
    }
    const qa = a.q ?? (isExactZero(a) ? 0 : undefined);
    const qb = b.q ?? (isExactZero(b) ? 0 : undefined);
    if (qa !== undefined && qb !== undefined) return fromQ(qa - qb);
    if (isExactZero(b)) return a;
    if (isExactZero(a)) return { v: b.v.neg(), r: b.r, exact: b.exact };
    const v = a.v.sub(b.v);
    if (!v.isFinite()) fail();
    return { v, r: a.r.add(b.r).add(ulp(v)), exact: false };
  };

  const subBall = (a: Ball, b: Ball): Ball => {
    const re = subComp(a.re, b.re);
    const im = subComp(a.im, b.im);
    if (re.exact && im.exact && re.v.isZero() && im.v.isZero()) return zeroBall(re, im);
    // a − 0 is a itself, signed zeros included.
    if (re === a.re && im === a.im) return a;
    if (a.key !== undefined && b.key !== undefined) {
      const key = keyDiff(a.key, b.key);
      // Two finite values with one exact value subtract to an exact +0.
      if (key === EMPTY && !isInf(re) && !isInf(im)) return zeroBall(ZERO, ZERO);
      return { re, im, key };
    }
    return { re, im };
  };

  /** cos and sin of an exact angle on an axis (0, ±1, signed zeros as exact mode snaps them), or null. */
  const axisTrig = (theta: Comp): { c: Decimal; s: Decimal } | null => {
    if (isExactZero(theta)) return { c: new B(1), s: theta.v };
    if (theta.q === undefined || !Number.isInteger(theta.q * 2)) return null;
    const k = (((theta.q * 2) % 4) + 4) % 4;
    return { c: new B(k === 0 ? 1 : k === 2 ? -1 : 0), s: new B(k === 1 ? 1 : k === 3 ? -1 : 0) };
  };

  /** Signs a cos or sin of the angle ball can take: both when the interval meets 0. */
  const signsOf = (value: Decimal, radius: Decimal): boolean[] => (radius.isZero() || value.abs().gt(radius) ? [value.isNeg()] : [false, true]);

  /** Y with exp(ln(Y)) = Y, signed zeros included: finite, not 0, and no −0 part (ln(−5 − 0i) is the cut's −π). */
  const roundTrips = (y: Ball): boolean => {
    if (!y.re.v.isFinite() || !y.im.v.isFinite()) return false;
    if ((isExactZero(y.re) && y.re.v.isNeg()) || (isExactZero(y.im) && y.im.v.isNeg())) return false;
    return y.re.v.abs().gt(y.re.r) || y.im.v.abs().gt(y.im.r);
  };

  /** Im X in [−π, π), where ln(exp(X)) is X under this cut. */
  const principal = (x: Ball): boolean => {
    if (!x.re.v.isFinite()) return false;
    if (isExactZero(x.im)) return true;
    if (x.im.q !== undefined) return x.im.q >= -1 && x.im.q < 1;
    return x.im.v.sub(x.im.r).gt(piLow.neg()) && x.im.v.add(x.im.r).lt(piLow);
  };

  const expBalls = (x: Ball): Ball[] => {
    if (x.re.v.isNaN() || x.im.v.isNaN() || !x.im.v.isFinite()) fail();
    if (x.key !== undefined) {
      // exp(ln(Y)) is Y.
      const y = lnArg.get(x.key);
      if (y && roundTrips(y)) return [y];
    }
    const key = x.key !== undefined ? atom(`E${x.key}`) : undefined;
    if (key !== undefined && !expArg.has(key)) expArg.set(key, x);
    const trig = axisTrig(x.im);
    const r = trig ? zero : x.im.r.add(ten);
    const cos = trig ? trig.c : x.im.v.cos();
    const sin = trig ? trig.s : x.im.v.sin();
    if (isInf(x.re)) {
      if (!x.re.exact) fail();
      const out: Ball[] = [];
      if (x.re.v.isNeg()) {
        // exp(−∞ + iθ) is 0 with the signs of cos θ and sin θ, which a later ln reads.
        for (const cNeg of signsOf(cos, r)) for (const sNeg of signsOf(sin, r)) out.push(zeroBall(signedZero(cNeg), signedZero(sNeg)));
        // One candidate is the value exp of that key; several are several values.
        return out.length === 1 ? [{ ...(out[0] as Ball), key }] : out;
      }
      // exp(+∞ + iθ): a cos or sin under 10^(−15) is that axis (a signed 0), any other ±∞.
      const snap = new B("1e-15");
      const parts = (value: Decimal): Comp[] => {
        if (value.abs().add(r).lt(snap)) return signsOf(value, r).map(signedZero);
        if (value.abs().sub(r).gte(snap)) return [infinite(value.isNeg())];
        return fail();
      };
      for (const re of parts(cos)) for (const im of parts(sin)) out.push({ re, im });
      return out.length === 1 ? [{ ...(out[0] as Ball), key }] : out;
    }
    if (!x.re.r.isFinite() || !x.im.r.isFinite()) fail();
    if (zeroVector(x)) return [{ re: { v: new B(1), r: zero, exact: true }, im: signedZero(x.im.v.isNeg()), key }];
    const m = x.re.v.exp();
    if (!m.isFinite() || m.isZero()) fail();
    const d = x.re.r.add(trig ? zero : x.im.r);
    // |e^(z+δ) − e^z| ≤ e^Re z · (e^|δ| − 1) ≤ e^Re z · |δ| e^|δ|.
    const spread = d.isZero() ? zero : m.mul(d).mul(d.exp()).mul(new B(1).add(ten));
    if (trig) {
      const part = (unit: Decimal): Comp => {
        if (unit.isZero()) return signedZero(unit.isNeg());
        if (x.re.exact && x.re.v.isZero()) return { v: unit, r: zero, exact: true };
        return { v: unit.isNeg() ? m.neg() : m, r: spread.add(m.mul(ten)), exact: false };
      };
      return [{ re: part(trig.c), im: part(trig.s), key }];
    }
    const round = m.mul(ten.mul(3));
    return [
      {
        re: { v: m.mul(cos), r: spread.add(round), exact: false },
        im: { v: m.mul(sin), r: spread.add(round), exact: false },
        key,
      },
    ];
  };

  const lnBalls = (y: Ball): Ball[] => {
    if (y.key !== undefined) {
      // ln(exp(X)) is X when Im X lies in [−π, π). ln(1) is +0 whatever the sign of the 0 that exp read.
      const x = expArg.get(y.key);
      if (x && principal(x)) return [isExactZero(x.re) && x.re.v.isNeg() ? { ...x, re: ZERO, key: undefined } : x];
    }
    const key = y.key !== undefined ? atom(`N${y.key}`) : undefined;
    if (key !== undefined && !lnArg.has(key)) lnArg.set(key, y);
    if (isInf(y.im) && isExactZero(y.re)) return [{ re: infinite(false), im: fromQ(y.im.v.isNeg() ? -0.5 : 0.5), key }];
    if (isInf(y.re) && isExactZero(y.im)) {
      // ln(+∞) is +∞; ln(−∞ ± 0i) is +∞ − iπ, on the cut.
      return [{ re: infinite(false), im: y.re.v.isNeg() ? fromQ(-1) : signedZero(y.im.v.isNeg()), key }];
    }
    if (!y.re.v.isFinite() || !y.im.v.isFinite()) fail();
    if (zeroVector(y)) return [{ re: infinite(true), im: y.re.v.isNeg() ? fromQ(-1) : signedZero(y.im.v.isNeg()), key }];
    if (isExactZero(y.im) && y.re.exact && y.re.v.eq(1)) return [{ re: ZERO, im: signedZero(y.im.v.isNeg()), key }];
    const reLo = y.re.v.sub(y.re.r);
    const reHi = y.re.v.add(y.re.r);
    const imLo = y.im.v.sub(y.im.r);
    const imHi = y.im.v.add(y.im.r);
    const rho = y.re.r.add(y.im.r);
    const h = B.hypot(y.re.v, y.im.v);
    const hl = h.mul(new B(1).sub(ten));
    if (!hl.isFinite() || hl.lte(rho)) fail();
    const ims: Comp[] = [];
    if (isExactZero(y.im)) {
      if (reLo.gt(0)) ims.push(signedZero(y.im.v.isNeg()));
      else if (reHi.lt(0)) ims.push(fromQ(-1));
      else fail();
    } else if (isExactZero(y.re)) {
      if (imLo.gt(0)) ims.push(fromQ(0.5));
      else if (imHi.lt(0)) ims.push(fromQ(-0.5));
      else fail();
    } else if (reLo.lte(0) && imLo.lte(0) && imHi.gte(0)) {
      // The rectangle meets the negative real axis, where Arg jumps from π to −π.
      // The true point is on or below it (Arg near −π) or above it (near +π):
      // carry both, each within asin(|Im|/|z|) ≤ (π/2)·|Im|/|z| of its end.
      if (!reHi.lt(0)) fail();
      const span = B.max(imLo.abs(), imHi.abs()).div(hl.sub(rho)).mul(1.6);
      if (!span.lt(1)) fail();
      const half = span.div(2);
      ims.push({ v: pi.neg().add(half), r: half.add(ten.mul(4)), exact: false });
      ims.push({ v: pi.sub(half), r: half.add(ten.mul(4)), exact: false });
    } else {
      // |Δ Arg| ≤ asin(ρ/|z|) ≤ (π/2)·ρ/|z|.
      ims.push({ v: B.atan2(y.im.v, y.re.v), r: rho.div(hl).mul(1.6).add(ten.mul(4)), exact: false });
    }
    const lnv = h.ln();
    // |ln|z+δ| − ln|z|| ≤ ρ/(|z| − ρ), plus the rounding of |z| and of ln.
    const spread = rho.isZero() ? zero : rho.div(hl.sub(rho)).mul(new B(1).add(ten));
    const re: Comp = { v: lnv, r: spread.add(ten).add(lnv.abs().mul(ten)), exact: false };
    // Two candidates are two values, so neither keeps the key.
    return ims.length === 1 ? [{ re, im: ims[0] as Comp, key }] : ims.map((im) => ({ re, im }));
  };

  /** One ball holding both, when they nearly coincide (two branches that exp brought back together). */
  const unite = (a: Ball, b: Ball): Ball | null => {
    if (a.key !== undefined && a.key === b.key) return a;
    const part = (x: Comp, y: Comp): Comp | null => {
      if (x.exact && y.exact) return x.v.eq(y.v) && x.v.isNeg() === y.v.isNeg() ? x : null;
      if (x.q !== undefined && x.q === y.q) return x;
      if (!x.v.isFinite() || !y.v.isFinite()) return null;
      const lo = B.min(x.v.sub(x.r), y.v.sub(y.r));
      const hi = B.max(x.v.add(x.r), y.v.add(y.r));
      const r = hi.sub(lo).div(2);
      if (r.gt(B.max(x.r, y.r).mul(4))) return null;
      const v = lo.add(r);
      return { v, r: r.add(ulp(v)), exact: false };
    };
    const re = part(a.re, b.re);
    const im = part(a.im, b.im);
    return re && im ? { re, im } : null;
  };

  const gate = (xs: Ball[], ys: Ball[]): Ball[] => {
    const out: Ball[] = [];
    const lns = ys.flatMap(lnBalls);
    for (const ex of xs.flatMap(expBalls)) {
      for (const l of lns) {
        let next = subBall(ex, l);
        for (let k = 0; k < out.length; k += 1) {
          const joined = unite(out[k] as Ball, next);
          if (joined) {
            out.splice(k, 1);
            next = joined;
            k = -1;
          }
        }
        out.push(next);
        if (out.length > MAX_BRANCHES) fail();
      }
    }
    return out;
  };

  const leaf = (re: Decimal.Value, im: Decimal.Value): Ball => {
    const a = new B(re);
    const b = new B(im);
    if (!a.isFinite() || !b.isFinite()) fail();
    const ball: Ball = { re: { v: a, r: zero, exact: true }, im: { v: b, r: zero, exact: true } };
    if (a.isZero() && b.isZero()) return zeroBall(ball.re, ball.im);
    return { ...ball, key: atom(`L${a.toString()},${b.toString()}`) };
  };

  const memo = new Map<Node, Ball[]>();
  let out: Ball[] | undefined;
  try {
    const stack: { n: Node; seen: boolean }[] = [{ n: root, seen: false }];
    let steps = 0;
    while (stack.length) {
      const frame = stack.pop();
      if (!frame) break;
      const n = frame.n;
      if (memo.has(n)) continue;
      if (++steps > maxNodes * 2) return false;
      if ((steps & 63) === 0 && deadline && performance.now() > deadline) return false;
      const big = isMarkedExactInt(n) ? provenInteger(n) : undefined;
      if (big !== undefined) memo.set(n, [leaf(big.toString(), 0)]);
      else if (n.type === "one") memo.set(n, [leaf(1, 0)]);
      else if (n.type === "input") memo.set(n, [leaf(n.value.re, n.value.im)]);
      else if (n.type === "var") {
        const v = env[n.name];
        if (!v) return false;
        memo.set(n, [leaf(v.re.toString(), v.im.toString())]);
      } else if (!frame.seen) {
        stack.push({ n, seen: true });
        stack.push({ n: n.b, seen: false });
        stack.push({ n: n.a, seen: false });
      } else {
        const a = memo.get(n.a);
        const b = memo.get(n.b);
        if (!a || !b) return false;
        memo.set(n, gate(a, b));
      }
    }
    out = memo.get(root);
  } catch (err) {
    if (err instanceof BallFail) return false;
    // decimal.js refuses a trig argument past its π table, among others.
    if (err instanceof Error && /DecimalError/.test(err.message)) return false;
    throw err;
  }
  if (!out || out.length === 0) return false;
  const tolerance = new B(10).pow(-agree);
  const confirms = (got: Decimal, c: Comp): boolean => {
    if (!got.isFinite() || !c.v.isFinite()) return false;
    if (got.isZero()) return isExactZero(c);
    if (isExactZero(c)) return false;
    const g = new B(got.toString());
    return g.sub(c.v).abs().add(c.r).lte(g.abs().mul(tolerance));
  };
  return out.every((ball) => confirms(value.re, ball.re) && confirms(value.im, ball.im));
}
