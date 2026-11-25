import Decimal from "decimal.js";
import { exactDecimalOf, exactRationalOf, factsOf, isExactUnsure, isUnverified, provenInteger } from "./facts";
import type { Node } from "./node";

/**
 * A rigorous enclosure of a circuit's value, used to confirm a result that a
 * size rule would refuse. Each component is a center (computed on B with
 * ROUND_HALF_UP at precision P) and a radius (computed on DU with ROUND_UP at
 * 20 digits, with lower bounds on DD with ROUND_DOWN) that bounds the distance
 * to the true value of the gates, read the way exact mode reads them:
 * exp(x) − ln(y), Arg = −π on the negative real axis, ln(±0) = −∞ with the
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
 */
type Comp = { v: Decimal; r: Decimal; exact: boolean; q?: number; key?: number };
type Ball = { re: Comp; im: Comp; key?: number };

class BallFail extends Error {
  constructor(reason = "fail") {
    super(reason);
  }
}

export type BallCompOut = { v: Decimal; r: Decimal; exact: boolean };
export type BallOut = { re: BallCompOut; im: BallCompOut };
export type BallEncloseResult = { ok: true; balls: BallOut[] } | { ok: false; reason: string };

export type BallValue = { re: Decimal | number; im: Decimal | number };

const MAX_BRANCHES = 8;

// Directed rounding clones for radii (upper bounds) and denominators (lower bounds).
const DU = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_UP, minE: -9e15, maxE: 9e15 });
const DD = Decimal.clone({ precision: 20, rounding: Decimal.ROUND_DOWN, minE: -9e15, maxE: 9e15 });
const zeroU = new DU(0);
const zeroD = new DD(0);
const oneU = new DU(1);
const oneD = new DD(1);
// new DU(x) does not round until an operation; adding 0 forces directed rounding.
const up = (w: Decimal): Decimal => new DU(w.abs()).add(zeroU);
const dn = (w: Decimal): Decimal => new DD(w.abs()).add(zeroD);
const duBump = new DU("1.000000000000000001"); // 1 + 10^(1 - 20) * 10 for transcendental DU ops
const snapU = new DU("1e-15");
const snapD = new DD("1e-15");

type PrecCtx = {
  B: Decimal.Constructor;
  L: Decimal.Constructor;
  zeroB: Decimal;
  oneB: Decimal;
  negOneB: Decimal;
  epsU: Decimal;
  tenU: Decimal;
  pi: Decimal;
  piL: Decimal;
  ln10L?: Decimal;
  piLowD: Decimal;
  ZERO: Comp;
  NEG_ZERO: Comp;
  epsL: Decimal;
};

const precCache = new Map<number, PrecCtx>();

function lnReducedL(x: Decimal, L: Decimal.Constructor, epsL: Decimal): Decimal {
  // Repeatedly take square roots until |x - 1| < 0.05, then use 2*artanh((x-1)/(x+1)).
  // Never calls decimal.js's built-in LN10 table (which caps out around 500-1000 digits).
  let r = new L(x);
  let k = 0;
  while (r.sub(1).abs().gt("0.05") && k < 16) {
    r = r.sqrt();
    k += 1;
  }
  const u = r.sub(1).div(r.plus(1));
  const u2 = u.mul(u);
  let term = u;
  let sum = u;
  for (let n = 3; term.abs().gt(epsL) && n < 4001; n += 2) {
    term = term.mul(u2);
    sum = sum.plus(term.div(n));
  }
  return sum.mul(2 * (1 << k));
}

function precCtx(P: number): PrecCtx {
  let ctx = precCache.get(P);
  if (ctx) return ctx;
  const B = Decimal.clone({ precision: P, rounding: Decimal.ROUND_HALF_UP, minE: -9e15, maxE: 9e15 });
  const L = Decimal.clone({ precision: P + 12, rounding: Decimal.ROUND_HALF_UP, minE: -9e15, maxE: 9e15 });
  const zeroB = new B(0);
  const oneB = new B(1);
  const negOneB = new B(-1);
  const epsU = new DU(10).pow(1 - P);
  const tenU = epsU.mul(10);
  const pi = B.acos(-1);
  const piL = L.acos(-1);
  const epsL = new L(10).pow(-(P + 10));
  const piLowD = dn(pi).mul(oneD.sub(new DD(tenU)));
  const ZERO: Comp = { v: zeroB, r: zeroU, exact: true };
  const NEG_ZERO: Comp = { v: new B(-0), r: zeroU, exact: true };
  ctx = { B, L, zeroB, oneB, negOneB, epsU, tenU, pi, piL, piLowD, ZERO, NEG_ZERO, epsL };
  precCache.set(P, ctx);
  return ctx;
}

function atan2FastCore(y: Decimal, x: Decimal, ctx: PrecCtx): Decimal | null {
  const { L, epsL } = ctx;
  const shift = Math.max(y.e, x.e);
  const scale = new L(10).pow(-shift);
  const Y = new L(y);
  const X = new L(x);
  const ys = Y.mul(scale).toNumber();
  const xs = X.mul(scale).toNumber();
  if (!Number.isFinite(ys) || !Number.isFinite(xs) || (ys === 0 && xs === 0)) return null;
  const seed = Math.atan2(ys, xs);
  const th = new L(seed);
  const { c, s } = cosSinL(th, ctx);
  const t = Y.mul(c).sub(X.mul(s)).div(X.mul(c).plus(Y.mul(s)));
  if (!t.isFinite() || t.abs().gt("1e-8")) return null;
  const t2 = t.mul(t);
  let term = t;
  let sum = t;
  for (let n = 3; term.abs().gt(epsL) && n < 4001; n += 2) {
    term = term.mul(t2).neg();
    sum = sum.plus(term.div(n));
  }
  if (term.abs().gt(epsL)) return null;
  return th.plus(sum);
}

function cosSinSmallL(r: Decimal, L: Decimal.Constructor, epsL: Decimal): { c: Decimal; s: Decimal } {
  try {
    return { c: r.cos(), s: r.sin() };
  } catch (err) {
    if (!(err instanceof Error) || !/DecimalError/.test(err.message)) throw err;
  }
  // Halve r until |r| < 0.1 so Taylor converges fast, then double back.
  let h = new L(r);
  let halves = 0;
  while (h.abs().gt("0.1") && halves < 12) {
    h = h.div(2);
    halves += 1;
  }
  const h2 = h.mul(h);
  let c = new L(1);
  let s = h;
  let cTerm = new L(1);
  let sTerm = h;
  for (let n = 1; (cTerm.abs().gt(epsL) || sTerm.abs().gt(epsL)) && n < 2000; n += 1) {
    cTerm = cTerm.mul(h2).neg().div((2 * n - 1) * (2 * n));
    sTerm = sTerm.mul(h2).neg().div((2 * n) * (2 * n + 1));
    c = c.plus(cTerm);
    s = s.plus(sTerm);
  }
  for (let j = 0; j < halves; j += 1) {
    const c2 = c.mul(c).sub(s.mul(s));
    const s2 = c.mul(s).mul(2);
    c = c2;
    s = s2;
  }
  return { c, s };
}

function cosSinL(theta: Decimal, ctx: PrecCtx): { c: Decimal; s: Decimal } {
  const { L, piL, epsL } = ctx;
  const thL = new L(theta);
  if (thL.abs().lt(1)) return cosSinSmallL(thL, L, epsL);
  const halfPi = piL.div(2);
  const kDec = thL.div(halfPi).toDecimalPlaces(0, Decimal.ROUND_HALF_UP);
  if (!kDec.isFinite() || kDec.abs().gt("1e12")) return cosSinSmallL(thL, L, epsL);
  const r = thL.sub(halfPi.mul(kDec));
  const { c, s } = cosSinSmallL(r, L, epsL);
  const k = ((kDec.toNumber() % 4) + 4) % 4;
  if (k === 0) return { c, s };
  if (k === 1) return { c: s.neg(), s: c };
  if (k === 2) return { c: c.neg(), s: s.neg() };
  return { c: s, s: c.neg() };
}

function cosSinBall(theta: Decimal, ctx: PrecCtx): { cos: Decimal; sin: Decimal } {
  const { B } = ctx;
  const { c, s } = cosSinL(theta, ctx);
  return { cos: new B(c), sin: new B(s) };
}

function lnPosBall(h: Decimal, ctx: PrecCtx): Decimal {
  try {
    return h.ln();
  } catch (err) {
    if (!(err instanceof Error) || !/DecimalError/.test(err.message)) throw err;
  }
  const { B, L, epsL } = ctx;
  const diff = h.sub(1);
  if (diff.isZero()) return ctx.zeroB;
  if (diff.abs().lt("0.05")) return new B(lnReducedL(h, L, epsL));
  const e = h.e;
  if (e === 0) return new B(lnReducedL(h, L, epsL));
  if (!ctx.ln10L) ctx.ln10L = lnReducedL(new L(10), L, epsL);
  const m = new L(h).div(new L(10).pow(e));
  const lnM = m.eq(1) ? new L(0) : lnReducedL(m, L, epsL);
  return new B(lnM.plus(ctx.ln10L.mul(e)));
}

function atan2Ball(y: Decimal, x: Decimal, ctx: PrecCtx): Decimal {
  if (!y.isZero() && !x.isZero()) {
    if (x.isNeg() && y.abs().lt(x.abs())) {
      const phi = atan2FastCore(y.abs(), x.neg(), ctx);
      if (phi) {
        const out = ctx.piL.sub(phi);
        return new ctx.B(y.isNeg() ? out.neg() : out);
      }
    } else {
      const th = atan2FastCore(y, x, ctx);
      if (th) return new ctx.B(th);
    }
  }
  return ctx.B.atan2(y, x);
}

/**
 * True when every enclosure candidate at `precision` digits shows each nonzero
 * component of `value` correct to `agree` digits and each zero component exactly 0.
 * A 0 the keys cannot prove (circuits also build 0 through products such as
 * exp(a)·exp(−a), and only the gates' snap makes it exact) leaves the ball unable
 * to take its ln, and the value is not confirmed.
 */
export function ballEnclose(
  root: Node,
  env: Record<string, BallValue>,
  precision: number,
  budget: { maxNodes?: number; deadline?: number } = {},
): BallEncloseResult {
  const maxNodes = budget.maxNodes ?? 400_000;
  const deadline = budget.deadline ?? 0;
  const P = Math.max(precision, 40);
  const ctx = precCtx(P);
  const { B, epsU, tenU, pi, piLowD, ZERO, NEG_ZERO } = ctx;
  const signedZero = (neg: boolean): Comp => (neg ? NEG_ZERO : ZERO);
  const infinite = (neg: boolean): Comp => ({ v: new B(neg ? -Infinity : Infinity), r: zeroU, exact: true });
  const isExactZero = (c: Comp) => c.exact && c.v.isZero();
  const isInf = (c: Comp) => !c.v.isFinite() && !c.v.isNaN();
  const zeroVector = (x: Ball) => isExactZero(x.re) && isExactZero(x.im);
  const fail = (reason = "fail"): never => {
    throw new BallFail(reason);
  };
  /** Upper bound on one ulp of `w` at precision P, computed on DU. */
  const ulp = (w: Decimal): Decimal => up(w).mul(epsU);

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
  const keyNeg = (a: number): number => keyDiff(EMPTY, a);
  /** Canonical representative of {k, -k} for even/odd real identities (cos, sin, ln|z|, atan2). */
  const absKey = (k: number): { k: number; neg: boolean } => {
    const combo = combos[k];
    if (!combo || combo.size === 0) return { k: EMPTY, neg: false };
    let minAtom = Infinity;
    let minCoeff = 0;
    for (const [a, c] of combo) {
      if (a < minAtom) {
        minAtom = a;
        minCoeff = c;
      }
    }
    return minCoeff < 0 ? { k: keyNeg(k), neg: true } : { k, neg: false };
  };
  const compKey = (c: Comp): number | undefined => c.key ?? (isExactZero(c) ? EMPTY : undefined);
  const ONE_KEY = atom("R1");
  const NEG_ONE_KEY = keyNeg(ONE_KEY);
  /** The ball each exp atom was taken of, and each ln atom of. */
  const expArg = new Map<number, Ball>();
  const lnArg = new Map<number, Ball>();
  const lnAtomArg = new Map<number, Ball>();
  /** Positive-real Comp whose ln produced this real-component key. */
  const lnMagArg = new Map<number, Comp>();

  const zeroBall = (re: Comp, im: Comp): Ball => {
    const key = !re.v.isNeg() && !im.v.isNeg() ? EMPTY : atom(`Z${re.v.isNeg() ? "-" : "+"}${im.v.isNeg() ? "-" : "+"}`);
    return { re, im, key };
  };

  const fromQ = (q: number): Comp => {
    if (q === 0) return ZERO;
    const v = pi.mul(q);
    return { v, r: up(v).mul(tenU), exact: false, q };
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
      return v.isNeg() === a.v.isNeg() ? a : { v, r: zeroU, exact: true };
    }
    const qa = a.q ?? (isExactZero(a) ? 0 : undefined);
    const qb = b.q ?? (isExactZero(b) ? 0 : undefined);
    if (qa !== undefined && qb !== undefined) return fromQ(qa - qb);
    if (isExactZero(b)) return a;
    if (isExactZero(a)) {
      const kb = compKey(b);
      return { v: b.v.neg(), r: b.r, exact: b.exact, ...(kb !== undefined ? { key: keyNeg(kb) } : {}) };
    }
    const ka = compKey(a);
    const kb = compKey(b);
    let key: number | undefined;
    if (ka !== undefined && kb !== undefined) {
      key = keyDiff(ka, kb);
      if (key === EMPTY) return ZERO;
    }
    const v = a.v.sub(b.v);
    if (!v.isFinite()) fail();
    return { v, r: a.r.add(b.r).add(ulp(v)), exact: false, ...(key !== undefined ? { key } : {}) };
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

  /** Signs a cos or sin of the angle ball can take: both when the interval meets 0 (exact comparison). */
  const signsOf = (value: Decimal, radius: Decimal): boolean[] => (radius.isZero() || value.abs().gt(radius) ? [value.isNeg()] : [false, true]);

  /** Y with exp(ln(Y)) = Y, signed zeros included: finite, not 0, and no −0 part (ln(−5 − 0i) is the cut's −π). */
  const roundTrips = (y: Ball): boolean => {
    if (!y.re.v.isFinite() || !y.im.v.isFinite()) return false;
    if ((isExactZero(y.re) && y.re.v.isNeg()) || (isExactZero(y.im) && y.im.v.isNeg())) return false;
    return y.re.v.abs().gt(y.re.r) || y.im.v.abs().gt(y.im.r);
  };

  /** Im X in [−π, π), where ln(exp(X)) is X under this cut. Uses upward-rounded |Im| + r < piLow. */
  const principal = (x: Ball): boolean => {
    if (!x.re.v.isFinite()) return false;
    if (isExactZero(x.im)) return true;
    if (x.im.q !== undefined) return x.im.q >= -1 && x.im.q < 1;
    return up(x.im.v).add(x.im.r).lt(piLowD);
  };

  const expBalls = (x: Ball): Ball[] => {
    if (x.re.v.isNaN() || x.im.v.isNaN() || !x.im.v.isFinite()) fail();
    if (x.key !== undefined) {
      // exp(ln(Y)) is Y.
      const y = lnArg.get(x.key);
      if (y && roundTrips(y)) return [y];
      // exp(ln(A) − ln(B)) is A / B for exact π-multiples and exact ±1, ±2, ±i.
      const combo = combos[x.key];
      if (combo && combo.size === 2) {
        let posAtom = -1;
        let negAtom = -1;
        for (const [aId, coeff] of combo) {
          if (coeff === 1) posAtom = aId;
          else if (coeff === -1) negAtom = aId;
        }
        if (posAtom !== -1 && negAtom !== -1) {
          const a = lnAtomArg.get(posAtom);
          const b = lnAtomArg.get(negAtom);
          if (a && b && roundTrips(a) && roundTrips(b)) {
            const key = atom(`E${x.key}`);
            if (!expArg.has(key)) expArg.set(key, x);
            if (isExactZero(a.re) && a.im.q !== undefined) {
              if (isExactZero(b.im) && b.re.exact && (b.re.v.abs().eq(1) || b.re.v.abs().eq(2))) {
                const q = a.im.q / b.re.v.toNumber();
                return [{ re: ZERO, im: fromQ(q), key }];
              }
              if (isExactZero(b.re) && b.im.exact && b.im.v.abs().eq(1)) {
                const q = a.im.q * b.im.v.toNumber();
                return [{ re: fromQ(q), im: ZERO, key }];
              }
            }
            if (isExactZero(a.im) && a.re.q !== undefined) {
              if (isExactZero(b.im) && b.re.exact && (b.re.v.abs().eq(1) || b.re.v.abs().eq(2))) {
                const q = a.re.q / b.re.v.toNumber();
                return [{ re: fromQ(q), im: ZERO, key }];
              }
            }
          }
        }
      }
    }
    const key = x.key !== undefined ? atom(`E${x.key}`) : undefined;
    if (key !== undefined && !expArg.has(key)) expArg.set(key, x);
    const trig = axisTrig(x.im);
    const r = trig ? zeroU : x.im.r.add(tenU);
    const cs = trig ? { cos: trig.c, sin: trig.s } : cosSinBall(x.im.v, ctx);
    const cos = cs.cos;
    const sin = cs.sin;
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
      const parts = (value: Decimal): Comp[] => {
        if (up(value).add(r).lt(snapD)) return signsOf(value, r).map(signedZero);
        if (value.abs().gt(r) && dn(value).sub(new DD(r)).gte(snapU)) return [infinite(value.isNeg())];
        return fail();
      };
      for (const re of parts(cos)) for (const im of parts(sin)) out.push({ re, im });
      return out.length === 1 ? [{ ...(out[0] as Ball), key }] : out;
    }
    if (!x.re.r.isFinite() || !x.im.r.isFinite()) fail();
    if (zeroVector(x)) return [{ re: { v: ctx.oneB, r: zeroU, exact: true, key: ONE_KEY }, im: signedZero(x.im.v.isNeg()), key }];
    const m = x.re.v.exp();
    if (!m.isFinite() || m.isZero()) fail();
    const mUp = up(m).mul(oneU.add(epsU.mul(2)));
    const d = x.re.r.add(trig ? zeroU : x.im.r);
    // |e^(z+δ) − e^z| ≤ e^Re z · (e^|δ| − 1).
    // For d ≤ 1: e^d − 1 ≤ d·(1 + d) (polynomial, no exp(d)−1 cancellation).
    // For d > 1: e^d − 1 ≤ d·e^d · duBump.
    let stretch = zeroU;
    if (!d.isZero()) {
      const factor = d.lte(1) ? d.mul(oneU.add(d)) : d.mul(d.exp()).mul(duBump);
      if (!factor.isFinite()) fail();
      stretch = mUp.mul(factor);
    }
    if (!stretch.isFinite()) fail();
    const rk = compKey(x.re);
    if (trig) {
      // exp(ln(A) + i·kπ/2) = A · i^k when A is a known positive real Comp (keeps exactness on 6*i, 4*i, 0.00005*i).
      if (rk !== undefined) {
        const mag = lnMagArg.get(rk);
        if (mag && !mag.v.isNeg() && mag.v.gt(mag.r)) {
          const rotComp = (unit: Decimal): Comp => {
            if (unit.isZero()) return signedZero(unit.isNeg());
            if (!unit.isNeg()) return mag;
            const mk = compKey(mag);
            return { v: mag.v.neg(), r: mag.r, exact: mag.exact, ...(mk !== undefined ? { key: keyNeg(mk) } : {}) };
          };
          return [{ re: rotComp(trig.c), im: rotComp(trig.s), key }];
        }
      }
      const ek = rk !== undefined ? atom(`RE${rk}`) : undefined;
      const part = (unit: Decimal): Comp => {
        if (unit.isZero()) return signedZero(unit.isNeg());
        if (x.re.exact && x.re.v.isZero()) {
          return { v: unit, r: zeroU, exact: true, key: unit.isNeg() ? NEG_ONE_KEY : ONE_KEY };
        }
        return {
          v: unit.isNeg() ? m.neg() : m,
          r: stretch.add(mUp.mul(tenU)),
          exact: false,
          ...(ek !== undefined ? { key: unit.isNeg() ? keyNeg(ek) : ek } : {}),
        };
      };
      return [{ re: part(trig.c), im: part(trig.s), key }];
    }
    const round = mUp.mul(epsU.mul(8));
    const rad = stretch.add(round);
    const ik = compKey(x.im);
    let cosKey: number | undefined;
    let sinKey: number | undefined;
    if (rk !== undefined && ik !== undefined) {
      const absIm = absKey(ik);
      cosKey = atom(`EC${rk},${absIm.k}`);
      const sinAtom = atom(`ES${rk},${absIm.k}`);
      sinKey = absIm.neg ? keyNeg(sinAtom) : sinAtom;
    }
    return [
      {
        re: { v: m.mul(cos), r: rad, exact: false, ...(cosKey !== undefined ? { key: cosKey } : {}) },
        im: { v: m.mul(sin), r: rad, exact: false, ...(sinKey !== undefined ? { key: sinKey } : {}) },
        key,
      },
    ];
  };

  const lnBalls = (y: Ball): Ball[] => {
    const key = y.key !== undefined ? atom(`N${y.key}`) : undefined;
    if (key !== undefined && !lnArg.has(key)) {
      lnArg.set(key, y);
      const aId = atomIds.get(`N${y.key}`);
      if (aId !== undefined) lnAtomArg.set(aId, y);
    }
    if (y.key !== undefined) {
      // ln(exp(X)) is X when Im X lies in [−π, π). For any exact half-integer q·π,
      // ln(exp(a + i·qπ)) = a + i·wrapLower(q)·π with the exact same real part a.
      const x = expArg.get(y.key);
      if (x && x.re.v.isFinite()) {
        if (principal(x)) return [isExactZero(x.re) && x.re.v.isNeg() ? { ...x, re: ZERO, key: undefined } : x];
        if (x.im.q !== undefined && Number.isInteger(x.im.q * 2)) {
          let q = (((x.im.q + 1) % 2) + 2) % 2 - 1;
          if (Object.is(q, -0)) q = 0;
          const re = isExactZero(x.re) && x.re.v.isNeg() ? ZERO : x.re;
          return [{ re, im: fromQ(q), key }];
        }
      }
    }
    if (isInf(y.im) && isExactZero(y.re)) return [{ re: infinite(false), im: fromQ(y.im.v.isNeg() ? -0.5 : 0.5), key }];
    if (isInf(y.re) && isExactZero(y.im)) {
      // ln(+∞) is +∞; ln(−∞ ± 0i) is +∞ − iπ, on the cut.
      return [{ re: infinite(false), im: y.re.v.isNeg() ? fromQ(-1) : signedZero(y.im.v.isNeg()), key }];
    }
    if (!y.re.v.isFinite() || !y.im.v.isFinite()) fail();
    if (zeroVector(y)) return [{ re: infinite(true), im: y.re.v.isNeg() ? fromQ(-1) : signedZero(y.im.v.isNeg()), key }];
    if (isExactZero(y.im) && y.re.exact && y.re.v.eq(1)) return [{ re: ZERO, im: signedZero(y.im.v.isNeg()), key }];
    if (isExactZero(y.im) && y.re.exact && y.re.v.eq(-1)) return [{ re: ZERO, im: fromQ(-1), key }];
    if (isExactZero(y.re) && y.im.exact && y.im.v.abs().eq(1)) return [{ re: ZERO, im: fromQ(y.im.v.isNeg() ? -0.5 : 0.5), key }];
    // Exact center-vs-radius comparisons (never v ± r under ROUND_HALF_UP).
    const reStrictlyPos = y.re.v.gt(y.re.r);
    const reStrictlyNeg = y.re.v.isNeg() && y.re.v.abs().gt(y.re.r);
    const reLoLeZero = !reStrictlyPos;
    const imStrictlyPos = y.im.v.gt(y.im.r);
    const imStrictlyNeg = y.im.v.isNeg() && y.im.v.abs().gt(y.im.r);
    const imContainsZero = y.im.v.abs().lte(y.im.r);
    if (y.re.v.abs().lte(y.re.r) && imContainsZero) fail();
    const rho = y.re.r.add(y.im.r);
    const h = B.hypot(y.re.v, y.im.v);
    if (!h.isFinite() || h.isZero()) fail();
    // Sound lower bound on dist(0, Z) computed on DD: max(|x|-rx, |y|-ry, |c|*(1-ten)-rho).
    const dx = y.re.v.abs().gt(y.re.r) ? dn(y.re.v).sub(new DU(y.re.r)) : zeroD;
    const dy = y.im.v.abs().gt(y.im.r) ? dn(y.im.v).sub(new DU(y.im.r)) : zeroD;
    const hLow = dn(h).mul(oneD.sub(new DD(tenU)));
    const hDist = hLow.gt(rho) ? hLow.sub(new DD(rho)) : zeroD;
    const dist = DD.max(dx, dy, hDist);
    if (!dist.isFinite() || dist.lte(0)) fail();
    const ims: Comp[] = [];
    if (isExactZero(y.im)) {
      if (reStrictlyPos) ims.push(signedZero(y.im.v.isNeg()));
      else if (reStrictlyNeg) ims.push(fromQ(-1));
      else fail();
    } else if (isExactZero(y.re)) {
      if (imStrictlyPos) ims.push(fromQ(0.5));
      else if (imStrictlyNeg) ims.push(fromQ(-0.5));
      else fail();
    } else if (reLoLeZero && imContainsZero) {
      // The rectangle meets the negative real axis, where Arg jumps from π to −π.
      // Carry both sides, each within asin(|Im|/|z|) ≤ (π/2)·|Im|/dist(0, Z).
      if (!reStrictlyNeg) fail();
      const imMax = up(y.im.v).add(y.im.r);
      const span = imMax.div(dist).mul("1.6");
      if (!span.lt(1)) fail();
      const half = span.div(2);
      const halfB = new B(half.toString());
      ims.push({ v: pi.neg().add(halfB), r: half.add(tenU.mul(4)), exact: false });
      ims.push({ v: pi.sub(halfB), r: half.add(tenU.mul(4)), exact: false });
    } else {
      // On any convex rectangle off the cut, |L(z) − L(c)| ≤ ρ / dist(0, Z).
      const yrk = compKey(y.re);
      const yik = compKey(y.im);
      let imKey: number | undefined;
      if (reStrictlyPos && yrk !== undefined && yik !== undefined) {
        const absIm = absKey(yik);
        const atAtom = atom(`AT${yrk},${absIm.k}`);
        imKey = absIm.neg ? keyNeg(atAtom) : atAtom;
      }
      ims.push({ v: atan2Ball(y.im.v, y.re.v, ctx), r: rho.div(dist).add(tenU.mul(4)), exact: false, ...(imKey !== undefined ? { key: imKey } : {}) });
    }
    const lnv = lnPosBall(h, ctx);
    // |ln|z+δ| − ln|z|| ≤ ρ / dist(0, Z), plus rounding of |z| and of ln.
    const spread = rho.isZero() ? zeroU : rho.div(dist);
    const yrk = compKey(y.re);
    const yik = compKey(y.im);
    const reKey = yrk !== undefined && yik !== undefined ? atom(`LM${absKey(yrk).k},${absKey(yik).k}`) : undefined;
    if (reKey !== undefined && !lnMagArg.has(reKey)) {
      if (isExactZero(y.im) && reStrictlyPos) lnMagArg.set(reKey, y.re);
      else if (isExactZero(y.im) && reStrictlyNeg) {
        const mk = compKey(y.re);
        lnMagArg.set(reKey, { v: y.re.v.neg(), r: y.re.r, exact: y.re.exact, ...(mk !== undefined ? { key: keyNeg(mk) } : {}) });
      } else if (isExactZero(y.re) && imStrictlyPos) lnMagArg.set(reKey, y.im);
      else if (isExactZero(y.re) && imStrictlyNeg) {
        const mk = compKey(y.im);
        lnMagArg.set(reKey, { v: y.im.v.neg(), r: y.im.r, exact: y.im.exact, ...(mk !== undefined ? { key: keyNeg(mk) } : {}) });
      }
    }
    const re: Comp = { v: lnv, r: spread.add(tenU).add(up(lnv).mul(tenU)), exact: false, ...(reKey !== undefined ? { key: reKey } : {}) };
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
      // Midpoint of the two centers, with radius enclosing both intervals on DU.
      const v = x.v.add(y.v).div(2);
      if (!v.isFinite()) return null;
      const dx = x.v.sub(v);
      const dy = y.v.sub(v);
      const rx = up(dx).add(ulp(dx)).add(x.r);
      const ry = up(dy).add(ulp(dy)).add(y.r);
      const r = DU.max(rx, ry).add(ulp(v));
      if (!r.isFinite() || r.gt(DU.max(x.r, y.r).mul(4))) return null;
      return { v, r, exact: false };
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

  const leafComp = (val: Decimal.Value): Comp => {
    const raw = new B(val);
    if (!raw.isFinite()) fail();
    // A wide exact integer (sd > P) would lose digits on the first rounded op on B;
    // round it into P digits up front and charge one ulp to its radius.
    if (raw.sd() > P) {
      const v = raw.toSignificantDigits(P);
      return { v, r: ulp(v), exact: false };
    }
    if (raw.isZero()) return { v: raw, r: zeroU, exact: true, key: EMPTY };
    const absAtom = atom(`R${raw.abs().toString()}`);
    return { v: raw, r: zeroU, exact: true, key: raw.isNeg() ? keyNeg(absAtom) : absAtom };
  };

  const leaf = (re: Decimal.Value, im: Decimal.Value): Ball => {
    const a = leafComp(re);
    const b = leafComp(im);
    const ball: Ball = { re: a, im: b };
    if (isExactZero(a) && isExactZero(b)) return zeroBall(a, b);
    if (a.exact && b.exact) return { ...ball, key: atom(`L${a.v.toString()},${b.v.toString()}`) };
    return ball;
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
      if (++steps > maxNodes * 2) return { ok: false, reason: "maxNodes" };
      if ((steps & 63) === 0 && deadline && performance.now() > deadline) return { ok: false, reason: "deadline" };
      const exactFromFacts = (): Ball | null => {
        if (isUnverified(n) || isExactUnsure(n)) return null;
        const big = provenInteger(n);
        if (big !== undefined) return leaf(big.toString(), 0);
        const f = factsOf(n);
        if (f.imaginaryUnit !== undefined) return leaf(0, f.imaginaryUnit);
        if (f.angle) {
          const { n: num, d: den } = f.angle.q;
          if (num === BigInt(0)) return leaf(0, 0);
          let comp: Comp;
          const absN = num < BigInt(0) ? -num : num;
          if ((den === BigInt(1) || den === BigInt(2) || den === BigInt(4)) && absN <= BigInt(1_000_000_000_000)) {
            comp = fromQ(Number(num) / Number(den));
          } else {
            const v = pi.mul(num.toString()).div(den.toString());
            if (!v.isFinite()) return null;
            const aKey = atom(`Q${absN.toString()}/${den.toString()}`);
            comp = { v, r: up(v).mul(tenU), exact: false, key: num < BigInt(0) ? keyNeg(aKey) : aKey };
          }
          const ballKey = atom(`A${f.angle.unit}:${num.toString()}/${den.toString()}`);
          return f.angle.unit === "real" ? { re: comp, im: ZERO, key: ballKey } : { re: ZERO, im: comp, key: ballKey };
        }
        const dec = exactDecimalOf(n);
        if (dec) {
          const text = dec.s === 0 ? dec.n.toString() : `${dec.n.toString()}e-${dec.s}`;
          return leaf(text, 0);
        }
        const rat = exactRationalOf(n);
        if (rat) {
          if (rat.d === BigInt(1)) return leaf(rat.n.toString(), 0);
          const v = new B(rat.n.toString()).div(rat.d.toString());
          if (v.isFinite()) {
            const absN = rat.n < BigInt(0) ? -rat.n : rat.n;
            const rk = atom(`FQ${absN.toString()}/${rat.d.toString()}`);
            const comp: Comp = { v, r: ulp(v), exact: false, key: rat.n < BigInt(0) ? keyNeg(rk) : rk };
            return { re: comp, im: ZERO, key: atom(`BQ${rat.n.toString()}/${rat.d.toString()}`) };
          }
        }
        return null;
      };
      const factBall = n.type === "var" ? null : exactFromFacts();
      if (factBall) memo.set(n, [factBall]);
      else if (n.type === "one") memo.set(n, [leaf(1, 0)]);
      else if (n.type === "input") memo.set(n, [leaf(n.value.re, n.value.im)]);
      else if (n.type === "var") {
        const v = env[n.name];
        if (!v) return { ok: false, reason: "missingVar" };
        memo.set(n, [leaf(v.re.toString(), v.im.toString())]);
      } else if (!frame.seen) {
        stack.push({ n, seen: true });
        stack.push({ n: n.b, seen: false });
        stack.push({ n: n.a, seen: false });
      } else {
        const a = memo.get(n.a);
        const b = memo.get(n.b);
        if (!a || !b) return { ok: false, reason: "missingChild" };
        const res = gate(a, b);
        if (res.length === 1 && res[0] && res[0].key === undefined && res[0].re.v.isFinite() && res[0].im.v.isFinite()) {
          res[0] = { ...res[0], key: atom(`D${n.id}`) };
        }
        memo.set(n, res);
      }
    }
    out = memo.get(root);
  } catch (err) {
    if (err instanceof BallFail) return { ok: false, reason: err.message };
    // decimal.js refuses a trig argument past its π table, among others.
    if (err instanceof Error && /DecimalError/.test(err.message)) return { ok: false, reason: err.message };
    throw err;
  }
  if (!out || out.length === 0) return { ok: false, reason: "empty" };
  return { ok: true, balls: out };
}

export function ballConfirmsValue(
  root: Node,
  env: Record<string, BallValue>,
  value: { re: Decimal; im: Decimal },
  precision: number,
  agree: number,
  budget: { maxNodes?: number; deadline?: number } = {},
): boolean {
  const enclosed = ballEnclose(root, env, precision, budget);
  if (!enclosed.ok) return false;
  const P = Math.max(precision, 40);
  const { B, epsU } = precCtx(P);
  const ulp = (w: Decimal): Decimal => up(w).mul(epsU);
  const isExactZero = (c: BallCompOut) => c.exact && c.v.isZero();
  const tolD = new DD(10).pow(-agree);
  const confirms = (got: Decimal, c: BallCompOut): boolean => {
    if (!got.isFinite() || !c.v.isFinite()) return false;
    if (got.isZero()) return isExactZero(c);
    if (isExactZero(c)) return false;
    const g = new B(got.toString());
    const diff = g.sub(c.v);
    const errUp = up(diff).add(ulp(diff)).add(c.r);
    const limitDn = dn(g).mul(tolD);
    return errUp.lte(limitDn);
  };
  return enclosed.balls.every((ball) => confirms(value.re, ball.re) && confirms(value.im, ball.im));
}
