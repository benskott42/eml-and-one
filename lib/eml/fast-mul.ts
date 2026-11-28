import Decimal from "decimal.js";

/**
 * decimal.js multiplies base-1e7 limbs with a schoolbook loop. At a few hundred
 * digits that loop is most of exp, ln, cos and sin. This is the same integer
 * product: the significands are multiplied and written back in the same base, so
 * every digit matches. An internal series keeps the full product, and a normal
 * call rounds to the working precision. decimal.js keeps that choice in a closed
 * flag; a value past minE is preserved only while the flag says not to round.
 */
const BASE = 10_000_000;
const LOG = 7;
const MIN_LIMBS = 12;
const TAG = "[object Decimal]";
// minE cannot be below -9e15, so this exponent underflows exactly when rounding is on.
const PROBE_E = -9e15 - 1;
const probe = { toStringTag: TAG, s: 1, e: PROBE_E, d: [1] };

function roundingOff(Ctor: Decimal.Constructor): boolean {
  const copied = new Ctor(probe as unknown as Decimal);
  return copied.d![0] !== 0;
}

function digitsToBig(d: number[]): bigint {
  if (d.length === 1) return BigInt(d[0]!);
  const parts = new Array<string>(d.length);
  parts[0] = String(d[0]);
  for (let i = 1; i < d.length; i++) parts[i] = String(BASE + d[i]!).slice(1);
  return BigInt(parts.join(""));
}

function limbsFromProduct(prod: bigint, xdL: number, ydL: number): { digits: number[]; carry: boolean } {
  const s = prod.toString();
  const carry = Math.ceil(s.length / LOG) === xdL + ydL;
  const digits: number[] = [];
  const rem = s.length % LOG;
  let i = 0;
  if (rem !== 0) {
    digits.push(Number(s.slice(0, rem)));
    i = rem;
  }
  for (; i < s.length; i += LOG) digits.push(Number(s.slice(i, i + LOG)));
  let end = digits.length;
  while (end > 1 && digits[end - 1] === 0) end -= 1;
  if (end !== digits.length) digits.length = end;
  return { digits, carry };
}

function limbExpToE(digits: number[], limbE: number): number {
  let e = limbE * LOG;
  let w = digits[0]!;
  for (; w >= 10; w /= 10) e += 1;
  return e;
}

let installed = false;

export function installFastMul(): void {
  if (installed) return;
  installed = true;
  const orig = Decimal.prototype.mul;
  const fastMul = function (this: Decimal, y: Decimal.Value): Decimal {
    const Ctor = this.constructor as Decimal.Constructor;
    const xd = this.d;
    if (!(y instanceof Ctor) || !xd || !y.d || !xd[0] || !y.d[0] || xd.length < MIN_LIMBS || y.d.length < MIN_LIMBS) {
      return orig.call(this, y);
    }
    const round = !roundingOff(Ctor);
    const { digits, carry } = limbsFromProduct(digitsToBig(xd) * digitsToBig(y.d), xd.length, y.d.length);
    let limbE = Math.floor(this.e / LOG) + Math.floor(y.e / LOG);
    if (carry) limbE += 1;
    const out = new Ctor(0);
    // decimal.js types mark the coefficient read-only; the constructor is the only other writer.
    const coeff = out as unknown as { s: number; d: number[]; e: number };
    coeff.s = this.s * y.s;
    coeff.d = digits;
    coeff.e = limbExpToE(digits, limbE);
    return round ? out.toSD(Ctor.precision, Ctor.rounding) : out;
  };
  Decimal.prototype.mul = fastMul;
  Decimal.prototype.times = fastMul;
}
