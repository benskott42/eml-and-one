/**
 * Complex arithmetic for the EML operator.
 *
 * eml(x, y) = exp(x) − ln(y). There is no magnitude clamp on exp:
 * a finite input uses the real exponential, exp(−∞) is 0, and exp(+∞) is +∞.
 *
 * Two logs, on purpose:
 * - Principal Log has Arg ∈ (−π, π]. The negative-real axis takes the upper
 *   edge, Arg = +π. That is the usual mathematical logarithm.
 * - The log inside eml is the paper's other choice (§4.1): on a negative
 *   real, Arg = −π. The composed circuit
 *   ln z = eml(1, eml(eml(1, z), 1)) then matches principal Log, and i is +i.
 *   A point is on the cut only when its imaginary part is exact 0 or −0.
 *   −2 ± 10^(−300)i stay off the axis. exp(iπ) is −1 only because π is an
 *   exact quarter turn; a 10^(−15) step off the axis is not moved. A
 *   subtraction is cleared only when it cancelled to a couple of ulps.
 *
 * IEEE extended values, shared by float64 and exact mode:
 * - ln(0) = −∞, and exp(−∞) = 0.
 * - ∞ − ∞ and 0 · ∞ are indeterminate. They are NaN, not a number.
 * - ln(+∞) = +∞. exp(+∞ + iθ) is infinity in the direction of θ.
 *
 * Subtraction. eml(ln a, exp b) equals a − b only for Im(b) ∈ (−π, π)
 * and a moderate real part. The library chooses the circuit from a
 * structural range, not from a second evaluation of the node.
 */

export type C = { re: number; im: number };

export const C1: C = { re: 1, im: 0 };

export function c(re: number, im = 0): C {
  return { re, im };
}

function copysign(magnitude: number, sign: number): number {
  const mag = Math.abs(magnitude);
  return sign < 0 || Object.is(sign, -0) ? -mag : mag;
}

/** A few ulps of `scale`. Subnormals and non-finites contribute nothing. */
function unitUlp(scale: number): number {
  const ax = Math.abs(scale);
  if (!(ax > 0) || !Number.isFinite(ax)) return 0;
  return 2 ** (Math.floor(Math.log2(ax)) - 52);
}

/**
 * cos(θ) + i sin(θ), reduced to the nearest quarter turn first.
 * Math.sin and Math.cos of a large or near-axis angle differ between
 * engines and lose the component that sits on the other axis. The
 * reduction uses only the distance to that quarter turn, which is what
 * makes exp(iπ) exactly −1 and still leaves a 10^(−15) step off the axis
 * where it is. A pure axis (delta 0) is that axis; anything else is not moved.
 */
function reducedTrig(im: number): { re: number; im: number } {
  if (!Number.isFinite(im)) return { re: NaN, im: NaN };
  const quarter = Math.PI / 2;
  const steps = Math.round(im / quarter);
  const delta = im - steps * quarter;
  const sine = delta === 0 ? 0 : Math.sin(delta);
  const cosine = delta === 0 ? 1 : Math.cos(delta);
  const axis = ((steps % 4) + 4) % 4;
  if (axis === 0) return { re: cosine, im: sine };
  if (axis === 1) return { re: -sine, im: cosine };
  if (axis === 2) return { re: -cosine, im: -sine };
  return { re: sine, im: -cosine };
}

function cis(im: number, mag: number): C {
  const trig = reducedTrig(im);
  if (mag === Infinity) {
    return {
      re: trig.re === 0 ? 0 : trig.re > 0 ? Infinity : -Infinity,
      im: trig.im === 0 ? 0 : trig.im > 0 ? Infinity : -Infinity,
    };
  }
  return { re: mag * trig.re, im: mag * trig.im };
}

function signedZero(part: number): number {
  return part < 0 || Object.is(part, -0) ? -0 : 0;
}

/** exp(−∞ + iθ) is a signed zero in the direction of θ, not a bare +0. */
function underflowCis(im: number): C {
  const trig = reducedTrig(im);
  return { re: signedZero(trig.re), im: signedZero(trig.im) };
}

export function cexp(z: C): C {
  if (z.re === -Infinity && Number.isFinite(z.im)) return underflowCis(z.im);
  if (z.re === Infinity && Number.isFinite(z.im)) return cis(z.im, Infinity);
  if (!Number.isFinite(z.re) || !Number.isFinite(z.im)) return { re: NaN, im: NaN };
  const m = Math.exp(z.re);
  if (m === 0) return underflowCis(z.im);
  if (m === Infinity) return cis(z.im, Infinity);
  return cis(z.im, m);
}

/**
 * True on the negative-real axis, including −∞.
 * −∞ is a negative real, so the lower bank gives it argument −π.
 * atan2(0, −∞) is +π, which would put the composed ln(−0) on the other bank.
 */
function onNegativeCut(re: number, im: number): boolean {
  if (!(re < 0)) return false;
  return im === 0 || Object.is(im, -0);
}

/** log|z| without overflowing hypot when both components are huge and finite. */
function logMagnitude(re: number, im: number): number {
  const ax = Math.abs(re);
  const ay = Math.abs(im);
  const large = Number.MAX_VALUE / 4;
  if (ax > large || ay > large) {
    return Math.log(Math.hypot(ax / 2, ay / 2)) + Math.LN2;
  }
  return Math.log(Math.hypot(ax, ay));
}

function logArg(z: C, negativeAxis: number): C {
  if (z.re === 0 && (z.im === 0 || Object.is(z.im, -0))) {
    // +0 is −∞ on the positive axis. −0 is the origin approached from the
    // negative side, so it takes that evaluator's bank (eml: −π, principal: +π).
    if (Object.is(z.re, -0)) return { re: -Infinity, im: negativeAxis };
    return { re: -Infinity, im: Object.is(z.im, -0) ? -0 : 0 };
  }
  const arg = onNegativeCut(z.re, z.im) ? negativeAxis : Math.atan2(z.im, z.re);
  const re = logMagnitude(z.re, z.im);
  if (Number.isNaN(re) || Number.isNaN(arg)) return { re: NaN, im: NaN };
  return { re, im: arg };
}

/** Logarithm used inside eml. Negative reals sit on the lower bank of the cut. */
export function clog(z: C): C {
  return logArg(z, -Math.PI);
}

/** Principal logarithm. Negative reals sit on the upper bank, arg = +π. */
export function clogPrincipal(z: C): C {
  return logArg(z, Math.PI);
}

/**
 * Drop a component only when it cancelled to a few ulps of the terms that
 * produced it. A genuine 10^(−15) difference is kept. This is what lets the
 * composed logarithm land on the negative axis and take the upper bank.
 */
function cancelled(diff: number, left: number, right: number): number {
  if (diff === 0 || !Number.isFinite(diff)) return diff;
  const scale = Math.max(Math.abs(left), Math.abs(right));
  if (scale > 0 && Math.abs(diff) <= 2 * unitUlp(scale)) return 0;
  return diff;
}

export function eml(x: C, y: C): C {
  const a = cexp(x);
  const b = clog(y);
  const re = cancelled(a.re - b.re, a.re, b.re);
  const im = cancelled(a.im - b.im, a.im, b.im);
  if (Number.isNaN(re) || Number.isNaN(im)) return { re: NaN, im: NaN };
  return { re, im };
}

export function hypotC(z: C): number {
  return Math.hypot(z.re, z.im);
}

/**
 * Relative error. A residue smaller than a few ulps of 1 is cancellation dust
 * and matches zero. Anything larger is compared with the values themselves,
 * so a large relative error near 10^(−12) does not pass.
 */
export function close(z: C, target: C, tol = 1e-8): boolean {
  if (z.re === target.re && z.im === target.im) return true;
  if (!Number.isFinite(z.re) || !Number.isFinite(z.im) || !Number.isFinite(target.re) || !Number.isFinite(target.im)) {
    return false;
  }
  const mag = Math.max(hypotC(z), hypotC(target));
  const err = Math.hypot(z.re - target.re, z.im - target.im);
  const dust = 32 * unitUlp(1);
  if (mag <= dust) return err <= dust;
  return err <= Math.max(tol * mag, 32 * unitUlp(mag));
}

export function isZero(z: C): boolean {
  return z.re === 0 && (z.im === 0 || Object.is(z.im, -0));
}

function nearlyReal(z: C): boolean {
  return Number.isFinite(z.re) && (z.im === 0 || Object.is(z.im, -0));
}

function imagIsZero(z: C): boolean {
  return z.im === 0 || Object.is(z.im, -0);
}

function finitePart(n: number): boolean {
  return Number.isFinite(n);
}

export function cadd(a: C, b: C): C {
  return { re: a.re + b.re, im: a.im + b.im };
}

export function csub(a: C, b: C): C {
  return { re: a.re - b.re, im: a.im - b.im };
}

/** 0 · ∞ and 0 · NaN are indeterminate. A finite product is the usual one. */
export function cmul(a: C, b: C): C {
  const aFinite = finitePart(a.re) && finitePart(a.im);
  const bFinite = finitePart(b.re) && finitePart(b.im);
  if ((isZero(a) && !bFinite) || (isZero(b) && !aFinite)) return { re: NaN, im: NaN };
  if (imagIsZero(a) && imagIsZero(b)) return { re: a.re * b.re, im: 0 };
  return { re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re };
}

export function cneg(a: C): C {
  // Unary minus keeps the sign of zero: −(+0) is −0, and −(−0) is +0.
  return { re: -a.re, im: -a.im };
}

export function cdiv(a: C, b: C): C {
  if (!finitePart(a.re) && !finitePart(a.im) && isZero(b)) return { re: NaN, im: NaN };
  if (Number.isNaN(a.re) || Number.isNaN(a.im) || Number.isNaN(b.re) || Number.isNaN(b.im)) {
    return { re: NaN, im: NaN };
  }
  if (a.im === 0 && b.im === 0) {
    if (b.re === 0) {
      if (a.re === 0 || !finitePart(a.re)) return { re: NaN, im: NaN };
      const sign = (a.re < 0 ? -1 : 1) * (Object.is(b.re, -0) ? -1 : 1);
      return { re: sign > 0 ? Infinity : -Infinity, im: 0 };
    }
    return { re: a.re / b.re, im: 0 };
  }
  if (isZero(b)) {
    if (isZero(a)) return { re: NaN, im: NaN };
    if (a.re === 0 && finitePart(a.im) && a.im !== 0) {
      const sign = (a.im < 0 ? -1 : 1) * (Object.is(b.re, -0) ? -1 : 1);
      return { re: 0, im: sign > 0 ? Infinity : -Infinity };
    }
    return { re: NaN, im: NaN };
  }
  if (!finitePart(b.re) || !finitePart(b.im)) {
    if (finitePart(a.re) && finitePart(a.im)) return { re: 0, im: 0 };
    return { re: NaN, im: NaN };
  }
  // Scale by the larger part so b.re² + b.im² does not overflow.
  // A zero times an infinite numerator is 0 here: this is division, not 0·∞.
  const mul = (x: number, y: number) => ((x === 0 || y === 0) && (!finitePart(x) || !finitePart(y)) ? 0 : x * y);
  const ar = Math.abs(b.re);
  const ai = Math.abs(b.im);
  if (ar >= ai) {
    const t = b.im / b.re;
    const den = b.re + b.im * t;
    if (!(den !== 0) || !finitePart(den)) return { re: NaN, im: NaN };
    return { re: (mul(a.re, 1) + mul(a.im, t)) / den, im: (mul(a.im, 1) - mul(a.re, t)) / den };
  }
  const t = b.re / b.im;
  const den = b.im + b.re * t;
  if (!(den !== 0) || !finitePart(den)) return { re: NaN, im: NaN };
  return { re: (mul(a.re, t) + mul(a.im, 1)) / den, im: (mul(a.im, t) - mul(a.re, 1)) / den };
}

/** Principal power. 0 raised to a positive real power is 0, and finite z^0 is 1. */
export function cpow(a: C, b: C): C {
  if (isZero(b)) {
    return Number.isFinite(a.re) && Number.isFinite(a.im) ? { re: 1, im: 0 } : { re: NaN, im: NaN };
  }
  if (imagIsZero(a) && imagIsZero(b) && !Number.isNaN(a.re) && !Number.isNaN(b.re)) {
    if ((a.re === 1 || a.re === -1) && !Number.isFinite(b.re)) return { re: 1, im: 0 };
    if (a.re === 0 || Object.is(a.re, -0)) {
      if (b.re > 0) return { re: 0, im: 0 };
      if (b.re < 0) return { re: Infinity, im: 0 };
    } else if (a.re < 0 && Number.isInteger(b.re)) {
      return { re: a.re ** b.re, im: 0 };
    }
  }
  if (isZero(a)) {
    if (nearlyReal(b) && b.re > 0) return { re: 0, im: 0 };
    if (nearlyReal(b) && b.re < 0) return { re: Infinity, im: 0 };
    return { re: NaN, im: NaN };
  }
  if (nearlyReal(a) && nearlyReal(b) && a.re < 0 && Number.isInteger(b.re)) {
    return { re: a.re ** b.re, im: 0 };
  }
  return cexp(cmul(b, clogPrincipal(a)));
}

function pureImag(z: C): boolean {
  return (z.re === 0 || Object.is(z.re, -0)) && Number.isFinite(z.im);
}

export function csinh(z: C): C {
  if (z.im === 0 && !Number.isNaN(z.re)) return { re: Math.sinh(z.re), im: 0 };
  if (pureImag(z)) return { re: 0, im: Math.sin(z.im) };
  return cdiv(csub(cexp(z), cexp(cneg(z))), c(2));
}

export function ccosh(z: C): C {
  if (z.im === 0 && !Number.isNaN(z.re)) return { re: Math.cosh(z.re), im: 0 };
  if (pureImag(z)) return { re: Math.cos(z.im), im: 0 };
  return cdiv(cadd(cexp(z), cexp(cneg(z))), c(2));
}

/** Principal square root, matching cmath: non-negative real part. */
function csqrt(z: C): C {
  if ((z.re === 0 || Object.is(z.re, -0)) && (z.im === 0 || Object.is(z.im, -0))) {
    return { re: 0, im: z.im };
  }
  const ax = Math.abs(z.re);
  const ay = Math.abs(z.im);
  const ax8 = ax / 8;
  const s = 2 * Math.sqrt(ax8 + Math.hypot(ax8, ay / 8));
  const d = s === 0 ? 0 : ay / (2 * s);
  if (z.re >= 0) return { re: s, im: copysign(d, z.im) };
  return { re: d, im: copysign(s, z.im) };
}

const LARGE = Number.MAX_VALUE / 4;

/** Principal arcsinh. asinh is odd, and the real line uses Math.asinh. */
export function casinh(z: C): C {
  if (z.im === 0 && !Number.isNaN(z.re)) return { re: Math.asinh(z.re), im: 0 };
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  // Oddness covers the negative real half and the negative imaginary axis.
  // Leaving Im < −1 on the formula below flips the real sign.
  if (z.re < 0 || (z.re === 0 && z.im < 0)) {
    const w = casinh({ re: z.re === 0 ? 0 : -z.re, im: z.im === 0 ? 0 : -z.im });
    return { re: -w.re, im: -w.im };
  }
  const ax = Math.abs(z.re);
  const ay = Math.abs(z.im);
  if (ax > LARGE || ay > LARGE) {
    const mag = Math.log(Math.hypot(z.re / 2, z.im / 2)) + Math.LN2 * 2;
    return { re: copysign(mag, z.re), im: Math.atan2(z.im, ax) };
  }
  const s1 = csqrt({ re: 1 + z.im, im: -z.re });
  const s2 = csqrt({ re: 1 - z.im, im: z.re });
  return {
    re: Math.asinh(s1.re * s2.im - s2.re * s1.im),
    im: Math.atan2(z.im, s1.re * s2.re - s1.im * s2.im),
  };
}

/**
 * Principal arccosh. Real x < −1 keeps a positive real part and imag +π.
 */
export function cacosh(z: C): C {
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  const ax = Math.abs(z.re);
  const ay = Math.abs(z.im);
  if (ax > LARGE || ay > LARGE) {
    return {
      re: Math.log(Math.hypot(z.re / 2, z.im / 2)) + Math.LN2 * 2,
      im: Math.atan2(z.im, z.re),
    };
  }
  const s1 = csqrt({ re: z.re - 1, im: z.im });
  const s2 = csqrt({ re: z.re + 1, im: z.im });
  return {
    re: Math.asinh(s1.re * s2.re + s1.im * s2.im),
    im: 2 * Math.atan2(s1.im, s2.re),
  };
}

/** Principal arcsin. Real values outside [−1, 1] have a negative imag for x > 1. */
export function casin(z: C): C {
  if (z.im === 0 && Number.isFinite(z.re) && Math.abs(z.re) <= 1) {
    return { re: Math.asin(z.re), im: 0 };
  }
  // The lower cut: arcsin(x > 1) = π/2 − i·arcosh(x). arccos(2) is then +i·arcosh(2).
  if (z.im === 0 && Number.isFinite(z.re) && z.re > 1) return { re: Math.PI / 2, im: -Math.acosh(z.re) };
  if (z.im === 0 && Number.isFinite(z.re) && z.re < -1) return { re: -Math.PI / 2, im: Math.acosh(-z.re) };
  const s = casinh({ re: -z.im, im: z.re });
  return { re: s.im, im: -s.re };
}

/** Principal arccos, π/2 − arcsin. */
export function cacos(z: C): C {
  const a = casin(z);
  return { re: Math.PI / 2 - a.re, im: -a.im };
}

export function csin(z: C): C {
  if (nearlyReal(z)) return { re: Math.sin(z.re), im: 0 };
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  return {
    re: Math.sin(z.re) * Math.cosh(z.im),
    im: Math.cos(z.re) * Math.sinh(z.im),
  };
}

export function ccos(z: C): C {
  if (nearlyReal(z)) return { re: Math.cos(z.re), im: 0 };
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  return {
    re: Math.cos(z.re) * Math.cosh(z.im),
    im: -Math.sin(z.re) * Math.sinh(z.im),
  };
}

export function ctanh(z: C): C {
  if (z.im === 0 && !Number.isNaN(z.re)) return { re: Math.tanh(z.re), im: 0 };
  if (pureImag(z)) return { re: 0, im: Math.tan(z.im) };
  return cdiv(csub(cexp(z), cexp(cneg(z))), cadd(cexp(z), cexp(cneg(z))));
}

const SQRT_LARGE = Math.sqrt(LARGE);
const SQRT_MIN_NORMAL = Math.sqrt(Number.MIN_VALUE * 2 ** 52);

/**
 * artanh. atanh(1) is +∞.
 * A real x > 1 uses this project's lower cut: ½ ln|(1+x)/(1−x)| − iπ/2.
 * This matches mpmath's atanh. C99 catanh of a real above 1, with a +0
 * imaginary part, returns the opposite sign.
 */
export function catanh(z: C): C {
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  if (z.im === 0 && Math.abs(z.re) > 1) {
    const mag = Math.abs(z.re);
    const half = Math.log((mag + 1) / (mag - 1)) / 2;
    return { re: z.re > 0 ? half : -half, im: z.re > 0 ? -Math.PI / 2 : Math.PI / 2 };
  }
  if (z.re < 0) {
    const w = catanh({ re: -z.re, im: -z.im });
    return { re: -w.re, im: -w.im };
  }
  const ay = Math.abs(z.im);
  if (z.re > SQRT_LARGE || ay > SQRT_LARGE) {
    const h = Math.hypot(z.re / 2, z.im / 2);
    return { re: z.re / 4 / h / h, im: -copysign(Math.PI / 2, -z.im) };
  }
  if (z.re === 1 && ay < SQRT_MIN_NORMAL) {
    if (ay === 0) return { re: Infinity, im: z.im };
    return {
      re: -Math.log(Math.sqrt(ay) / Math.sqrt(Math.hypot(ay, 2))),
      im: copysign(Math.atan2(2, -ay) / 2, z.im),
    };
  }
  const denom = (1 - z.re) * (1 - z.re) + ay * ay;
  return {
    re: Math.log1p((4 * z.re) / denom) / 4,
    im: -Math.atan2(-2 * z.im, (1 - z.re) * (1 + z.re) - ay * ay) / 2,
  };
}

export function catan(z: C): C {
  if (z.im === 0 && !Number.isNaN(z.re)) return { re: Math.atan(z.re), im: 0 };
  // iy with |y| > 1 is i·artanh(y) on this cut. arctan(−2i) is −π/2 − (artanh 2)i,
  // the value both engines and mpmath give. The principal log would flip the real part.
  if ((z.re === 0 || Object.is(z.re, -0)) && Math.abs(z.im) > 1) return cmul(c(0, 1), catanh(c(z.im)));
  const it = cmul(c(0, 1), z);
  return cdiv(clogPrincipal(cdiv(cadd(c(1), it), csub(c(1), it))), c(0, 2));
}

export function chypot(a: C, b: C): C {
  if (a.im === 0 && b.im === 0 && !Number.isNaN(a.re) && !Number.isNaN(b.re)) {
    return { re: Math.hypot(a.re, b.re), im: 0 };
  }
  return cpow(cadd(cmul(a, a), cmul(b, b)), c(0.5));
}

/** Average that does not overflow when the two values are large and equal. */
export function cavg(a: C, b: C): C {
  return { re: a.re / 2 + b.re / 2, im: a.im / 2 + b.im / 2 };
}

/**
 * tan(z) = −i (e^{2iz} − 1) / (e^{2iz} + 1), from the side that underflows.
 * sin/cos overflows for an imaginary part of a few hundred.
 */
export function ctan(z: C): C {
  if (Number.isNaN(z.re) || Number.isNaN(z.im)) return { re: NaN, im: NaN };
  if (z.im === 0 && Number.isFinite(z.re)) return { re: Math.tan(z.re), im: 0 };
  if (z.re === 0 && Number.isFinite(z.im)) return { re: 0, im: Math.tanh(z.im) };
  if (z.im >= 0) {
    const w = cexp({ re: -2 * z.im, im: 2 * z.re });
    return cmul({ re: 0, im: -1 }, cdiv(csub(w, C1), cadd(w, C1)));
  }
  const w = cexp({ re: 2 * z.im, im: -2 * z.re });
  return cmul({ re: 0, im: -1 }, cdiv(csub(C1, w), cadd(C1, w)));
}
