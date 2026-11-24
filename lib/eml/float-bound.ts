import type { C } from "./complex";

/**
 * True when the float evaluation and the exact evaluation of the same circuit
 * disagree by more than the screen can hide. Twelve digits are shown, so a
 * relative error of 10^(−11) on either component is flagged, and 10^(−12) is not.
 * The components are compared separately: exp(10^(−9)i) − 1 and 10^300 + i drop
 * one component, and that drop is a disagreement even when the other component
 * is huge. A few ulps of a moderate result still agree. Signed zeros agree.
 */
export function beyondFloatBound(got: C, exact: C): boolean {
  const scale = Math.max(Math.abs(got.re), Math.abs(got.im), Math.abs(exact.re), Math.abs(exact.im));
  const part = (left: number, right: number): boolean => {
    if (!Number.isFinite(left) || !Number.isFinite(right)) return !Object.is(left, right);
    if (Object.is(left, right)) return false;
    // −0 and 0 are the same component. A float 0 against a nonzero exact
    // component is a drop (exp(10^(−9)i) − 1, 10^300 + i). A float-only
    // component is dust when it sits below the digits on screen.
    if (left === 0 && right === 0) return false;
    if (left === 0) return true;
    if (right === 0) return Math.abs(left) > 5e-12 * Math.max(scale, Math.abs(left));
    const mag = Math.max(Math.abs(left), Math.abs(right));
    if (Math.abs(left - right) > 5e-12 * mag) return true;
    // The screen prints a float within half a twelfth digit of an integer below
    // 10^15 as that integer, every digit of it (formatReal in format.ts). From
    // 10^12 that is more than twelve digits, and the last ones can be wrong
    // inside the relative bound: 10^30/10^15 printed 999999999999985 with no
    // flag. Such a component is flagged when a printed digit is wrong.
    return printedAsLongInteger(left) && Math.abs(left - right) >= 0.5;
  };
  return part(got.re, exact.re) || part(got.im, exact.im);
}

/** True when formatReal prints |x| as an integer of 13 to 15 digits. */
function printedAsLongInteger(x: number): boolean {
  const abs = Math.abs(x);
  if (!(abs >= 1e12) || !(abs < 1e15)) return false;
  const nearest = Math.round(abs);
  const twelfth = 10 ** (Math.floor(Math.log10(abs)) - 11);
  return nearest < 1e15 && Math.abs(abs - nearest) < twelfth / 2;
}
