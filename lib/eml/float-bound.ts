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
    return Math.abs(left - right) > 5e-12 * mag;
  };
  return part(got.re, exact.re) || part(got.im, exact.im);
}
