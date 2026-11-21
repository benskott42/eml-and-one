import { exactParts, formatExact } from "./exact";

export type ExactMsg = {
  text: string;
  re: number;
  im: number;
  singular: string | null;
  touchedLn0: boolean;
  underflowedExact: boolean;
  unverified: boolean;
  cutHits?: number;
};

export type FloatInfo = {
  text: string;
  re: number;
  im: number;
  underflowed: boolean;
  overflowed: boolean;
  singular: string | null;
  touchedLn0: boolean;
};

export const targetText = (n: number) => formatExact(exactParts(n));

export function exactStatus(message: ExactMsg, n: number): "exact" | "unverified" | "not-certified" {
  if (message.unverified) return "unverified";
  if (message.singular || message.underflowedExact || message.text !== targetText(n)) return "not-certified";
  return "exact";
}

/** Float is certified when it is finite and within 1e−9 of the exact value. */
export function floatCertified(floated: FloatInfo, exact: ExactMsg | null): boolean {
  if (floated.underflowed || floated.overflowed || floated.singular || !Number.isFinite(floated.re) || !Number.isFinite(floated.im)) return false;
  if (!exact) return true;
  const tol = 1e-9 * Math.max(1, Math.abs(exact.re));
  return Math.abs(floated.re - exact.re) <= tol && Math.abs(floated.im - exact.im) <= tol;
}
