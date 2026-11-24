import type { GolfHit } from "./golf";

/** The with-infinity search keeps these and says so. The finite search rejects them. */
export function ln0Dependence(hit: GolfHit): string | null {
  return hit.usesLn0 ? "depends on ln 0 = −∞" : null;
}
