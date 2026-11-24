// The exact engine (decimal.js) runs in exact.worker. The screen loads it only
// for the fallback: no Worker, or a worker that failed. Once loaded it is kept,
// and a delivery runs synchronously as before.
export type ExactEngine = typeof import("@/lib/eml/exact");
let exactEngine: ExactEngine | null = null;
let exactEngineLoad: Promise<ExactEngine> | null = null;

export function loadExactEngine(): Promise<ExactEngine> {
  exactEngineLoad ??= import("@/lib/eml/exact").then(
    (engine) => {
      exactEngine = engine;
      return engine;
    },
    (err: unknown) => {
      // A failed chunk fetch is retried on the next delivery.
      exactEngineLoad = null;
      throw err;
    },
  );
  return exactEngineLoad;
}

/** The engine once loadExactEngine has resolved, else null. */
export function loadedExactEngine(): ExactEngine | null {
  return exactEngine;
}
