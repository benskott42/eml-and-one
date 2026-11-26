/// <reference lib="webworker" />

import { searchConstants, searchNearestConstant, type GolfHit, type NearestHit } from "./golf";

declare const self: DedicatedWorkerGlobalScope;

type Request = {
  type?: string;
  mode?: "constants" | "nearest";
  maxK?: number;
  request?: number;
  allowLn0?: boolean;
  targetRe?: number;
  targetIm?: number;
  limit?: number;
};

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  if (!data || data.type === "stop") return;
  const request = data.request ?? 0;
  const rawK = typeof data.maxK === "number" && Number.isFinite(data.maxK) ? data.maxK : 21;
  const maxK = Math.min(35, Math.max(1, Math.floor(rawK)));
  const started = performance.now();
  try {
    if (data.mode === "nearest") {
      const targetRe = typeof data.targetRe === "number" && Number.isFinite(data.targetRe) ? data.targetRe : 0;
      const targetIm = typeof data.targetIm === "number" && Number.isFinite(data.targetIm) ? data.targetIm : 0;
      const result = searchNearestConstant(targetRe, targetIm, maxK, {
        allowLn0: data.allowLn0 === false ? false : undefined,
        limit: data.limit ?? 5,
        onProgress: (progress) => {
          self.postMessage({ type: "progress", request, ...progress, ms: Math.round(performance.now() - started) });
        },
      });
      const nearest: NearestHit[] = result.hits;
      self.postMessage({ type: "done-nearest", request, nearest, pool: result.pool, ms: Math.round(performance.now() - started) });
      return;
    }
    const result = searchConstants(maxK, {
      allowLn0: data.allowLn0 === false ? false : undefined,
      onProgress: (progress) => {
        self.postMessage({ type: "progress", request, ...progress, ms: Math.round(performance.now() - started) });
      },
    });
    const hits: GolfHit[] = result.hits;
    self.postMessage({ type: "done", request, hits, pool: result.pool, ms: Math.round(performance.now() - started) });
  } catch (err) {
    const message = err instanceof Error ? err.message : "The search failed.";
    self.postMessage({ type: "error", request, message });
  }
};
