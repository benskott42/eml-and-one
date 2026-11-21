/// <reference lib="webworker" />

import { searchConstants, type GolfHit } from "./golf";

declare const self: DedicatedWorkerGlobalScope;

type Request = { type?: string; maxK?: number; request?: number; allowLn0?: boolean; sound?: boolean };

let active = 0;

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  // Cancel is worker.terminate(). This loop does not yield, so a stop message would wait until the search returned.
  if (data.type === "stop") {
    active += 1;
    return;
  }
  const request = data.request ?? 0;
  active += 1;
  const token = active;
  const maxK = Math.min(35, Math.max(1, Math.floor(data.maxK ?? 21)));
  const started = Date.now();
  try {
    const result = searchConstants(maxK, {
      allowLn0: data.allowLn0 === false ? false : undefined,
      ...(data.sound === true ? { sound: true } : {}),
      shouldStop: () => token !== active,
      onProgress: (progress) => {
        if (token !== active) return;
        self.postMessage({ type: "progress", request, ...progress, ms: Date.now() - started });
      },
    });
    if (token !== active) return;
    const hits: GolfHit[] = result.hits;
    self.postMessage({ type: "done", request, hits, pool: result.pool, ms: Date.now() - started });
  } catch (err) {
    if (token !== active) return;
    const message = err instanceof Error ? err.message : "The search failed.";
    self.postMessage({ type: "error", request, message });
  }
};
