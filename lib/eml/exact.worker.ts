/// <reference lib="webworker" />

import { exactToFloat, exactUnderflowsFloat, formatExact } from "./exact";
import { reportUnpacked, WORKER_NODE_BUDGET } from "./packed-eval";
import type { Wire } from "./wire";

declare const self: DedicatedWorkerGlobalScope;

type Env = Record<string, { re: number; im: number }>;
type Request = { request: number; tokens: Wire[]; root: number; env: Env };

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  try {
    const { report } = reportUnpacked(data.tokens, data.root, WORKER_NODE_BUDGET, data.env ?? {});
    const floated = exactToFloat(report.value);
    self.postMessage({
      type: "done",
      request: data.request,
      text: formatExact(report.value),
      re: floated.re,
      im: floated.im,
      singular: report.singular,
      touchedLn0: report.touchedLn0,
      underflowedExact: exactUnderflowsFloat(report.value),
      unverified: report.unverified === true,
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Exact evaluation failed.";
    self.postMessage({ type: "error", request: data.request, message });
  }
};
