/// <reference lib="webworker" />

import { exactOverflowsFloat, exactToFloat, exactUnderflowsFloat, formatExact } from "./exact";
import { EmlLimitError } from "./node";
import { reportUnpacked, WORKER_NODE_BUDGET, type PackedEnvNodes } from "./packed-eval";
import type { Wire } from "./wire";

declare const self: DedicatedWorkerGlobalScope;

type Env = Record<string, { re: number; im: number }>;
type Request = { request: number; tokens: Wire[]; root: number; env: Env; envNodes?: PackedEnvNodes };

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  try {
    const { report } = reportUnpacked(data.tokens, data.root, WORKER_NODE_BUDGET, data.env ?? {}, data.envNodes);
    const floated = exactToFloat(report.value);
    const exactInfRe = !report.value.re.isFinite() && !report.value.re.isNaN() ? (report.value.re.isNeg() ? -1 : 1) : 0;
    const exactInfIm = !report.value.im.isFinite() && !report.value.im.isNaN() ? (report.value.im.isNeg() ? -1 : 1) : 0;
    self.postMessage({
      type: "done",
      request: data.request,
      text: formatExact(report.value),
      re: floated.re,
      im: floated.im,
      singular: report.singular,
      touchedLn0: report.touchedLn0,
      underflowedExact: exactUnderflowsFloat(report.value),
      overflowedExact: exactOverflowsFloat(report.value),
      exactInfRe,
      exactInfIm,
      unverified: report.unverified === true,
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Exact evaluation failed.";
    self.postMessage({ type: "error", request: data.request, message, isLimit: err instanceof EmlLimitError });
  }
};
