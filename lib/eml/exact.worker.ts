/// <reference lib="webworker" />

import { exactReport, exactToFloat, exactUnderflowsFloat, formatExact } from "./exact";
import { unpackCircuit, type Wire } from "./wire";

declare const self: DedicatedWorkerGlobalScope;

type Env = Record<string, { re: number; im: number }>;
type Request = { request: number; tokens: Wire[]; root: number; env: Env };

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  try {
    const node = unpackCircuit(data.tokens, data.root);
    const report = exactReport(node, data.env ?? {}, { maxNodes: 80_000 });
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
      cutHits: report.cutHits,
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Exact evaluation failed.";
    self.postMessage({ type: "error", request: data.request, message });
  }
};
