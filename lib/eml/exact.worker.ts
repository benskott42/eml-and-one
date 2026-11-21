/// <reference lib="webworker" />

import { EXACT_MAX_NODES } from "./exactBudget";
import { exactReport, exactToFloat, exactUnderflowsFloat, formatExact } from "./exact";
import { unpackCircuit, type Wire } from "./wire";

declare const self: DedicatedWorkerGlobalScope;

type Env = Record<string, { re: number; im: number }>;
type Request = { request: number; tokens: Wire[]; root: number; env: Env };

/**
 * v1.1 (reviewbot E6): a cooperative deadline for slow huge circuits, and a progress message
 * per exact pass (throttled) so the screen can say which precision it is on.
 */
export const EXACT_DEADLINE_MS = 150_000;
const PROGRESS_EVERY_MS = 250;

self.onmessage = (event: MessageEvent<Request>) => {
  const data = event.data;
  try {
    const node = unpackCircuit(data.tokens, data.root);
    const started = performance.now();
    let last = -Infinity;
    const onProgress = ({ digits }: { digits: number }) => {
      const now = performance.now();
      if (now - last < PROGRESS_EVERY_MS) return;
      last = now;
      self.postMessage({ type: "progress", request: data.request, digits, elapsedMs: Math.round(now - started) });
    };
    const report = exactReport(node, data.env ?? {}, { maxNodes: EXACT_MAX_NODES, deadline: started + EXACT_DEADLINE_MS, onProgress });
    const floated = exactToFloat(report.value);
    const digits = (part: { isFinite(): boolean; toFixed(places: number): string; toString(): string }) =>
      part.isFinite() ? part.toFixed(120) : part.toString();
    self.postMessage({
      type: "done",
      request: data.request,
      text: formatExact(report.value),
      re: floated.re,
      im: floated.im,
      // 120-digit decimals. The on-screen text is shorter. Old clients ignore these.
      reDigits: digits(report.value.re),
      imDigits: digits(report.value.im),
      singular: report.singular,
      touchedLn0: report.touchedLn0,
      underflowedExact: exactUnderflowsFloat(report.value),
      unverified: report.unverified === true,
      cutHits: report.cutHits,
      // v1.1: sticky "not certified" (absorbed term). Old main threads ignore the field.
      notCertified: report.notCertified ?? null,
      // v1.1 (E3): a 0 reached through a recorded cancellation.
      cancelledZero: report.cancelledZero === true,
      wire: 2,
    });
  } catch (err) {
    const message = err instanceof Error ? err.message : "Exact evaluation failed.";
    self.postMessage({ type: "error", request: data.request, message });
  }
};
