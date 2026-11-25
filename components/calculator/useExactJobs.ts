// Exact values come from exact.worker: a fill worker for the top pending row and a
// compare worker that checks float rows against the exact value. This hook owns
// both workers and their jobs, and writes finished rows back into the model.
import { useCallback, useEffect, useRef } from "react";
import { type C } from "@/lib/eml/complex";
import { beyondFloatBound } from "@/lib/eml/float-bound";
import { EmlLimitError, substitute, type Node } from "@/lib/eml/node";
import type { PackedEnvNodes } from "@/lib/eml/packed-eval";
import { packCircuit } from "@/lib/eml/wire";
import { type Entry, failure, isUnverifiedEntry } from "@/components/calculator/entry";
import { type ExactEngine, loadExactEngine, loadedExactEngine } from "@/components/calculator/exactEngine";
import type { CalcAction, CalcState } from "@/components/calculator/reducer";

type Ref<T> = { current: T };

type WorkerPayload =
  | {
      text: string;
      re: number;
      im: number;
      singular: string | null;
      touchedLn0: boolean;
      underflowedExact?: boolean;
      overflowedExact?: boolean;
      exactInfRe?: -1 | 0 | 1;
      exactInfIm?: -1 | 0 | 1;
      unverified?: boolean;
    }
  | { error: string; isLimit?: boolean };

export function useExactJobs({
  stack,
  stateRef,
  queueRef,
  dispatch,
}: {
  stack: Entry[];
  stateRef: Ref<CalcState>;
  queueRef: Ref<Array<() => void>>;
  dispatch: (action: CalcAction) => void;
}): { cancelExact: () => void } {
  const followedRef = useRef(new Set<number>());
  type JobKind = "fill" | "compare";
  const exactWorkers = useRef<Record<JobKind, Worker | null>>({ fill: null, compare: null });
  const workersBrokenRef = useRef(false);
  const inflight = useRef<Record<JobKind, Map<number, number>>>({ fill: new Map(), compare: new Map() });
  const exactJobs = useRef(new Map<number, { watch: number; kind: JobKind; floated: C }>());
  const exactSerial = useRef(0);
  const startFillWorker = useRef<(() => void) | null>(null);

  const publishWatch = useCallback(
    (token: number, next: Entry) => {
      dispatch({ type: "PUBLISH_WATCH", watch: token, next });
    },
    [dispatch],
  );

  const finishExact = useCallback(
    (request: number, payload: WorkerPayload) => {
      const job = exactJobs.current.get(request);
      exactJobs.current.delete(request);
      inflight.current.fill.delete(request);
      inflight.current.compare.delete(request);
      if (!job) return;
      const current = stateRef.current.model.stack.find((row) => row.watch === job.watch);
      if (!current || current.cancelled) return;
      if ("error" in payload) {
        if (job.kind !== "fill") {
          publishWatch(job.watch, { ...current, unverified: true });
          return;
        }
        if (payload.isLimit) {
          publishWatch(job.watch, {
            ...current,
            pendingExact: false,
            text: "—",
            value: { re: Number.NaN, im: Number.NaN },
            unverified: true,
          });
          return;
        }
        publishWatch(job.watch, {
          ...current,
          pendingExact: false,
          text: "—",
          value: { re: Number.NaN, im: Number.NaN },
          singular: payload.error,
        });
        return;
      }
      const exact = { re: payload.re, im: payload.im };
      if (job.kind === "compare") {
        if (payload.unverified) {
          publishWatch(job.watch, { ...current, unverified: true });
          return;
        }
        if (!payload.underflowedExact && !payload.overflowedExact && !beyondFloatBound(job.floated, exact)) return;
        publishWatch(job.watch, { ...current, floatDiffers: true, exactBeside: payload.text });
        return;
      }
      if (payload.unverified) {
        publishWatch(job.watch, { ...current, pendingExact: false, text: "—", value: { re: Number.NaN, im: Number.NaN }, unverified: true });
        return;
      }
      if (!current.pendingExact) return;
      publishWatch(job.watch, {
        ...current,
        pendingExact: false,
        value: exact,
        text: payload.text,
        singular: payload.singular,
        touchedLn0: payload.touchedLn0,
        exactInfRe: payload.exactInfRe,
        exactInfIm: payload.exactInfIm,
      });
    },
    [publishWatch, stateRef],
  );

  const cancelExact = useCallback(function cancel() {
    // A mode switch or undo shows "computing" before its rows exist. A cancel
    // then waits for them, or the rows it lands would start computing again.
    if (stateRef.current.busy) {
      queueRef.current.push(() => cancel());
      return;
    }
    exactJobs.current.clear();
    for (const kind of ["fill", "compare"] as const) {
      exactWorkers.current[kind]?.terminate();
      exactWorkers.current[kind] = null;
      inflight.current[kind].clear();
    }
    dispatch({ type: "CANCEL_EXACT" });
  }, [dispatch, queueRef, stateRef]);

  useEffect(() => {
    const workers = exactWorkers.current;
    const jobs = exactJobs.current;
    const active = inflight.current;
    // Without workers every exact result comes from the fallback; fetch it before the first press.
    if (typeof Worker === "undefined") void loadExactEngine().catch(() => undefined);
    return () => {
      jobs.clear();
      active.fill.clear();
      active.compare.clear();
      workers.fill?.terminate();
      workers.compare?.terminate();
      workers.fill = null;
      workers.compare = null;
    };
  }, []);

  useEffect(() => {
    const run = ({ exactOverflowsFloat, exactReport, exactToFloat, exactUnderflowsFloat, formatExact }: ExactEngine, request: number, node: Node, bound: Record<string, C>, boundNodes?: Record<string, Node>) => {
      if (!exactJobs.current.has(request)) return;
      try {
        const target = boundNodes && Object.keys(boundNodes).length > 0 ? substitute(node, boundNodes) : node;
        const report = exactReport(target, bound, { maxNodes: 80_000 });
        const exact = exactToFloat(report.value);
        const exactInfRe = !report.value.re.isFinite() && !report.value.re.isNaN() ? (report.value.re.isNeg() ? -1 : 1) : 0;
        const exactInfIm = !report.value.im.isFinite() && !report.value.im.isNaN() ? (report.value.im.isNeg() ? -1 : 1) : 0;
        finishExact(request, {
          text: formatExact(report.value),
          re: exact.re,
          im: exact.im,
          singular: report.singular,
          touchedLn0: report.touchedLn0,
          underflowedExact: exactUnderflowsFloat(report.value),
          overflowedExact: exactOverflowsFloat(report.value),
          exactInfRe,
          exactInfIm,
          unverified: report.unverified === true,
        });
      } catch (err) {
        finishExact(request, { error: failure(err), isLimit: err instanceof EmlLimitError });
      }
    };
    const deliver = (request: number, node: Node, bound: Record<string, C>, boundNodes?: Record<string, Node>) => {
      if (!exactJobs.current.has(request)) return;
      const loaded = loadedExactEngine();
      if (loaded) {
        run(loaded, request, node, bound, boundNodes);
        return;
      }
      loadExactEngine().then(
        (engine) => {
          if (!exactJobs.current.has(request)) return;
          run(engine, request, node, bound, boundNodes);
        },
        (err: unknown) => {
          if (!exactJobs.current.has(request)) return;
          finishExact(request, { error: failure(err) });
        },
      );
    };
    const accept = (data: {
      type?: string;
      request?: number;
      text?: string;
      re?: number;
      im?: number;
      singular?: string | null;
      touchedLn0?: boolean;
      underflowedExact?: boolean;
      overflowedExact?: boolean;
      exactInfRe?: -1 | 0 | 1;
      exactInfIm?: -1 | 0 | 1;
      unverified?: boolean;
      message?: string;
      isLimit?: boolean;
    }) => {
      if (data.request === undefined || !exactJobs.current.has(data.request)) return;
      inflight.current.fill.delete(data.request);
      inflight.current.compare.delete(data.request);
      if (data.type === "error") {
        finishExact(data.request, { error: data.message ?? "Exact evaluation failed.", isLimit: data.isLimit === true });
        return;
      }
      finishExact(data.request, {
        text: data.text ?? "—",
        re: data.re ?? Number.NaN,
        im: data.im ?? Number.NaN,
        singular: data.singular ?? null,
        touchedLn0: data.touchedLn0 === true,
        underflowedExact: data.underflowedExact === true,
        overflowedExact: data.overflowedExact === true,
        exactInfRe: data.exactInfRe,
        exactInfIm: data.exactInfIm,
        unverified: data.unverified === true,
      });
    };
    const onStack = (watch: number) => stack.some((item) => item.watch === watch);
    for (const watch of followedRef.current) {
      if (!onStack(watch)) followedRef.current.delete(watch);
    }
    // A cleared job must not stay queued in front of the next one. Fill and
    // compare use different workers, and a worker holding a stale job is replaced.
    // Only the top pending exact row is filled, and only the top uncompared float row is compared.
    const topFill = [...stack].reverse().find((item) => item.pendingExact === true && item.cancelled !== true)?.watch;
    const topCompare = [...stack].reverse().find((item) => item.mode === "float" && item.floatDiffers !== true && item.pendingExact !== true && !isUnverifiedEntry(item))?.watch;
    for (const kind of ["fill", "compare"] as const) {
      const pending = inflight.current[kind];
      const stale = [...pending.values()].some((watch) => !onStack(watch));
      if (!stale) continue;
      exactWorkers.current[kind]?.terminate();
      exactWorkers.current[kind] = null;
      for (const [request, watch] of pending) {
        exactJobs.current.delete(request);
        if (onStack(watch)) followedRef.current.delete(watch);
      }
      pending.clear();
    }
    const preemptWorker = (kind: JobKind, targetWatch: number | undefined) => {
      if (targetWatch === undefined) return;
      const busy = [...inflight.current[kind].values()];
      if (!busy.some((watch) => watch !== targetWatch)) return;
      exactWorkers.current[kind]?.terminate();
      exactWorkers.current[kind] = null;
      for (const [request, watch] of inflight.current[kind]) {
        exactJobs.current.delete(request);
        followedRef.current.delete(watch);
      }
      inflight.current[kind].clear();
    };
    preemptWorker("fill", topFill);
    preemptWorker("compare", topCompare);
    const ensure = (kind: JobKind): Worker | null => {
      if (workersBrokenRef.current) return null;
      const existing = exactWorkers.current[kind];
      if (existing) return existing;
      if (typeof Worker === "undefined") return null;
      try {
        const created = new Worker(new URL("../../lib/eml/exact.worker.ts", import.meta.url));
        created.onmessage = (event: MessageEvent<Parameters<typeof accept>[0]>) => accept(event.data);
        created.onerror = () => {
          created.terminate();
          // Ignore stale onerror callbacks from an already-replaced worker.
          if (exactWorkers.current[kind] !== created) return;
          exactWorkers.current[kind] = null;
          workersBrokenRef.current = true;
          // A worker that fails once (blocked script, CSP) will likely fail again: have the fallback ready.
          void loadExactEngine().catch(() => undefined);
          const pending = [...exactJobs.current.entries()].filter(([, job]) => job.kind === kind);
          for (const [request, job] of pending) {
            const row = stateRef.current.model.stack.find((item) => item.watch === job.watch);
            if (!row) {
              exactJobs.current.delete(request);
              inflight.current[kind].delete(request);
              continue;
            }
            deliver(request, row.node, row.bound ?? {}, row.boundNodes);
          }
        };
        exactWorkers.current[kind] = created;
        return created;
      } catch {
        workersBrokenRef.current = true;
        return null;
      }
    };
    for (const item of stack) {
      if (item.watch === undefined || followedRef.current.has(item.watch)) continue;
      const fill = item.pendingExact === true && item.cancelled !== true && item.watch === topFill;
      const compare = item.mode === "float" && item.floatDiffers !== true && item.pendingExact !== true && !isUnverifiedEntry(item) && item.watch === topCompare;
      if (!fill && !compare) {
        if (!(item.pendingExact === true && item.cancelled !== true)) followedRef.current.add(item.watch);
        continue;
      }
      followedRef.current.add(item.watch);
      const request = ++exactSerial.current;
      const kind: JobKind = fill ? "fill" : "compare";
      const bound = item.bound ?? {};
      const boundNodes = item.boundNodes;
      exactJobs.current.set(request, { watch: item.watch, kind, floated: item.value });
      inflight.current[kind].set(request, item.watch);
      const worker = ensure(kind);
      if (!worker) {
        const node = item.node;
        window.setTimeout(() => deliver(request, node, bound, boundNodes), 0);
        continue;
      }
      const packed = packCircuit(item.node);
      const env: Record<string, { re: number; im: number }> = {};
      for (const [name, value] of Object.entries(bound)) env[name] = { re: value.re, im: value.im };
      let envNodes: PackedEnvNodes | undefined;
      if (boundNodes && Object.keys(boundNodes).length > 0) {
        envNodes = {};
        for (const [name, varNode] of Object.entries(boundNodes)) envNodes[name] = packCircuit(varNode);
      }
      worker.postMessage({ request, tokens: packed.tokens, root: packed.root, env, envNodes });
    }
    startFillWorker.current = () => {
      if (!exactWorkers.current.fill && !workersBrokenRef.current) ensure("fill");
    };
  }, [finishExact, stack, stateRef]);

  // The fill worker starts on the first exact job. Its startup (fetching and
  // compiling decimal.js and the exact engine) was most of the wait for the first
  // result, so it is started once the page is idle instead. Jobs still create one if
  // it is missing or was replaced.
  useEffect(() => {
    if (typeof Worker === "undefined") return;
    const start = () => startFillWorker.current?.();
    if (typeof window.requestIdleCallback === "function") {
      const handle = window.requestIdleCallback(start, { timeout: 3000 });
      return () => window.cancelIdleCallback(handle);
    }
    const handle = window.setTimeout(start, 500);
    return () => window.clearTimeout(handle);
  }, []);

  return { cancelExact };
}
