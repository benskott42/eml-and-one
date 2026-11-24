// Exact values come from exact.worker: a fill worker for the top pending row and a
// compare worker that checks float rows against the exact value. This hook owns
// both workers and their jobs, and writes finished rows back into the model.
import { useCallback, useEffect, useRef } from "react";
import { type C } from "@/lib/eml/complex";
import { beyondFloatBound } from "@/lib/eml/float-bound";
import { exactScreen, type History } from "@/lib/eml/history";
import { type Node } from "@/lib/eml/node";
import { packCircuit } from "@/lib/eml/wire";
import { type Entry, type Model, failure, noteFor, resultError } from "@/components/calculator/entry";
import { type ExactEngine, loadExactEngine, loadedExactEngine } from "@/components/calculator/exactEngine";

type Ref<T> = { current: T };

export function useExactJobs({
  stack,
  modelRef,
  historyRef,
  recomputeRef,
  queueRef,
  setModel,
}: {
  stack: Entry[];
  modelRef: Ref<Model>;
  historyRef: Ref<History<Model>>;
  recomputeRef: Ref<boolean>;
  queueRef: Ref<Array<() => void>>;
  setModel: (next: Model) => void;
}): { cancelExact: () => void } {
  const followedRef = useRef(new Set<number>());
  type JobKind = "fill" | "compare";
  const exactWorkers = useRef<Record<JobKind, Worker | null>>({ fill: null, compare: null });
  const inflight = useRef<Record<JobKind, Map<number, number>>>({ fill: new Map(), compare: new Map() });
  const exactJobs = useRef(new Map<number, { watch: number; kind: JobKind; floated: C }>());
  const exactSerial = useRef(0);
  const startFillWorker = useRef<(() => void) | null>(null);

  const publishWatch = useCallback((token: number, next: Entry) => {
    const current = modelRef.current;
    if (!current.stack.some((row) => row.watch === token)) return;
    const stack = current.stack.map((row) => (row.watch === token ? next : row));
    const top = stack[stack.length - 1];
    const updated: Model = {
      ...current,
      stack,
      note: top?.watch === token ? noteFor(next) : current.note,
      // "Swap needs two values." pressed while the top computed stays up.
      error: top?.watch === token ? (resultError(next) ?? current.error) : current.error,
    };
    modelRef.current = updated;
    historyRef.current = { ...historyRef.current, current: updated };
    setModel(updated);
  }, [historyRef, modelRef, setModel]);

  const finishExact = useCallback(
    (request: number, payload: { text: string; re: number; im: number; singular: string | null; touchedLn0: boolean; underflowedExact?: boolean; unverified?: boolean } | { error: string }) => {
      const job = exactJobs.current.get(request);
      exactJobs.current.delete(request);
      inflight.current.fill.delete(request);
      inflight.current.compare.delete(request);
      if (!job) return;
      const current = modelRef.current.stack.find((row) => row.watch === job.watch);
      if (!current || current.cancelled) return;
      if ("error" in payload) {
        if (job.kind !== "fill") {
          publishWatch(job.watch, { ...current, notice: "couldn't verify" });
          return;
        }
        const blank = exactScreen("cancelled");
        publishWatch(job.watch, { ...current, pendingExact: false, cancelled: true, text: blank.text, singular: payload.error });
        return;
      }
      const exact = { re: payload.re, im: payload.im };
      if (job.kind === "compare") {
        if (payload.unverified) {
          publishWatch(job.watch, { ...current, notice: "couldn't verify" });
          return;
        }
        if (!payload.underflowedExact && !beyondFloatBound(job.floated, exact)) return;
        publishWatch(job.watch, { ...current, floatDiffers: true, exactBeside: payload.text });
        return;
      }
      if (payload.unverified) {
        publishWatch(job.watch, { ...current, pendingExact: false, text: "—", value: { re: Number.NaN, im: Number.NaN }, notice: "couldn't verify" });
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
      });
    },
    [modelRef, publishWatch],
  );

  const cancelExact = useCallback(function cancel() {
    // A mode switch or undo shows "computing" before its rows exist. A cancel
    // then waits for them, or the rows it lands would start computing again.
    if (recomputeRef.current) {
      queueRef.current.push(() => cancel());
      return;
    }
    exactJobs.current.clear();
    for (const kind of ["fill", "compare"] as const) {
      exactWorkers.current[kind]?.terminate();
      exactWorkers.current[kind] = null;
      inflight.current[kind].clear();
    }
    const blank = exactScreen("cancelled");
    const stack = modelRef.current.stack.map((item) =>
      item.pendingExact ? { ...item, pendingExact: false, cancelled: true, text: blank.text, value: { re: Number.NaN, im: Number.NaN } } : item,
    );
    const top = stack[stack.length - 1];
    const updated: Model = {
      ...modelRef.current,
      stack,
      note: top?.cancelled ? blank.note : modelRef.current.note,
      error: null,
    };
    modelRef.current = updated;
    historyRef.current = { ...historyRef.current, current: updated };
    setModel(updated);
  }, [historyRef, modelRef, queueRef, recomputeRef, setModel]);

  useEffect(() => {
    const workers = exactWorkers.current;
    // Without workers every exact result comes from the fallback; fetch it before the first press.
    if (typeof Worker === "undefined") void loadExactEngine().catch(() => undefined);
    return () => {
      workers.fill?.terminate();
      workers.compare?.terminate();
    };
  }, []);

  useEffect(() => {
    const run = ({ exactReport, exactToFloat, exactUnderflowsFloat, formatExact }: ExactEngine, request: number, node: Node, bound: Record<string, C>) => {
      try {
        const report = exactReport(node, bound, { maxNodes: 80_000 });
        const exact = exactToFloat(report.value);
        finishExact(request, {
          text: formatExact(report.value),
          re: exact.re,
          im: exact.im,
          singular: report.singular,
          touchedLn0: report.touchedLn0,
          underflowedExact: exactUnderflowsFloat(report.value),
          unverified: report.unverified === true,
        });
      } catch (err) {
        finishExact(request, { error: failure(err) });
      }
    };
    const deliver = (request: number, node: Node, bound: Record<string, C>) => {
      const loaded = loadedExactEngine();
      if (loaded) {
        run(loaded, request, node, bound);
        return;
      }
      loadExactEngine().then(
        (engine) => run(engine, request, node, bound),
        (err: unknown) => finishExact(request, { error: failure(err) }),
      );
    };
    const accept = (data: { type?: string; request?: number; text?: string; re?: number; im?: number; singular?: string | null; touchedLn0?: boolean; underflowedExact?: boolean; unverified?: boolean; message?: string }) => {
      if (data.request === undefined || !exactJobs.current.has(data.request)) return;
      inflight.current.fill.delete(data.request);
      inflight.current.compare.delete(data.request);
      if (data.type === "error") {
        finishExact(data.request, { error: data.message ?? "Exact evaluation failed." });
        return;
      }
      finishExact(data.request, {
        text: data.text ?? "—",
        re: data.re ?? Number.NaN,
        im: data.im ?? Number.NaN,
        singular: data.singular ?? null,
        touchedLn0: data.touchedLn0 === true,
        underflowedExact: data.underflowedExact === true,
        unverified: data.unverified === true,
      });
    };
    const onStack = (watch: number) => stack.some((item) => item.watch === watch);
    for (const watch of followedRef.current) {
      if (!onStack(watch)) followedRef.current.delete(watch);
    }
    // A cleared job must not stay queued in front of the next one. Fill and
    // compare use different workers, and a worker holding a stale job is replaced.
    // Only the top pending exact row is filled. A newer expression pre-empts
    // the one already running, so 1+1 does not wait behind a slow tiny subtraction.
    const topFill = [...stack].reverse().find((item) => item.pendingExact === true && item.cancelled !== true)?.watch;
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
    const fillBusy = [...inflight.current.fill.values()];
    if (topFill !== undefined && fillBusy.some((watch) => watch !== topFill)) {
      exactWorkers.current.fill?.terminate();
      exactWorkers.current.fill = null;
      for (const [request, watch] of inflight.current.fill) {
        exactJobs.current.delete(request);
        followedRef.current.delete(watch);
      }
      inflight.current.fill.clear();
    }
    const ensure = (kind: JobKind): Worker | null => {
      const existing = exactWorkers.current[kind];
      if (existing) return existing;
      if (typeof Worker === "undefined") return null;
      try {
        const created = new Worker(new URL("../../lib/eml/exact.worker.ts", import.meta.url));
        created.onmessage = (event: MessageEvent<Parameters<typeof accept>[0]>) => accept(event.data);
        created.onerror = () => {
          created.terminate();
          // A worker that fails once (blocked script, CSP) will likely fail again: have the fallback ready.
          void loadExactEngine().catch(() => undefined);
          if (exactWorkers.current[kind] === created) exactWorkers.current[kind] = null;
          const pending = [...exactJobs.current.entries()].filter(([, job]) => job.kind === kind);
          for (const [request, job] of pending) {
            const row = modelRef.current.stack.find((item) => item.watch === job.watch);
            if (!row) {
              exactJobs.current.delete(request);
              inflight.current[kind].delete(request);
              continue;
            }
            deliver(request, row.node, row.bound ?? {});
          }
        };
        exactWorkers.current[kind] = created;
        return created;
      } catch {
        return null;
      }
    };
    for (const item of stack) {
      if (item.watch === undefined || followedRef.current.has(item.watch)) continue;
      const fill = item.pendingExact === true && item.cancelled !== true && item.watch === topFill;
      const compare = item.mode === "float" && item.floatDiffers !== true && item.pendingExact !== true && item.notice !== "couldn't verify";
      if (!fill && !compare) {
        if (!(item.pendingExact === true && item.cancelled !== true)) followedRef.current.add(item.watch);
        continue;
      }
      followedRef.current.add(item.watch);
      const request = ++exactSerial.current;
      const kind: JobKind = fill ? "fill" : "compare";
      const bound = item.bound ?? {};
      exactJobs.current.set(request, { watch: item.watch, kind, floated: item.value });
      inflight.current[kind].set(request, item.watch);
      const worker = ensure(kind);
      if (!worker) {
        const node = item.node;
        window.setTimeout(() => deliver(request, node, bound), 0);
        continue;
      }
      const packed = packCircuit(item.node);
      const env: Record<string, { re: number; im: number }> = {};
      for (const [name, value] of Object.entries(bound)) env[name] = { re: value.re, im: value.im };
      worker.postMessage({ request, tokens: packed.tokens, root: packed.root, env });
    }
    startFillWorker.current = () => {
      if (!exactWorkers.current.fill) ensure("fill");
    };
  }, [finishExact, modelRef, stack]);

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
