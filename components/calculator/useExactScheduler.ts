import { useCallback, useEffect, useRef, type MutableRefObject } from "react";
import { type C } from "@/lib/eml/complex";
import { EXACT_MAX_NODES } from "@/lib/eml/exactBudget";
import { beyondFloatBound, exactReport, exactToFloat, exactUnderflowsFloat, formatExact } from "@/lib/eml/exact";
import { compareVerdict, exactProgressNote, exactScreen, fillNotice, type History } from "@/lib/eml/history";
import { type Node } from "@/lib/eml/node";
import { packCircuit } from "@/lib/eml/wire";
import { failure, noteFor, resultError, type Entry, type Model } from "./screen";

type JobKind = "fill" | "compare";

/** What exact.worker.ts posts: "done", "error", or (v1.1, E6) "progress" for each pass. */
export type WorkerMessage = {
  type?: string;
  request?: number;
  text?: string;
  re?: number;
  im?: number;
  singular?: string | null;
  touchedLn0?: boolean;
  underflowedExact?: boolean;
  unverified?: boolean;
  cutHits?: number;
  notCertified?: unknown;
  cancelledZero?: boolean;
  message?: string;
  digits?: number;
  elapsedMs?: number;
};

type ExactPayload =
  | {
      text: string;
      re: number;
      im: number;
      singular: string | null;
      touchedLn0: boolean;
      underflowedExact?: boolean;
      unverified?: boolean;
      cutHits?: number;
      /** v1.1 (E3) */
      notCertified?: boolean;
      cancelledZero?: boolean;
    }
  | { error: string };

/**
 * Fill and compare workers for the exact screen.
 * `cancel()` stops both. A returned cleanup is the hook's own unmount.
 * The stack model stays with the caller; this hook only publishes finished rows.
 */
export function useExactScheduler(input: {
  modelRef: MutableRefObject<Model>;
  historyRef: MutableRefObject<History<Model>>;
  setModel: (next: Model) => void;
  stack: Entry[];
}) {
  const { modelRef, historyRef, setModel, stack } = input;
  const followedRef = useRef(new Set<number>());
  const exactWorkers = useRef<Record<JobKind, Worker | null>>({ fill: null, compare: null });
  const inflight = useRef<Record<JobKind, Map<number, number>>>({ fill: new Map(), compare: new Map() });
  const exactJobs = useRef(new Map<number, { watch: number; kind: JobKind; floated: C }>());
  const exactSerial = useRef(0);

  const publishWatch = useCallback((token: number, next: Entry) => {
    const current = modelRef.current;
    if (!current.stack.some((row) => row.watch === token)) return;
    const rows = current.stack.map((row) => (row.watch === token ? next : row));
    const top = rows[rows.length - 1];
    const updated: Model = {
      ...current,
      stack: rows,
      note: top?.watch === token ? noteFor(next) : current.note,
      error: top?.watch === token ? resultError(next) : current.error,
    };
    modelRef.current = updated;
    historyRef.current = { ...historyRef.current, current: updated };
    setModel(updated);
  }, [historyRef, modelRef, setModel]);

  const finishExact = useCallback(
    (request: number, payload: ExactPayload) => {
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
        // v1.1 (E3): a cancelled or not-certified exact 0 is not shown as the reference.
        const verdict = compareVerdict({
          text: payload.text,
          unverified: payload.unverified === true,
          notCertified: payload.notCertified === true,
          cancelledZero: payload.cancelledZero === true,
          differs: payload.underflowedExact === true || beyondFloatBound(job.floated, exact),
        });
        if (!verdict) return;
        if ("notice" in verdict) {
          publishWatch(job.watch, { ...current, notice: verdict.notice });
          return;
        }
        publishWatch(job.watch, { ...current, floatDiffers: true, exactBeside: verdict.beside });
        return;
      }
      if (payload.unverified) {
        publishWatch(job.watch, { ...current, pendingExact: false, text: "—", value: { re: Number.NaN, im: Number.NaN }, notice: "couldn't verify", cutHits: payload.cutHits });
        return;
      }
      if (!current.pendingExact) return;
      publishWatch(job.watch, {
        ...current,
        pendingExact: false,
        progress: undefined,
        value: exact,
        text: payload.text,
        singular: payload.singular,
        touchedLn0: payload.touchedLn0,
        cutHits: payload.cutHits,
        underflowedExact: payload.underflowedExact === true,
        cancelledZero: payload.cancelledZero === true,
        notCertified: payload.notCertified === true,
        notice: fillNotice({ notCertified: payload.notCertified === true }) ?? current.notice,
      });
    },
    [modelRef, publishWatch],
  );

  const cancel = useCallback(() => {
    exactJobs.current.clear();
    for (const kind of ["fill", "compare"] as const) {
      exactWorkers.current[kind]?.terminate();
      exactWorkers.current[kind] = null;
      inflight.current[kind].clear();
    }
    const blank = exactScreen("cancelled");
    const rows = modelRef.current.stack.map((item) =>
      item.pendingExact ? { ...item, pendingExact: false, cancelled: true, text: blank.text, value: { re: Number.NaN, im: Number.NaN } } : item,
    );
    const top = rows[rows.length - 1];
    const updated: Model = {
      ...modelRef.current,
      stack: rows,
      note: top?.cancelled ? blank.note : modelRef.current.note,
      error: null,
    };
    modelRef.current = updated;
    historyRef.current = { ...historyRef.current, current: updated };
    setModel(updated);
  }, [historyRef, modelRef, setModel]);

  useEffect(() => {
    const workers = exactWorkers.current;
    return () => {
      workers.fill?.terminate();
      workers.compare?.terminate();
    };
  }, []);

  useEffect(() => {
    const deliver = (request: number, node: Node, bound: Record<string, C>) => {
      try {
        const report = exactReport(node, bound, { maxNodes: EXACT_MAX_NODES });
        const exact = exactToFloat(report.value);
        finishExact(request, {
          text: formatExact(report.value),
          re: exact.re,
          im: exact.im,
          singular: report.singular,
          touchedLn0: report.touchedLn0,
          underflowedExact: exactUnderflowsFloat(report.value),
          unverified: report.unverified === true,
          cutHits: report.cutHits,
          notCertified: report.notCertified !== undefined,
          cancelledZero: report.cancelledZero === true,
        });
      } catch (err) {
        finishExact(request, { error: failure(err) });
      }
    };
    const accept = (data: WorkerMessage) => {
      if (data.request === undefined || !exactJobs.current.has(data.request)) return;
      // v1.1 (E6): the worker posts progress on the FIRST pass. It is not the result: the job
      // stays in flight, and only the pending fill row shows the line.
      if (data.type === "progress") {
        const job = exactJobs.current.get(data.request);
        if (!job || job.kind !== "fill") return;
        const row = modelRef.current.stack.find((item) => item.watch === job.watch);
        if (!row || !row.pendingExact || row.cancelled) return;
        publishWatch(job.watch, { ...row, progress: exactProgressNote(data.digits ?? 0, data.elapsedMs ?? 0) });
        return;
      }
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
        cutHits: data.cutHits,
        notCertified: data.notCertified !== undefined && data.notCertified !== null,
        cancelledZero: data.cancelledZero === true,
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
  }, [finishExact, modelRef, publishWatch, stack]);

  return { cancel };
}
