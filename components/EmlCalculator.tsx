"use client";

import { useCallback, useEffect, useMemo, useRef, useState, useSyncExternalStore, type ReactNode } from "react";
import { type C } from "@/lib/eml/complex";
import { beyondFloatBound, exactReport, exactToFloat, exactUnderflowsFloat, formatExact } from "@/lib/eml/exact";
import { packCircuit } from "@/lib/eml/wire";
import { captionName, formatC, isUsable, recognize } from "@/lib/eml/format";
import { ln0Dependence, type GolfHit } from "@/lib/eml/golf";
import {
  BINARY_KEYS,
  CONSTANT_KEYS,
  UNARY_KEYS,
  applyBinaryNode,
  applyUnaryNode,
  binaryNode,
  constantNode,
  integerNode,
  scalarNode,
  seriesShortcutNote,
  unaryNode,
} from "@/lib/eml/library";
import {
  E,
  EmlError,
  EmlLimitError,
  ONE,
  SINGULAR_LN0,
  type Node,
  circuitStats,
  describe,
  evaluateReport,
  isPure,
  nodeFromRpn,
  rpnTokens,
} from "@/lib/eml/node";
import { agreementNote, compileExpression } from "@/lib/eml/parse";
import table from "@/lib/eml/best-known.json";
import { FLOAT_DIFFERS, applyModeSwitch, commitHistory, drainQueue, exactScreen, finiteLossMessage, modeRequest, underflowDisclosure, undoHistory, type History } from "@/lib/eml/history";
import { pressPreviewForNode } from "@/lib/eml/presses";
import { parseProgramInput, programIndexDigits, programNumberText, rankProgram, stepProgram, unnumberedReason, unrankProgram } from "@/lib/eml/programIndex";

const TWO_BUTTONS_KEY = "eml-and-one-two-buttons";
let twoButtonsStored = false;
let twoButtonsLoaded = false;
const twoButtonsListeners = new Set<() => void>();

function subscribeTwoButtons(listener: () => void) {
  twoButtonsListeners.add(listener);
  return () => {
    twoButtonsListeners.delete(listener);
  };
}

function readTwoButtons() {
  if (!twoButtonsLoaded) {
    twoButtonsLoaded = true;
    try {
      twoButtonsStored = window.localStorage.getItem(TWO_BUTTONS_KEY) === "1";
    } catch {
      twoButtonsStored = false;
    }
  }
  return twoButtonsStored;
}

function writeTwoButtons(value: boolean) {
  twoButtonsStored = value;
  twoButtonsLoaded = true;
  try {
    window.localStorage.setItem(TWO_BUTTONS_KEY, value ? "1" : "0");
  } catch {
    /* private mode and blocked storage still toggle for this visit */
  }
  document.documentElement.classList.toggle("ti-two-buttons", value);
  for (const listener of twoButtonsListeners) listener();
}

type Mode = "float" | "exact";

type Entry = {
  value: C;
  text: string;
  singular: string | null;
  mode: Mode;
  node: Node;
  caption: string;
  bound?: Record<string, C>;
  touchedLn0?: boolean;
  overflowed?: boolean;
  underflowed?: boolean;
  nearCut?: boolean;
  pendingExact?: boolean;
  cancelled?: boolean;
  floatDiffers?: boolean;
  exactBeside?: string;
  notice?: string | null;
  watch?: number;
};

type Model = {
  stack: Entry[];
  tape: string[];
  note: string | null;
  error: string | null;
};

const EMPTY: Model = { stack: [], tape: [], note: null, error: null };

const EXAMPLES = [
  { label: "e", expr: "e" },
  { label: "π", expr: "pi" },
  { label: "ln 2", expr: "ln(2)" },
  { label: "√2", expr: "sqrt(2)" },
  { label: "sin(π/6)", expr: "sin(pi/6)" },
  { label: "cos(π/3)", expr: "cos(pi/3)" },
  { label: "2^10", expr: "2^10" },
  { label: "φ", expr: "(1+sqrt(5))/2" },
];

function failure(err: unknown): string {
  if (err instanceof EmlError) return err.message;
  if (err instanceof Error && err.message) return err.message;
  return "That calculation failed.";
}

function isOneAndE(token: string): boolean {
  return token === "1" || token === "E" || token === "x" || token === "y";
}

/** Nested eml text whose leaves are only 1, x, and y — no repaired numbers. */
function pureDescribe(text: string): boolean {
  const leaves = text.split(/eml|[(),\s]+/).filter(Boolean);
  return leaves.length > 0 && leaves.every((leaf) => leaf === "1" || leaf === "x" || leaf === "y");
}

function programText(node: Node): string | null {
  if (node.type !== "eml") return null;
  const stats = circuitStats(node);
  const summary = `K ${stats.rpnLength} · ${stats.dagGates} shared · depth ${stats.depth}`;
  if (stats.dagGates <= 12 && stats.depth <= 10 && stats.rpnLength <= BigInt(48)) {
    const tokens = rpnTokens(node, 48);
    if (tokens && tokens.every(isOneAndE)) return `${tokens.join(" ")} · ${summary}`;
    const nested = describe(node);
    if (nested && pureDescribe(nested)) return nested;
  }
  return summary;
}

function runNode(node: Node, mode: Mode): Pick<Entry, "value" | "text" | "singular" | "mode" | "touchedLn0" | "overflowed" | "underflowed" | "nearCut" | "pendingExact" | "notice"> {
  if (node.type === "one") {
    return { value: { re: 1, im: 0 }, text: "1", singular: null, mode, touchedLn0: false, overflowed: false, underflowed: false, nearCut: false, pendingExact: false, notice: null };
  }
  if (mode === "exact") {
    const blank = exactScreen("computing");
    return {
      value: { re: Number.NaN, im: Number.NaN },
      text: blank.text,
      singular: null,
      mode,
      touchedLn0: false,
      overflowed: false,
      underflowed: false,
      nearCut: false,
      pendingExact: true,
      notice: null,
    };
  }
  try {
    const report = evaluateReport(node, {}, { maxNodes: 80_000 });
    if (report.unverified) {
      return {
        value: { re: Number.NaN, im: Number.NaN },
        text: "—",
        singular: null,
        mode,
        touchedLn0: false,
        overflowed: false,
        underflowed: false,
        nearCut: false,
        pendingExact: false,
        notice: "couldn't verify",
      };
    }
    return {
      value: report.value,
      text: formatC(report.value),
      singular: report.singular,
      mode,
      touchedLn0: report.touchedLn0,
      overflowed: report.overflowed,
      underflowed: report.underflowed,
      nearCut: report.nearCut,
      pendingExact: false,
      notice: null,
    };
  } catch (err) {
    if (!(err instanceof EmlLimitError)) throw err;
    return {
      value: { re: Number.NaN, im: Number.NaN },
      text: "—",
      singular: null,
      mode,
      touchedLn0: false,
      overflowed: false,
      underflowed: false,
      nearCut: false,
      pendingExact: false,
      notice: "couldn't verify",
    };
  }
}

function programFlags(item: Entry): string | null {
  const bits: string[] = [];
  if (item.value.re === Infinity) bits.push("+∞");
  else if (item.value.re === -Infinity) bits.push("−∞");
  if (item.value.im === Infinity) bits.push("+∞i");
  else if (item.value.im === -Infinity) bits.push("−∞i");
  if (item.touchedLn0) bits.push("ln 0");
  return bits.length ? bits.join(" · ") : null;
}

function agreementText(caption: string, value: C, variables: Record<string, C>, text: string): string | null {
  return agreementNote(caption, value, variables, text);
}

function shownSingular(item: Entry): string | null {
  if (
    item.singular === SINGULAR_LN0 &&
    Number.isFinite(item.value.re) &&
    Number.isFinite(item.value.im)
  ) {
    return null;
  }
  return item.singular;
}

function noteFor(item: Entry): string | null {
  const number = programNumberText(item.node);
  const bits = [
    programText(item.node),
    number,
    number ? programFlags(item) : null,
    item.pendingExact ? exactScreen("computing").note : null,
    item.cancelled ? exactScreen("cancelled").note : null,
    item.floatDiffers && item.exactBeside ? `${FLOAT_DIFFERS} · ${item.exactBeside}` : null,
    item.notice,
    item.overflowed ? "overflow" : null,
    underflowDisclosure(item.value, item.underflowed === true),
    item.nearCut ? "on or very near the branch cut" : null,
    seriesShortcutNote(item.node),
    isPure(item.node) ? "pure" : null,
    shownSingular(item),
    agreementText(item.caption, item.value, item.bound ?? {}, item.text),
  ].filter(Boolean);
  return bits.length ? bits.join(" · ") : null;
}

function shortcutTitle(node: Node, hint?: string): string {
  const presses = pressPreviewForNode(node);
  const lead = hint ? `${hint}. ` : "";
  if (!presses) return `${lead}Shortcut for the 1 and EML keys.`;
  return `${lead}Presses ${presses.preview}${presses.truncated ? ` (${presses.presses} presses)` : ""}`;
}

function CopyNumber({ text }: { text: string }) {
  const [copied, setCopied] = useState(false);
  return (
    <button
      type="button"
      className="ti-lcd-btn"
      title={text}
      aria-label={`Copy ${text}`}
      onClick={() => {
        const clip = navigator.clipboard;
        if (!clip) return;
        void clip.writeText(text).then(() => setCopied(true)).catch(() => undefined);
      }}
    >
      {copied ? "Copied" : "Copy number"}
    </button>
  );
}

function PressLine({ node }: { node: Node | null }) {
  const [copied, setCopied] = useState(false);
  if (!node) return null;
  const view = pressPreviewForNode(node);
  if (!view) {
    return <p className="ti-press">Binary applies only to programs of the 1 and EML keys.</p>;
  }
  return (
    <div>
      <p className="ti-press">
        {view.preview} ({view.presses.toString()} presses)
      </p>
      <div className="ti-press-meta">
        <span>1 = 1 key, 0 = EML. Within one length, a higher program number is a lower binary value, because 1 comes before E.</span>
        {view.usesVariables ? <span>x and y stay in the string</span> : null}
        {view.copyable ? (
          <button
            type="button"
            className="ti-lcd-btn"
            onClick={() => {
              void navigator.clipboard.writeText(view.full).then(() => setCopied(true)).catch(() => undefined);
            }}
          >
            {copied ? "Copied" : "Copy"}
          </button>
        ) : null}
      </div>
    </div>
  );
}

function golfLabel(id: string): string {
  if (id === "ipi") return "+iπ";
  if (id === "-ipi") return "−iπ";
  return id;
}

function clip(text: string, max = 72): string {
  return text.length <= max ? text : `${text.slice(0, max - 1)}…`;
}

function unaryCaption(id: string, label: string, arg: string): string {
  if (id === "inv") return `1/(${arg})`;
  if (id === "minus") return `−(${arg})`;
  if (id === "sqr") return `(${arg})²`;
  if (id === "sqrt") return `√(${arg})`;
  return `${label}(${arg})`;
}

function binaryCaption(id: string, x: string, y: string): string {
  if (id === "add") return `${x} + ${y}`;
  if (id === "sub") return `${x} − ${y}`;
  if (id === "mul") return `${x} × ${y}`;
  if (id === "div") return `${x} ÷ ${y}`;
  if (id === "pow") return `${x}^${y}`;
  if (id === "log") return `log(${x}, ${y})`;
  if (id === "avg") return `avg(${x}, ${y})`;
  if (id === "hypot") return `hypot(${x}, ${y})`;
  return `${x} ${id} ${y}`;
}

let watchSerial = 1;

function resultError(item: Entry): string | null {
  if (item.pendingExact || item.cancelled) return null;
  // (10^400+1)/7 is finite in exact arithmetic and only overflows as a float.
  // The printed exact value stays, without a second "left the finite numbers".
  return finiteLossMessage({
    usable: isUsable(item.value),
    notice: item.notice,
    singular: shownSingular(item),
    mode: item.mode,
    text: item.text,
  });
}

function entry(node: Node, caption: string, mode: Mode): Entry {
  return { node, caption, watch: watchSerial++, ...runNode(node, mode) };
}

function readScalar(text: string): Node {
  const trimmed = text.trim();
  try {
    return scalarNode(trimmed);
  } catch {
    return compileExpression(trimmed, {});
  }
}

function valuesOf(xText: string, yText: string): Record<string, C> {
  const bound: Record<string, C> = {};
  try {
    bound.x = evaluateReport(readScalar(xText)).value;
  } catch {
    /* the field is not a value yet */
  }
  try {
    bound.y = evaluateReport(readScalar(yText)).value;
  } catch {
    /* the field is not a value yet */
  }
  return bound;
}

function KeyButton({
  children,
  onClick,
  title,
  ariaLabel,
  disabled = false,
  tone = "plain",
  secondary,
  onReveal,
}: {
  children: ReactNode;
  onClick: () => void;
  title?: string;
  ariaLabel?: string;
  disabled?: boolean;
  tone?: "plain" | "one" | "eml";
  secondary?: string;
  onReveal?: (text: string) => void;
}) {
  const revealed = useRef(false);
  return (
    <div className="ti-key">
      {secondary ? (
        <span className={tone === "plain" ? "ti-key-alt" : "ti-key-alt ti-key-alt-strong"}>{secondary}</span>
      ) : (
        <span className="ti-key-alt" aria-hidden="true" />
      )}
      <button
        type="button"
        title={title}
        aria-label={ariaLabel}
        aria-disabled={disabled || undefined}
        onClick={() => {
          if (revealed.current) {
            revealed.current = false;
            return;
          }
          if (disabled) return;
          onClick();
        }}
        onPointerDown={() => {
          if (!title || !onReveal) return;
          revealed.current = false;
          const timer = window.setTimeout(() => {
            revealed.current = true;
            onReveal(title);
          }, 450);
          const end = () => {
            window.clearTimeout(timer);
            if (!revealed.current) return;
            // pointerup outside the button does not deliver a click, so the
            // flag would swallow the next key. Drop it on the next turn if
            // this click does not consume it first.
            window.setTimeout(() => {
              revealed.current = false;
            }, 0);
          };
          window.addEventListener("pointerup", end, { once: true });
          window.addEventListener("pointercancel", end, { once: true });
        }}
        className={disabled ? `ti-btn ti-btn-${tone} is-quiet` : `ti-btn ti-btn-${tone}`}
      >
        {children}
      </button>
    </div>
  );
}

function GolfPanel() {
  const [line, setLine] = useState("Search constants up to K 21. The slow script runs through K 35.");
  const [busy, setBusy] = useState(false);
  const workerRef = useRef<Worker | null>(null);
  const requestRef = useRef(0);

  useEffect(() => () => {
    workerRef.current?.terminate();
    workerRef.current = null;
  }, []);

  function stop() {
    requestRef.current += 1;
    // The search loop does not yield, so a stop message never arrives. Ending the worker is the cancel.
    workerRef.current?.terminate();
    workerRef.current = null;
    setBusy(false);
  }

  function start(allowLn0: boolean) {
    stop();
    const request = requestRef.current;
    const worker = new Worker(new URL("../lib/eml/golf.worker.ts", import.meta.url));
    workerRef.current = worker;
    setBusy(true);
    setLine("Searching…");
    worker.onmessage = (event: MessageEvent<{ type: string; request?: number; k?: number; pool?: number; hits?: GolfHit[]; message?: string }>) => {
      const data = event.data;
      if (data.request !== request) return;
      if (data.type === "progress") setLine(`K ${data.k} · ${data.pool} new circuits`);
      if (data.type === "error") {
        setLine(data.message ?? "The search worker failed.");
        setBusy(false);
        worker.terminate();
        if (workerRef.current === worker) workerRef.current = null;
      }
      if (data.type === "done") {
        const text = (data.hits ?? [])
          .map((hit) => {
            const dependence = ln0Dependence(hit);
            return `${golfLabel(hit.id)} = K ${hit.k}${dependence ? ` · ${dependence}` : ""}`;
          })
          .join(" · ");
        setLine(text || "No constants in range.");
        setBusy(false);
        worker.terminate();
        if (workerRef.current === worker) workerRef.current = null;
      }
    };
    worker.onerror = () => {
      if (requestRef.current !== request) return;
      setLine("The search worker failed.");
      worker.terminate();
      if (workerRef.current === worker) workerRef.current = null;
      setBusy(false);
    };
    worker.postMessage({ maxK: 21, request, allowLn0 });
  }

  return (
    <details className="ti-fold">
      <summary>Circuit golf</summary>
      <p>{line}</p>
      <div className="ti-manual-actions">
        <button type="button" onClick={() => start(true)} disabled={busy} className="ti-text-btn ti-text-btn-strong">
          Search with ln 0
        </button>
        <button type="button" onClick={() => start(false)} disabled={busy} className="ti-text-btn">
          Search without ln 0
        </button>
        <button type="button" onClick={stop} disabled={!busy} className="ti-text-btn">
          Cancel
        </button>
      </div>
    </details>
  );
}

export function EmlCalculator() {
  const [model, setModel] = useState<Model>(EMPTY);
  const [xText, setXText] = useState("0.5");
  const [yText, setYText] = useState("2");
  const [expr, setExpr] = useState("sin(pi/6)");
  const [programField, setProgramField] = useState("");
  const [mode, setMode] = useState<Mode>("exact");
  const twoButtons = useSyncExternalStore(subscribeTwoButtons, readTwoButtons, () => false);
  const [heldShortcut, setHeldShortcut] = useState<string | null>(null);
  const modelRef = useRef(model);
  const textRef = useRef({ xText, yText });
  const modeRef = useRef<Mode>("exact");
  const historyRef = useRef<History<Model>>({ past: [], current: EMPTY });
  const recomputeRef = useRef(false);
  const queueRef = useRef<Array<() => void>>([]);
  const jobRef = useRef(0);
  const twoButtonsRef = useRef(false);
  twoButtonsRef.current = twoButtons;
  const costs = useMemo(() => {
    const table: Record<string, string> = {};
    const label = (node: Node) => {
      const k = circuitStats(node).rpnLength;
      return k <= BigInt(9999) ? `K ${k}` : "wide";
    };
    for (const key of CONSTANT_KEYS) {
      try {
        table[key.id] = label(constantNode(key.id));
      } catch {
        table[key.id] = "";
      }
    }
    let xNode = integerNode(2);
    let yNode = integerNode(3);
    try {
      if (model.stack.length >= 2) {
        xNode = model.stack[model.stack.length - 2]?.node ?? xNode;
        yNode = model.stack[model.stack.length - 1]?.node ?? yNode;
      } else if (model.stack.length === 1) {
        xNode = model.stack[0]?.node ?? xNode;
        yNode = readScalar(yText);
      } else {
        xNode = readScalar(xText);
        yNode = readScalar(yText);
      }
    } catch {
      xNode = integerNode(2);
      yNode = integerNode(3);
    }
    const arg = model.stack[model.stack.length - 1]?.node ?? xNode;
    for (const key of UNARY_KEYS) {
      try {
        table[key.id] = label(applyUnaryNode(key.id, arg));
      } catch {
        table[key.id] = "";
      }
    }
    for (const key of BINARY_KEYS) {
      try {
        table[key.id] = label(applyBinaryNode(key.id, xNode, yNode));
      } catch {
        table[key.id] = "";
      }
    }
    return table;
  }, [model.stack, xText, yText]);

  useEffect(() => {
    modelRef.current = model;
    textRef.current = { xText, yText };
    modeRef.current = mode;
  }, [model, xText, yText, mode]);

  const followedRef = useRef(new Set<number>());
  type JobKind = "fill" | "compare";
  const exactWorkers = useRef<Record<JobKind, Worker | null>>({ fill: null, compare: null });
  const inflight = useRef<Record<JobKind, Map<number, number>>>({ fill: new Map(), compare: new Map() });
  const exactJobs = useRef(new Map<number, { watch: number; kind: JobKind; floated: C }>());
  const exactSerial = useRef(0);

  const publishWatch = useCallback((token: number, next: Entry) => {
    const current = modelRef.current;
    if (!current.stack.some((row) => row.watch === token)) return;
    const stack = current.stack.map((row) => (row.watch === token ? next : row));
    const top = stack[stack.length - 1];
    const updated: Model = {
      ...current,
      stack,
      note: top?.watch === token ? noteFor(next) : current.note,
      error: top?.watch === token ? resultError(next) : current.error,
    };
    modelRef.current = updated;
    historyRef.current = { ...historyRef.current, current: updated };
    setModel(updated);
  }, []);

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
    [publishWatch],
  );

  const cancelExact = useCallback(() => {
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
  }, []);

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
    const onStack = (watch: number) => model.stack.some((item) => item.watch === watch);
    for (const watch of followedRef.current) {
      if (!onStack(watch)) followedRef.current.delete(watch);
    }
    // A cleared job must not stay queued in front of the next one. Fill and
    // compare use different workers, and a worker holding a stale job is replaced.
    // Only the top pending exact row is filled. A newer expression pre-empts
    // the one already running, so 1+1 does not wait behind a slow tiny subtraction.
    const topFill = [...model.stack].reverse().find((item) => item.pendingExact === true && item.cancelled !== true)?.watch;
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
        const created = new Worker(new URL("../lib/eml/exact.worker.ts", import.meta.url));
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
    for (const item of model.stack) {
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
  }, [finishExact, model.stack]);

  const expansions = useMemo(() => {
    const table: Record<string, string> = {};
    for (const key of CONSTANT_KEYS) {
      try {
        table[key.id] = shortcutTitle(constantNode(key.id), key.label);
      } catch {
        table[key.id] = "Shortcut for the 1 and EML keys.";
      }
    }
    for (const key of UNARY_KEYS) {
      try {
        table[key.id] = shortcutTitle(unaryNode(key.id), key.label);
      } catch {
        table[key.id] = "Shortcut for the 1 and EML keys.";
      }
    }
    for (const key of BINARY_KEYS) {
      try {
        table[key.id] = shortcutTitle(binaryNode(key.id), key.hint);
      } catch {
        table[key.id] = key.hint;
      }
    }
    return table;
  }, []);

  useEffect(() => {
    const snapshot = modelRef.current.stack.map((item) => ({ ...item }));
    if (snapshot.length === 0) return;
    let cancel = false;
    jobRef.current += 1;
    recomputeRef.current = true;
    setModel((current) => ({
      ...current,
      stack: mode === "exact" ? current.stack.map((item) => ({ ...item, text: "computing", pendingExact: true, value: { re: Number.NaN, im: Number.NaN } })) : current.stack,
      note: mode === "exact" ? "computing" : "Computing…",
      error: null,
    }));
    void (async () => {
      const stack: Entry[] = [];
      let error: string | null = null;
      try {
        for (const item of snapshot) {
          if (cancel) return;
          await new Promise((resolve) => setTimeout(resolve, 0));
          if (cancel) return;
          stack.push({ ...entry(item.node, item.caption, mode), bound: item.bound });
        }
      } catch (err) {
        error = failure(err);
      }
      if (cancel) return;
      const current = modelRef.current;
      const applied = applyModeSwitch({
        previous: snapshot,
        recomputed: stack,
        error,
        fail: (item, message) => ({
          node: item.node,
          caption: item.caption,
          bound: item.bound,
          value: { re: Number.NaN, im: Number.NaN },
          text: "—",
          singular: message,
          mode,
          touchedLn0: false,
          overflowed: false,
          underflowed: false,
          nearCut: false,
        }),
      });
      const shown = [...applied.stack, ...current.stack.slice(snapshot.length)];
      const top = shown[shown.length - 1];
      const next: Model = {
        ...current,
        stack: shown,
        note: applied.error ? null : top ? noteFor(top) : null,
        error: applied.error ?? (top ? resultError(top) : null),
      };
      historyRef.current = { ...historyRef.current, current: next };
      modelRef.current = next;
      setModel(next);
      recomputeRef.current = false;
      drainQueue(queueRef.current);
    })();
    return () => {
      cancel = true;
      recomputeRef.current = false;
    };
  }, [mode]);

  const commit = useCallback((next: Model) => {
    historyRef.current = commitHistory(historyRef.current, next);
    modelRef.current = next;
    setModel(next);
  }, []);

  const pushEntry = useCallback(
    (item: Entry, tapeLabel: string, note: string | null) => {
      const current = modelRef.current;
      commit({
        stack: [...current.stack, item],
        tape: [...current.tape, tapeLabel],
        note,
        error: resultError(item),
      });
    },
    [commit],
  );

  const pushNode = useCallback(
    (node: Node, caption: string, tapeLabel: string) => {
      if (recomputeRef.current) {
        queueRef.current.push(() => pushNode(node, caption, tapeLabel));
        return;
      }
      try {
        const item = entry(node, caption, modeRef.current);
        const known = recognize(item.value);
        const name = known && known !== caption ? `this is ${known}` : null;
        const bits = [noteFor(item), name].filter(Boolean);
        pushEntry(item, tapeLabel, bits.length ? bits.join(" · ") : null);
      } catch (err) {
        const next = { ...modelRef.current, error: failure(err) };
        modelRef.current = next;
        setModel(next);
      }
    },
    [pushEntry],
  );

  const pushOne = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => pushOne());
      return;
    }
    pushNode(ONE, "1", "1");
  }, [pushNode]);

  const pushScalar = useCallback(
    (text: string, tapeLabel: string) => {
      if (recomputeRef.current) {
        queueRef.current.push(() => pushScalar(text, tapeLabel));
        return;
      }
      try {
        const node = readScalar(text);
        const item = {
          ...entry(node, text.trim(), modeRef.current),
          bound: valuesOf(textRef.current.xText, textRef.current.yText),
        };
        const known = recognize(item.value);
        const name = known && known !== item.caption ? `this is ${known}` : null;
        const bits = [noteFor(item), name].filter(Boolean);
        pushEntry(item, tapeLabel, bits.length ? bits.join(" · ") : null);
      } catch (err) {
        const next = { ...modelRef.current, error: failure(err) };
        modelRef.current = next;
        setModel(next);
      }
    },
    [pushEntry],
  );

  const applyEml = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => applyEml());
      return;
    }
    const current = modelRef.current;
    try {
      let x: Entry;
      let y: Entry;
      let rest: Entry[];
      if (current.stack.length >= 2) {
        y = current.stack[current.stack.length - 1];
        x = current.stack[current.stack.length - 2];
        rest = current.stack.slice(0, -2);
      } else if (current.stack.length === 0 && !twoButtonsRef.current) {
        const rawX = textRef.current.xText;
        const rawY = textRef.current.yText;
        const numbers = valuesOf(rawX, rawY);
        x = { ...entry(readScalar(rawX), rawX.trim() || "x", modeRef.current), bound: numbers };
        y = { ...entry(readScalar(rawY), rawY.trim() || "y", modeRef.current), bound: numbers };
        rest = [];
      } else {
        const next = {
          ...current,
          error: "EML needs two values. The older one is x, the top one is y.",
        };
        modelRef.current = next;
        setModel(next);
        return;
      }
      const node = E(x.node, y.node);
      const caption = clip(`eml(${x.caption}, ${y.caption})`);
      const item = { ...entry(node, caption, modeRef.current), bound: { ...x.bound, ...y.bound } };
      commit({
        stack: [...rest, item],
        tape: [...current.tape, "E"],
        note: noteFor(item),
        error: resultError(item),
      });
    } catch (err) {
      const next = { ...modelRef.current, error: failure(err) };
      modelRef.current = next;
      setModel(next);
    }
  }, [commit]);

  function fail(error: string) {
    const next = { ...modelRef.current, error };
    modelRef.current = next;
    setModel(next);
  }

  function applyUnary(id: string, label: string) {
    if (recomputeRef.current) {
      queueRef.current.push(() => applyUnary(id, label));
      return;
    }
    const current = modelRef.current;
    try {
      let arg: Entry;
      let rest: Entry[];
      if (current.stack.length > 0) {
        arg = current.stack[current.stack.length - 1];
        rest = current.stack.slice(0, -1);
      } else {
        const raw = textRef.current.xText;
        arg = {
          ...entry(readScalar(raw), raw.trim() || "x", modeRef.current),
          bound: valuesOf(raw, textRef.current.yText),
        };
        rest = [];
      }
      const node = applyUnaryNode(id, arg.node);
      const caption = clip(unaryCaption(id, label, arg.caption));
      const item = { ...entry(node, caption, modeRef.current), bound: arg.bound };
      commit({
        stack: [...rest, item],
        tape: [...current.tape, label],
        note: noteFor(item),
        error: resultError(item),
      });
    } catch (err) {
      fail(failure(err));
    }
  }

  function applyBinary(id: string, label: string) {
    if (recomputeRef.current) {
      queueRef.current.push(() => applyBinary(id, label));
      return;
    }
    const current = modelRef.current;
    try {
      let x: Entry;
      let y: Entry;
      let rest: Entry[];
      if (current.stack.length >= 2) {
        y = current.stack[current.stack.length - 1];
        x = current.stack[current.stack.length - 2];
        rest = current.stack.slice(0, -2);
      } else if (current.stack.length === 0) {
        const rawX = textRef.current.xText;
        const rawY = textRef.current.yText;
        const numbers = valuesOf(rawX, rawY);
        x = { ...entry(readScalar(rawX), rawX.trim() || "x", modeRef.current), bound: numbers };
        y = { ...entry(readScalar(rawY), rawY.trim() || "y", modeRef.current), bound: numbers };
        rest = [];
      } else {
        fail("Push a second value. The older one is x and the top one is y.");
        return;
      }
      const node = applyBinaryNode(id, x.node, y.node);
      const caption = clip(binaryCaption(id, x.caption, y.caption));
      const item = { ...entry(node, caption, modeRef.current), bound: { ...x.bound, ...y.bound } };
      commit({
        stack: [...rest, item],
        tape: [...current.tape, label],
        note: noteFor(item),
        error: resultError(item),
      });
    } catch (err) {
      fail(failure(err));
    }
  }

  function compute(source: string) {
    if (recomputeRef.current) {
      queueRef.current.push(() => compute(source));
      return;
    }
    const text = source.trim();
    setExpr(text);
    const current = modelRef.current;
    if (!text) {
      fail("Enter an expression.");
      return;
    }
    try {
      const variables: Record<string, Node> = {};
      const numbers: Record<string, C> = {};
      if (/\bx\b/i.test(text)) {
        variables.x = readScalar(textRef.current.xText);
        numbers.x = evaluateReport(variables.x).value;
      }
      if (/\by\b/i.test(text)) {
        variables.y = readScalar(textRef.current.yText);
        numbers.y = evaluateReport(variables.y).value;
      }
      const node = compileExpression(text, variables);
      const item = { ...entry(node, text, modeRef.current), bound: numbers };
      const bits = [noteFor(item)].filter(Boolean);
      commit({
        stack: [...current.stack, item],
        tape: [...current.tape, text],
        note: bits.length ? bits.join(" · ") : null,
        error: resultError(item),
      });
    } catch (err) {
      fail(failure(err));
    }
  }

  function swap() {
    if (recomputeRef.current) {
      queueRef.current.push(() => swap());
      return;
    }
    const current = modelRef.current;
    if (current.stack.length < 2) {
      fail("Swap needs two values.");
      return;
    }
    const next = current.stack.slice();
    const last = next.length - 1;
    const top = next[last];
    next[last] = next[last - 1];
    next[last - 1] = top;
    const shown = next[last];
    commit({
      stack: next,
      tape: [...current.tape, "swap"],
      note: shown ? noteFor(shown) : null,
      error: null,
    });
  }

  function drop() {
    if (recomputeRef.current) {
      queueRef.current.push(() => drop());
      return;
    }
    const current = modelRef.current;
    if (current.stack.length === 0) {
      fail("The stack is empty.");
      return;
    }
    const stack = current.stack.slice(0, -1);
    const shown = stack[stack.length - 1];
    commit({
      stack,
      tape: [...current.tape, "drop"],
      note: shown ? noteFor(shown) : null,
      error: null,
    });
  }

  const requestMode = useCallback((next: Mode) => {
    const step = modeRequest(modeRef.current, next, recomputeRef.current);
    if (step.queue) {
      queueRef.current.push(() => requestMode(next));
      return;
    }
    if (step.current === modeRef.current) return;
    modeRef.current = step.current;
    setMode(step.current);
  }, []);

  const undo = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => undo());
      return;
    }
    const nextHistory = undoHistory(historyRef.current);
    if (nextHistory === historyRef.current) return;
    historyRef.current = nextHistory;
    const previous = nextHistory.current;
    const job = (jobRef.current += 1);
    const modeNow = modeRef.current;
    recomputeRef.current = true;
    void (async () => {
      const built: Entry[] = [];
      let error: string | null = null;
      try {
        for (const item of previous.stack) {
          await new Promise((resolve) => setTimeout(resolve, 0));
          if (job !== jobRef.current) return;
          built.push({ ...entry(item.node, item.caption, modeNow), bound: item.bound });
        }
      } catch (err) {
        error = failure(err);
      }
      if (job !== jobRef.current) return;
      const applied = applyModeSwitch({
        previous: previous.stack,
        recomputed: built,
        error,
        fail: (item, message) => ({
          ...item,
          value: { re: Number.NaN, im: Number.NaN },
          text: "—",
          singular: message,
          mode: modeNow,
        }),
      });
      const top = applied.stack[applied.stack.length - 1];
      const restored: Model = {
        ...previous,
        stack: applied.stack,
        note: applied.error ? null : top ? noteFor(top) : previous.note,
        error: applied.error,
      };
      historyRef.current = { ...historyRef.current, current: restored };
      modelRef.current = restored;
      setModel(restored);
      recomputeRef.current = false;
      drainQueue(queueRef.current);
    })();
  }, []);

  function clearAll() {
    if (recomputeRef.current) {
      queueRef.current.push(() => clearAll());
      return;
    }
    setExpr("");
    commit(EMPTY);
  }

  function showProgram(node: Node, caption: string, replace: boolean, notice?: string | null) {
    if (recomputeRef.current) {
      queueRef.current.push(() => showProgram(node, caption, replace, notice));
      return;
    }
    const job = (jobRef.current += 1);
    const previous = modelRef.current;
    const mode = modeRef.current;
    if (mode === "exact") {
      const item = { ...entry(node, caption, mode), notice };
      const rest = replace && previous.stack.length > 0 ? previous.stack.slice(0, -1) : previous.stack;
      const next: Model = {
        stack: [...rest, item],
        tape: [...previous.tape, caption],
        note: noteFor(item),
        error: resultError(item),
      };
      historyRef.current = commitHistory(historyRef.current, next);
      modelRef.current = next;
      setModel(next);
      return;
    }
    recomputeRef.current = true;
    const pending = { ...previous, note: "Computing…", error: null };
    modelRef.current = pending;
    setModel(pending);
    void (async () => {
      await new Promise((resolve) => setTimeout(resolve, 0));
      if (job !== jobRef.current) return;
      try {
        const item = entry(node, caption, mode);
        const rest = replace && previous.stack.length > 0 ? previous.stack.slice(0, -1) : previous.stack;
        const next: Model = {
          stack: [...rest, item],
          tape: [...previous.tape, caption],
          note: [noteFor(item), notice].filter(Boolean).join(" · ") || null,
          error: resultError(item),
        };
        historyRef.current = commitHistory({ ...historyRef.current, current: previous }, next);
        modelRef.current = next;
        setModel(next);
      } catch (err) {
        const next = { ...previous, note: previous.note, error: failure(err) };
        modelRef.current = next;
        setModel(next);
      }
      if (job !== jobRef.current) return;
      recomputeRef.current = false;
      drainQueue(queueRef.current);
    })();
  }

  function loadProgramText(source: string) {
    try {
      const parsed = parseProgramInput(source);
      if (parsed.kind === "index") {
        showProgram(unrankProgram(parsed.index), `program #${parsed.index.toString()}`, false);
        return;
      }
      const from = parsed.rotatedFrom;
      const to = from && from.includes("0") ? parsed.word.replace(/E/g, "0") : parsed.word;
      const notice = from ? `Rotated ${from} to ${to}.` : null;
      showProgram(nodeFromRpn(parsed.word.split("")), parsed.word, false, notice);
    } catch (err) {
      fail(failure(err));
    }
  }

  function stepLoaded(delta: 1 | -1) {
    if (recomputeRef.current) {
      queueRef.current.push(() => stepLoaded(delta));
      return;
    }
    const top = modelRef.current.stack[modelRef.current.stack.length - 1];
    let index = BigInt(0);
    if (top) {
      const rank = rankProgram(top.node);
      if (rank === null) {
        fail(unnumberedReason(top.node) ?? "That value is not a numbered program.");
        return;
      }
      if (rank === BigInt(0) && delta < 0) {
        fail("Program numbers start at 0.");
        return;
      }
      index = stepProgram(rank, delta);
    } else if (delta < 0) {
      fail("Program numbers start at 0.");
      return;
    }
    try {
      showProgram(unrankProgram(index), `program #${index.toString()}`, Boolean(top));
    } catch (err) {
      fail(failure(err));
    }
  }

  useEffect(() => {
    function onKey(event: KeyboardEvent) {
      const target = event.target;
      if (event.metaKey || event.ctrlKey || event.altKey) return;
      if (target instanceof HTMLElement && target.closest("input, textarea")) return;
      const key = event.key;
      if (key !== "1" && key !== "e" && key !== "E" && key !== "x" && key !== "y" && key !== "Backspace" && key !== "Escape") return;
      if (twoButtonsRef.current && (key === "x" || key === "y")) return;
      event.preventDefault();
      const run = () => {
        if (key === "1") pushOne();
        else if (key === "e" || key === "E") applyEml();
        else if (key === "x") pushScalar(xText, "x");
        else if (key === "y") pushScalar(yText, "y");
        else if (key === "Backspace") undo();
        else if (key === "Escape") {
          const next = { ...modelRef.current, error: null };
          modelRef.current = next;
          setModel(next);
        }
      };
      if (recomputeRef.current) queueRef.current.push(run);
      else run();
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [applyEml, pushOne, pushScalar, undo, xText, yText]);

  const buried = model.stack.slice(-4, -1);
  const top = model.stack[model.stack.length - 1];
  const readout = top ? top.text : "0";
  const named = top ? captionName(top.text, top.value, top.caption) : null;
  const fullDigits = top ? programIndexDigits(top.node) : null;
  const fullNumber = fullDigits && fullDigits.length > 16 ? `#${fullDigits}` : null;

  return (
    <main className="ti-stage">
      <div className={twoButtons ? "ti-device ti-device-two" : "ti-device"}>
        <div className="ti-top">
          <div>
            <h1 className="ti-wordmark">EML and One</h1>
            <p className="ti-model">a two-button calculator</p>
          </div>
        </div>

        <div className="ti-bezel">
          <div className="ti-lcd" role="region" aria-label="Calculator screen">
            <p className="ti-lcd-status">
              <span>{mode === "exact" ? "exact" : "hardware view"}</span>
              <span>x older · y on top</span>
            </p>
            <div className="ti-lcd-stack">
              {buried.map((item, index) => (
                <p key={`${item.caption}-${index}`}>
                  {item.text} {item.caption}
                </p>
              ))}
            </div>
            <p className="ti-lcd-result" aria-live="polite">
              {readout}
            </p>
            <p className="ti-lcd-caption">
              {top ? top.caption : "Press 1, then 1, then EML. That is e."}
              {named ? ` · ${named}` : ""}
            </p>
            {top?.floatDiffers && top.exactBeside ? <p className="ti-lcd-flag">{FLOAT_DIFFERS} · {top.exactBeside}</p> : null}
            {top && shownSingular(top) ? <p className="ti-lcd-flag">{shownSingular(top)}</p> : null}
            {model.note ? (
              <div className="ti-lcd-note">
                <span title={fullNumber ?? undefined}>{model.note}</span>
                {fullNumber ? <CopyNumber text={fullNumber} /> : null}
              </div>
            ) : null}
            {model.error ? <p className="ti-lcd-error">{model.error}</p> : null}
            <PressLine key={top?.node.id ?? 0} node={top?.node ?? null} />
            {heldShortcut ? <p className="ti-lcd-hold">{heldShortcut}</p> : null}
          </div>
        </div>

        <div className="ti-modes">
          <button
            type="button"
            aria-pressed={twoButtons}
            onClick={() => writeTwoButtons(!twoButtons)}
            className={twoButtons ? "ti-btn ti-btn-2nd is-down" : "ti-btn ti-btn-2nd"}
          >
            Two buttons only
          </button>
          <div role="radiogroup" aria-label="Evaluation" className="ti-radio">
            <button
              type="button"
              role="radio"
              aria-checked={mode === "float"}
              onClick={() => requestMode("float")}
              onKeyDown={(event) => {
                if (event.key === "ArrowRight" || event.key === "ArrowDown") {
                  event.preventDefault();
                  requestMode("exact");
                  const next = event.currentTarget.nextElementSibling;
                  if (next instanceof HTMLButtonElement) next.focus();
                }
              }}
              className={mode === "float" ? "ti-btn ti-btn-alpha is-down" : "ti-btn ti-btn-alpha"}
            >
              hardware
            </button>
            <button
              type="button"
              role="radio"
              aria-checked={mode === "exact"}
              onClick={() => requestMode("exact")}
              onKeyDown={(event) => {
                if (event.key === "ArrowLeft" || event.key === "ArrowUp") {
                  event.preventDefault();
                  requestMode("float");
                  const previous = event.currentTarget.previousElementSibling;
                  if (previous instanceof HTMLButtonElement) previous.focus();
                }
              }}
              className={mode === "exact" ? "ti-btn ti-btn-alpha is-down" : "ti-btn ti-btn-alpha"}
            >
              exact
            </button>
          </div>
          {model.stack.some((item) => item.pendingExact) ? (
            <button type="button" className="ti-btn ti-btn-alpha" onClick={cancelExact}>
              Cancel
            </button>
          ) : null}
        </div>
        <p className="ti-case-note">
          {mode === "exact"
            ? "Exact value of this circuit. Cancel stops a long one, and the previous number comes down."
            : "Hardware view: the raw 64-bit float value of these gates. A disagreement is flagged, with the exact value beside it."}
        </p>
          {twoButtons ? null : (
          <div className="ti-fields">
            <label className="ti-label">
              x
              <input
                value={xText}
                onChange={(event) => setXText(event.target.value)}
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
            <label className="ti-label">
              y
              <input
                value={yText}
                onChange={(event) => setYText(event.target.value)}
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
          </div>
          )}

          <div className="ti-prime">
            <KeyButton tone="one" secondary="const" onClick={pushOne} title="Push the constant 1. This is one press: 1" ariaLabel="Push the constant 1. This is one press: 1">
              1
            </KeyButton>
            <KeyButton tone="eml" secondary="exp − ln" onClick={applyEml} title="The EML key. One press, written 0. exp(x) − ln(y)" ariaLabel="The EML key. One press, written 0. exp(x) − ln(y)">
              EML
            </KeyButton>
          </div>
          <p className="ti-caption">Every other key is a shortcut that presses these two for you.</p>

          {twoButtons ? null : (
          <div className="ti-block">
          <div className="ti-keys">
            <KeyButton onClick={() => pushScalar(xText, "x")} title="Push the value of x" onReveal={setHeldShortcut}>
              push x
            </KeyButton>
            <KeyButton onClick={() => pushScalar(yText, "y")} title="Push the value of y" onReveal={setHeldShortcut}>
              push y
            </KeyButton>
            <KeyButton onClick={swap} title="Swap the top two values" onReveal={setHeldShortcut}>
              swap
            </KeyButton>
            <KeyButton onClick={drop} title="Drop the top value" onReveal={setHeldShortcut}>
              drop
            </KeyButton>
          </div>

          <form
            className="ti-form"
            onSubmit={(event) => {
              event.preventDefault();
              compute(expr);
            }}
          >
            <label className="ti-label">
              Expression, compiled into EML
              <input
                value={expr}
                onChange={(event) => setExpr(event.target.value)}
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
            <button type="submit" className="ti-text-btn ti-text-btn-strong">
              Compute
            </button>
          </form>
          <div className="ti-chips">
            {EXAMPLES.map((example) => (
              <button
                key={example.expr}
                type="button"
                onClick={() => compute(example.expr)}
                className="ti-chip"
              >
                {example.label}
              </button>
            ))}
          </div>

          <form
            className="ti-form"
            onSubmit={(event) => {
              event.preventDefault();
              loadProgramText(programField);
            }}
          >
            <label className="ti-label">
              Program number (#110), presses, or a word of 1 and E
              <input
                value={programField}
                onChange={(event) => setProgramField(event.target.value)}
                placeholder="#110, 110, or 11E"
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
            <div className="ti-form-row">
              <button type="button" onClick={() => stepLoaded(-1)} className="ti-text-btn">
                Prev
              </button>
              <button type="submit" className="ti-text-btn ti-text-btn-strong">
                Load
              </button>
              <button type="button" onClick={() => stepLoaded(1)} className="ti-text-btn">
                Next
              </button>
            </div>
          </form>

          <div className="ti-group">
            <h2>Constants from 1</h2>
            <div className="ti-keys">
              {CONSTANT_KEYS.map((key) => (
                <KeyButton
                  key={key.id}
                  onClick={() => pushNode(constantNode(key.id), key.label, key.label)}
                  title={expansions[key.id]}
                  secondary={costs[key.id]}
                  onReveal={setHeldShortcut}
                >
                  {key.label}
                </KeyButton>
              ))}
            </div>
          </div>

          <div className="ti-group">
            <h2>One value</h2>
            <div className="ti-keys">
              {UNARY_KEYS.map((key) => (
                <KeyButton key={key.id} onClick={() => applyUnary(key.id, key.label)} title={expansions[key.id]} secondary={costs[key.id]} onReveal={setHeldShortcut}>
                  {key.label}
                </KeyButton>
              ))}
            </div>
          </div>

          <div className="ti-group">
            <h2>Two values · older x, top y</h2>
            <div className="ti-keys">
              {BINARY_KEYS.map((key) => (
                <KeyButton key={key.id} title={expansions[key.id] ?? key.hint} secondary={costs[key.id]} onClick={() => applyBinary(key.id, key.label)} onReveal={setHeldShortcut}>
                  {key.label}
                </KeyButton>
              ))}
            </div>
          </div>
          </div>
          )}

          <div className="ti-footer">
            <p className="ti-tape">{model.tape.slice(-16).join("  ") || "empty"}</p>
            <div className="ti-actions">
              <button type="button" onClick={undo} className="ti-btn">
                Undo
              </button>
              <button type="button" onClick={clearAll} className="ti-btn">
                Clear
              </button>
            </div>
          </div>
      </div>

      <div className="ti-manual">
        <p>
          eml(x, y) = exp(x) − ln(y). With the constant 1, that single operator builds
          arithmetic, roots, logarithms, and the trigonometric functions. The other keys
          are programs written only in those two.
        </p>
        {twoButtons ? null : <GolfPanel />}

        <details className="ti-fold">
          <summary>Branch, subtraction, and infinity</summary>
          <p>
            Exact mode and float64 use the same cut: on a negative real, the log inside eml has
            argument −π, so the composed ln is the principal logarithm and i is +i. The K 21
            word 111111E1EEEE11E1E1EEE is +iπ on this cut and −iπ under the principal log.
            A nonzero imaginary part, however small, stays off that ray. ln 0 is −∞ and exp(−∞) is 0.
            ∞ − ∞ and 0 · ∞ are indeterminate. The short subtraction equals a − b only while
            the imaginary part of b lies in [−π, π), away from the cut, with a moderate
            real part. A known subtrahend inside the float strip uses unscaled rotSub.
            An unknown or huge subtrahend uses k·rotSub(a/k, b/k), where
            k = 1 + √(b²), built from b for a sum as well, and rotSub is raw(c·raw(u, v), c·raw(v, v)) / c.
            rotSub(a, b) equals a − b when b ≠ 0, given ln 0 = −∞ and the extended
            model where exp(+∞ + iθ) = +∞. b = 0 needs a directed infinity: under that
            phase-free model, sub(5, 0) and add(5, 0) are NaN. A float result at b = 0
            is a fact about the float gates, not part of that identity.
            The log inside that square root has imaginary part in [−π, π], so the root has
            nonnegative real part and k ≠ 0. Another branch of that log need not. A subtrahend
            of 0 stays on those gates: exp(−∞ ± iπ) = −0, exp(+∞ ± iπ) = −∞ because float π is
            an exact half turn, and ln(−∞) and ln(−0) keep imaginary part ±π (−π on the lower
            bank inside eml, +π for the composed ln). The unscaled
            rotation is K 131, with c the K 21 word for +iπ.
            Corless and Jeffrey define the unwinding number in “The unwinding number”, ACM SIGSAM
            Bulletin 30(2):28–35, 1996, doi:10.1145/235699.235705. The rotation is ours, and it
            needs ln 0 = −∞ for almost every input: inside the strip, raw(b, b) is 0 and the next
            multiplication logs that 0. An exponential of a finite number that underflows to 0 or a
            subnormal is marked underflow. A displayed 0 from that underflow says it is not a
            mathematical zero. exp(−∞) from ln 0
            is not underflow. The search that disallows ln 0 does not use this construction.
            Both modes evaluate those gates. The scale keeps the exponential finite past the
            old −71π &lt; Im(b) &lt; 73π strip. A subtrahend with a real part around 1.3×10^154 or
            larger overflows that scale, because b² overflows there, so x − y is
            undefined and flagged out of float range.
            asin of a real greater than 1 is π/2 − i·arcosh(x), and asin of a real less
            than −1 is the odd value. A point just above the arcsin cut has positive imaginary
            part. arccos is π/2 − asin, so arccos(2) is +i·arcosh(2), about +1.317i, matching
            mpmath. arsinh(z) is −i·asin(i·z). Float and exact
            use that one branch. arctan of a pure imaginary iy with |y| &gt; 1 is i·artanh(y)
            on this cut, so arctan(−2i) is −π/2 − (artanh 2)i in both modes. A variable just off the cut is not given a second
            formula: when float and exact disagree, the flag shows the exact value.
            artanh of a real greater than 1 is
            ½ ln|(1+x)/(1−x)| − iπ/2. That matches mpmath atanh. C99 catanh of the
            same real, with a +0 imaginary part, returns +iπ/2.
            1+4i and 7i are inside the strip, so they use the unscaled rotation.
            A variable or a value outside the strip, such as 80π i, carries the scale.
            A proof is in docs/rotsub.md.
          </p>
          <ul className="ti-fold-list">
            {table.minimality.map((row) => (
              <li key={`${row.value}-${row.k}`}>
                {row.value}, K {row.k}: {row.label}. {row.note}.
              </li>
            ))}
          </ul>
        </details>

        <details className="ti-fold">
          <summary>Known float limits</summary>
          <p>
            Exact mode is the default. It evaluates this circuit and the screen says computing
            until that finishes. Cancel stops it. A previous result is not left on screen while
            a new one is computing, or after a cancel, and pressing the circuit runs the same gates.
          </p>
          <p>
            Hardware view shows what the raw 64-bit float gates do. It is not patched toward
            the exact value. One shared rule lifts a tiny add and a tiny subtract, real or complex, by
            the same power of ten, up to 10^307, because those short gates only have about
            10^(−16) of absolute accuracy. When the float disagrees with the exact value of
            the same circuit beyond what float can claim, the float stays on screen and a flag
            says float differs from exact, with the exact value beside it. A float 0 from
            underflow says it is not a mathematical zero.
            Float mode then rounds each component to about twelve digits of the whole number&apos;s
            magnitude and marks a component that changed with ≈. Exact mode prints each
            component on its own. A real part of 2 beside 10^10 i shows as 2.
          </p>
          <p>
            Float can drop a component the gates lost. Exact mode keeps a 2 beside 10^16 i,
            and it keeps the i in 10^300 + i. Exact mode is 120-digit decimal arithmetic,
            raised up to 480 digits when a tiny value would otherwise become 0. It is not
            symbolic. asinh of a variable near ±10^200 is undefined in float and
            flagged. tan(π/2) and tan(3π/2) are labelled near a pole in both modes.
            sin, cos, and tan of a real at least 10^6 are
            flagged because float π cannot reduce them. A long float sum can be off in the
            last digit. An add of unknown magnitude whose result is below about 10^(−8), and
            asinh of an unknown value below about 10^(−12), are flagged low absolute
            precision. A known tiny add or subtraction is scaled by a power of ten inside
            the circuit, up to 10^307. A variable at ±1 is ±π/2 in both modes. A variable just off the cut, with |x| &gt; 1 and |eps/x| ≤ 10^(−15), can still be wrong in float. Those points are not given a second formula, and the flag shows the exact value. Float transcendentals can differ by a few ulps across engines.
            Anything else unfinished is listed in docs/known-limitations.md and does not block this version.
            Rebuilding a circuit from its press string drops the low-precision flag, which
            is stored beside the node. A subtrahend with a real part around 1.3×10^154 or larger overflows the
            scale, so x − y is undefined and flagged out of float range.
          </p>
        </details>

        <details className="ti-fold">
          <summary>How ln is only 1 and EML</summary>
          <p>
            ln x = eml(1, eml(eml(1, x), 1)). On the stack that is the program{" "}
            <span className="ti-tape">1 1 x E 1 E E</span>. Pressing ln runs that program.
            Sine, π, and the rest are longer programs of the same kind. Keys 1 and E work from
            the keyboard; Backspace undoes.
          </p>
        </details>

        <p className="ti-fold">
          Andrzej Odrzywołek,{" "}
          <a href="https://arxiv.org/abs/2603.21852">All elementary functions from a single operator</a>
          . The negative real axis uses the branch that makes this ln the principal logarithm.
        </p>
      </div>
    </main>
  );
}
