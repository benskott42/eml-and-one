// Small pieces of the calculator screen that keep their own state.
import { useEffect, useMemo, useRef, useState, useSyncExternalStore, type ReactNode } from "react";
import { binaryProgramInfo, binaryTreeMetrics, rpnToBinary } from "@/lib/eml/binary";
import { formatC } from "@/lib/eml/format";
import type { GolfHit, NearestHit } from "@/lib/eml/golf";
import { ln0Dependence } from "@/lib/eml/golf-label";
import { type Node } from "@/lib/eml/node";
import { pressPreviewForNode } from "@/lib/eml/presses";

export function CopyNumber({ text }: { text: string }) {
  const [copied, setCopied] = useState(false);
  return (
    <button
      type="button"
      className="ti-lcd-btn"
      title={text}
      aria-label="Copy program number"
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

export function PressLine({ node }: { node: Node | null }) {
  const [copied, setCopied] = useState(false);
  const [copiedHex, setCopiedHex] = useState(false);
  const view = useMemo(() => (node ? pressPreviewForNode(node) : null), [node]);
  const binInfo = useMemo(
    () => (view && !view.usesVariables && view.copyable ? binaryProgramInfo(view.full) : null),
    [view],
  );
  const metrics = useMemo(() => {
    if (!binInfo || !view) return null;
    try {
      return binaryTreeMetrics(view.full);
    } catch {
      return null;
    }
  }, [binInfo, view]);
  if (!node) return null;
  if (!view) {
    return <p className="ti-press">Binary applies only to programs of the 1 and EML keys.</p>;
  }
  return (
    <div>
      <p className="ti-press">
        {pressWord(view.preview)} ({view.presses.toString()} presses)
      </p>
      <div className="ti-press-meta">
        <span>1 is the 1 key and E is the EML key. In binary, 1 is 1 and E is 0, so within one length a higher program number is a lower binary value.</span>
        {binInfo ? (
          <span>
            Binary: 0b{view.preview} · {binInfo.hex}
            {binInfo.decimal ? ` (${binInfo.decimal})` : ""}
            {metrics ? ` · max stack ${metrics.maxStack}` : ""}
          </span>
        ) : null}
        {view.usesVariables ? <span>x and y stay in the string</span> : null}
        {binInfo ? (
          <button
            type="button"
            className="ti-lcd-btn"
            aria-label="Copy hex value"
            onClick={() => {
              const clip = navigator.clipboard;
              if (!clip) return;
              void clip.writeText(binInfo.hex).then(() => setCopiedHex(true)).catch(() => undefined);
            }}
          >
            {copiedHex ? "Copied hex" : "Copy hex"}
          </button>
        ) : null}
        {view.copyable ? (
          <button
            type="button"
            className="ti-lcd-btn"
            aria-label="Copy word"
            onClick={() => {
              // No clipboard outside a secure context; that must not throw.
              const clip = navigator.clipboard;
              if (!clip) return;
              void clip.writeText(pressWord(view.full)).then(() => setCopied(true)).catch(() => undefined);
            }}
          >
            {copied ? "Copied" : "Copy"}
          </button>
        ) : null}
      </div>
    </div>
  );
}

/** Press bits as the key word: 0 is the EML key, written E. x and y stay. */
function pressWord(bits: string): string {
  return bits.replace(/0/g, "E");
}

function golfLabel(id: string): string {
  if (id === "ipi") return "+iπ";
  if (id === "-ipi") return "−iπ";
  return id;
}

export function KeyButton({
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
  const cleanupRef = useRef<(() => void) | null>(null);
  useEffect(() => () => cleanupRef.current?.(), []);
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
        onPointerDown={(event) => {
          if (!title || !onReveal) return;
          // Ignore secondary mouse buttons (e.g. right-click) and non-primary touches.
          if (event.isPrimary === false || (event.button !== undefined && event.button !== 0)) return;
          cleanupRef.current?.();
          revealed.current = false;
          const timer = window.setTimeout(() => {
            revealed.current = true;
            onReveal(title);
          }, 450);
          let resetTimer = 0;
          const detach = () => {
            window.clearTimeout(timer);
            window.clearTimeout(resetTimer);
            window.removeEventListener("pointerup", end);
            window.removeEventListener("pointercancel", end);
            cleanupRef.current = null;
          };
          const end = () => {
            detach();
            if (!revealed.current) return;
            // pointerup outside the button does not deliver a click, so the
            // flag would swallow the next key. Drop it on the next turn if
            // this click does not consume it first.
            resetTimer = window.setTimeout(() => {
              revealed.current = false;
            }, 0);
          };
          cleanupRef.current = detach;
          window.addEventListener("pointerup", end);
          window.addEventListener("pointercancel", end);
        }}
        onPointerLeave={() => {
          if (!revealed.current) cleanupRef.current?.();
        }}
        className={disabled ? `ti-btn ti-btn-${tone} is-quiet` : `ti-btn ti-btn-${tone}`}
      >
        {children}
      </button>
    </div>
  );
}

function parseTargetInput(raw: string): { re: number; im: number } | null {
  const s = raw.trim().replace(/\s+/g, "").replace(/−/g, "-").toLowerCase();
  if (!s) return null;
  if (s === "pi" || s === "π") return { re: Math.PI, im: 0 };
  if (s === "-pi" || s === "-π") return { re: -Math.PI, im: 0 };
  if (s === "e") return { re: Math.E, im: 0 };
  if (s === "phi" || s === "φ") return { re: (1 + Math.sqrt(5)) / 2, im: 0 };
  if (s === "i" || s === "+i") return { re: 0, im: 1 };
  if (s === "-i") return { re: 0, im: -1 };
  // Simple real fraction a/b (e.g. 1/3, -2/5, 22/7)
  const frac = /^([+-]?\d+)\/([+-]?\d+)$/.exec(s);
  if (frac) {
    const num = Number(frac[1]);
    const den = Number(frac[2]);
    if (Number.isFinite(num) && Number.isFinite(den) && den !== 0) {
      return { re: num / den, im: 0 };
    }
    return null;
  }
  // Pure real number
  if (!s.includes("i")) {
    const re = Number(s);
    return Number.isFinite(re) ? { re, im: 0 } : null;
  }
  // Pure imaginary (e.g. 2.5i, -3i, 1e-2i)
  const pureIm = /^([+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?)i$/.exec(s);
  if (pureIm) {
    const im = Number(pureIm[1]);
    return Number.isFinite(im) ? { re: 0, im } : null;
  }
  // Complex a+bi or a-bi
  const complex = /^([+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?)([+-](?:(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?)?)i$/.exec(s);
  if (complex) {
    const re = Number(complex[1]);
    const imPart = complex[2];
    const im = imPart === "+" ? 1 : imPart === "-" ? -1 : Number(imPart);
    return Number.isFinite(re) && Number.isFinite(im) ? { re, im } : null;
  }
  return null;
}

export function GolfPanel({ onLoadProgram }: { onLoadProgram?: (program: string) => void } = {}) {
  const [line, setLine] = useState("Search constants up to K 21, or find the closest short circuit to any target number.");
  const [hits, setHits] = useState<GolfHit[]>([]);
  const [nearest, setNearest] = useState<NearestHit[]>([]);
  const [targetText, setTargetText] = useState("1.6180339887");
  const [busy, setBusy] = useState(false);
  const workerRef = useRef<Worker | null>(null);
  const requestRef = useRef(0);

  useEffect(() => () => {
    workerRef.current?.terminate();
    workerRef.current = null;
  }, []);

  function stop(cancelled = false) {
    requestRef.current += 1;
    // The search loop does not yield, so a stop message never arrives. Ending the worker is the cancel.
    workerRef.current?.terminate();
    workerRef.current = null;
    setBusy(false);
    if (cancelled) setLine("Search cancelled.");
  }

  function launchWorker(payload: Record<string, unknown>, initialMessage: string) {
    stop(false);
    if (typeof Worker === "undefined") {
      setLine("Web Workers are not available in this browser.");
      return;
    }
    const request = requestRef.current;
    let worker: Worker;
    try {
      worker = new Worker(new URL("../../lib/eml/golf.worker.ts", import.meta.url));
    } catch {
      setLine("The search worker could not be started.");
      return;
    }
    workerRef.current = worker;
    setBusy(true);
    setHits([]);
    setNearest([]);
    setLine(initialMessage);
    worker.onmessage = (
      event: MessageEvent<{
        type: string;
        request?: number;
        k?: number;
        pool?: number;
        hits?: GolfHit[];
        nearest?: NearestHit[];
        message?: string;
      }>,
    ) => {
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
        const list = data.hits ?? [];
        setHits(list);
        const text = list
          .map((hit) => {
            const dependence = ln0Dependence(hit);
            const hex = /^[1E]+$/.test(hit.rpn) ? binaryProgramInfo(rpnToBinary(hit.rpn))?.hex : null;
            return `${golfLabel(hit.id)} = K ${hit.k}${hex ? ` (${hex})` : ""}${dependence ? ` · ${dependence}` : ""}`;
          })
          .join(" · ");
        setLine(text || "No constants in range.");
        setBusy(false);
        worker.terminate();
        if (workerRef.current === worker) workerRef.current = null;
      }
      if (data.type === "done-nearest") {
        const list = data.nearest ?? [];
        setNearest(list);
        setLine(list.length > 0 ? `Closest circuits up to K 19 (click any hit to load):` : "No finite circuits found.");
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
    worker.postMessage({ ...payload, request });
  }

  function start(allowLn0: boolean) {
    launchWorker({ mode: "constants", maxK: 21, allowLn0 }, "Searching…");
  }

  function startNearest() {
    const parsed = parseTargetInput(targetText);
    if (!parsed) {
      setLine("Enter a real or complex number (e.g. 1.6180339887, pi, phi, 0.5772, 1+2i).");
      return;
    }
    launchWorker(
      { mode: "nearest", maxK: 19, targetRe: parsed.re, targetIm: parsed.im, limit: 5, allowLn0: true },
      `Searching closest circuits to ${formatC(parsed)}…`,
    );
  }

  return (
    <details className="ti-fold ti-golf">
      <summary>Circuit golf &amp; target finder</summary>
      <p aria-live="polite">{line}</p>
      {hits.length > 0 && onLoadProgram ? (
        <div className="ti-chips">
          {hits.map((hit) => {
            const hex = /^[1E]+$/.test(hit.rpn) ? binaryProgramInfo(rpnToBinary(hit.rpn))?.hex : null;
            return (
              <button
                key={`${hit.id}-${hit.rpn}`}
                type="button"
                className="ti-chip"
                onClick={() => onLoadProgram(hit.rpn)}
                title={`Load ${hit.rpn}`}
              >
                {golfLabel(hit.id)} · K {hit.k}
                {hex ? ` · ${hex}` : ""}
              </button>
            );
          })}
        </div>
      ) : null}
      {nearest.length > 0 ? (
        <ul className="ti-fold-list">
          {nearest.map((hit) => {
            const hex = /^[1E]+$/.test(hit.rpn) ? binaryProgramInfo(rpnToBinary(hit.rpn))?.hex : null;
            const errLabel = hit.absError < 1e-13 ? "exact" : `err ${hit.absError.toExponential(2)}`;
            return (
              <li key={hit.rpn} className="ti-nearest-row">
                <span>
                  <strong>{formatC({ re: hit.re, im: hit.im })}</strong> · K {hit.k}
                  {hex ? ` (${hex})` : ""} · {errLabel}
                </span>
                {onLoadProgram ? (
                  <button type="button" className="ti-chip" onClick={() => onLoadProgram(hit.rpn)}>
                    Load
                  </button>
                ) : null}
              </li>
            );
          })}
        </ul>
      ) : null}
      <div className="ti-manual-actions">
        <button type="button" onClick={() => start(true)} disabled={busy} className="ti-text-btn ti-text-btn-strong">
          Search with ln 0
        </button>
        <button type="button" onClick={() => start(false)} disabled={busy} className="ti-text-btn">
          Search without ln 0
        </button>
        <button type="button" onClick={() => stop(true)} disabled={!busy} className="ti-text-btn">
          Cancel
        </button>
      </div>
      <form
        className="ti-form"
        onSubmit={(event) => {
          event.preventDefault();
          startNearest();
        }}
      >
        <label className="ti-label">
          Find closest circuit to target (real, complex, pi, phi)
          <input
            value={targetText}
            onChange={(event) => setTargetText(event.target.value)}
            placeholder="1.6180339887, 0.5772, pi, 1+2i"
            className="ti-field"
            spellCheck={false}
            autoComplete="off"
          />
        </label>
        <div className="ti-manual-actions">
          <button type="submit" disabled={busy} className="ti-text-btn ti-text-btn-strong">
            Find closest (K ≤ 19)
          </button>
        </div>
      </form>
    </details>
  );
}

const subscribeNothing = () => () => {};

/**
 * A closed fold. The static page and hydration carry its text, so a reader without
 * scripts has it and crawlers index it. Once React owns the page the text of a closed
 * fold is dropped, and kept after the fold has been opened. Left in, the browser still
 * shapes about 3,000 characters per closed fold when something reads the page (one
 * first layout of 25 ms at 6x CPU throttling), which counts as a long task.
 */
export function Fold({ summary, children }: { summary: string; children: ReactNode }) {
  const hydrated = useSyncExternalStore(subscribeNothing, () => true, () => false);
  const [opened, setOpened] = useState(false);
  const detailsRef = useRef<HTMLDetailsElement>(null);
  useEffect(() => {
    if (detailsRef.current?.open) queueMicrotask(() => setOpened(true));
  }, []);
  return (
    <details
      ref={detailsRef}
      className="ti-fold"
      onToggle={(event) => {
        if ((event.currentTarget as HTMLDetailsElement).open) setOpened(true);
      }}
    >
      <summary>{summary}</summary>
      {hydrated && !opened ? null : children}
    </details>
  );
}
