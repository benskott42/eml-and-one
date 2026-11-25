// Small pieces of the calculator screen that keep their own state.
import { useEffect, useMemo, useRef, useState, useSyncExternalStore, type ReactNode } from "react";
import type { GolfHit } from "@/lib/eml/golf";
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
  const view = useMemo(() => (node ? pressPreviewForNode(node) : null), [node]);
  if (!node) return null;
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
            aria-label="Copy press string"
            onClick={() => {
              // No clipboard outside a secure context; that must not throw.
              const clip = navigator.clipboard;
              if (!clip) return;
              void clip.writeText(view.full).then(() => setCopied(true)).catch(() => undefined);
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

export function GolfPanel() {
  const [line, setLine] = useState("Search constants up to K 21. The slow script runs through K 35.");
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

  function start(allowLn0: boolean) {
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
    <details className="ti-fold ti-golf">
      <summary>Circuit golf</summary>
      <p aria-live="polite">{line}</p>
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
