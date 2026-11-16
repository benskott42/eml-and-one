"use client";

import { useEffect, useRef, useState, type ReactNode } from "react";
import { ln0Dependence, type GolfHit } from "@/lib/eml/golf";
import { type Node } from "@/lib/eml/node";
import { pressPreviewForNode } from "@/lib/eml/presses";

function clipboardError(err: unknown): string {
  const name = typeof err === "object" && err !== null && "name" in err ? String(err.name) : "";
  if (name === "NotAllowedError" || name === "SecurityError") {
    return "Could not copy. Clipboard permission was denied.";
  }
  return "Could not copy. The clipboard is not available.";
}

export function CopyChip({
  text,
  label,
  ariaLabel,
  title,
  onError,
  copiedLabel = "Copied",
}: {
  text: string;
  label: string;
  ariaLabel: string;
  title?: string;
  onError?: (message: string) => void;
  copiedLabel?: string;
}) {
  const [copied, setCopied] = useState(false);
  useEffect(() => {
    if (!copied) return;
    const timer = window.setTimeout(() => setCopied(false), 2000);
    return () => window.clearTimeout(timer);
  }, [copied]);
  return (
    <button
      type="button"
      className="ti-lcd-btn"
      title={title}
      aria-label={ariaLabel}
      aria-live="polite"
      onClick={() => {
        const clip = window.navigator.clipboard;
        const write = clip?.writeText?.bind(clip);
        if (!write) {
          onError?.("Could not copy. The clipboard is not available.");
          return;
        }
        void write(text).then(() => setCopied(true)).catch((err: unknown) => {
          onError?.(clipboardError(err));
        });
      }}
    >
      {copied ? copiedLabel : label}
    </button>
  );
}

/** The display mark ≈ is not part of the number. A paste should be the digits alone. */
export function displayedCopy(shown: string): { text: string; approximate: boolean } {
  const trimmed = shown.trim();
  const approximate = trimmed.startsWith("≈") || trimmed.endsWith("≈");
  const text = trimmed.replace(/^≈\s*/, "").replace(/\s*≈$/, "");
  return { text, approximate };
}

export function CopyValue({ shown, onError }: { shown: string; onError?: (message: string) => void }) {
  const copy = displayedCopy(shown);
  return (
    <CopyChip
      text={copy.text}
      label="Copy value"
      ariaLabel="Copy displayed value"
      copiedLabel={copy.approximate ? "Copied · ≈ not certified" : "Copied"}
      onError={onError}
    />
  );
}

export function CopyNumber({ text, onError }: { text: string; onError?: (message: string) => void }) {
  return <CopyChip text={text} label="Copy #" ariaLabel="Copy program number" title={text} onError={onError} />;
}

export function PressLine({ node }: { node: Node | null }) {
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
          <CopyChip text={view.full} label="Copy" ariaLabel="Copy press string" />
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
  describedBy,
  disabled = false,
  tone = "plain",
  secondary,
  onReveal,
  hot = false,
}: {
  children: ReactNode;
  onClick: () => void;
  title?: string;
  ariaLabel?: string;
  describedBy?: string;
  disabled?: boolean;
  tone?: "plain" | "one" | "eml";
  secondary?: string;
  onReveal?: (text: string) => void;
  hot?: boolean;
}) {
  const gesture = useRef(0);
  const holdTimer = useRef(0);
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
        aria-describedby={describedBy}
        aria-disabled={disabled || undefined}
        onContextMenu={(event) => {
          if (onReveal) event.preventDefault();
        }}
        onClick={() => {
          onClick();
        }}
        onPointerDown={(event) => {
          if (!title || !onReveal || event.button !== 0) return;
          const button = event.currentTarget;
          const id = (gesture.current += 1);
          let revealed = false;
          window.clearTimeout(holdTimer.current);
          holdTimer.current = window.setTimeout(() => {
            if (gesture.current !== id) return;
            revealed = true;
            onReveal(title);
          }, 450);
          const end = (endEvent: PointerEvent) => {
            window.clearTimeout(holdTimer.current);
            if (gesture.current !== id || !revealed || endEvent.type === "pointercancel") return;
            const rect = button.getBoundingClientRect();
            const inside = endEvent.clientX >= rect.left && endEvent.clientX <= rect.right && endEvent.clientY >= rect.top && endEvent.clientY <= rect.bottom;
            if (!inside) return;
            // The touch click is synthesized after pointerup. Stop that one
            // click so a long-press shows the hint and does not press the key.
            button.addEventListener("click", (clickEvent) => {
              clickEvent.preventDefault();
              clickEvent.stopPropagation();
            }, { capture: true, once: true });
          };
          window.addEventListener("pointerup", end, { once: true });
          window.addEventListener("pointercancel", end, { once: true });
        }}
        className={`${disabled ? `ti-btn ti-btn-${tone} is-quiet` : `ti-btn ti-btn-${tone}`}${hot ? " is-tutorial" : ""}`}
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
    const worker = new Worker(new URL("../../lib/eml/golf.worker.ts", import.meta.url));
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
