"use client";

import { useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import { ln0Dependence, type GolfHit } from "@/lib/eml/golf";
import { type Node } from "@/lib/eml/node";
import { pressPreviewForNode } from "@/lib/eml/presses";

export function CopyNumber({ text }: { text: string }) {
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
        <span>E = 1, the 1 key = 0. Within one length, a higher program number is a higher binary value. The program ID is these bits with a 1 in front.</span>
        {view.usesVariables ? <span>x and y stay in the string</span> : null}
        {view.copyable ? (
          <button
            type="button"
            className="ti-lcd-btn"
            onClick={() => {
              void navigator.clipboard.writeText(view.full).then(() => setCopied(true)).catch(() => undefined);
            }}
          >
            {copied ? "Copied bits" : "Copy bits"}
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
