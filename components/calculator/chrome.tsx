"use client";

import { useEffect, useRef, useState, type ReactNode } from "react";
import { ln0Dependence, type GolfHit } from "@/lib/eml/golf";
import { type C } from "@/lib/eml/complex";
import { provenInteger, type Node } from "@/lib/eml/node";
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
  prepare,
}: {
  text: string;
  label: string;
  ariaLabel: string;
  title?: string;
  onError?: (message: string) => void;
  copiedLabel?: string;
  prepare?: () => { text: string; copiedLabel?: string };
}) {
  const [copied, setCopied] = useState(false);
  const [note, setNote] = useState(copiedLabel);
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
        const prepared = prepare ? prepare() : { text, copiedLabel };
        void write(prepared.text).then(() => {
          setNote(prepared.copiedLabel ?? copiedLabel);
          setCopied(true);
        }).catch((err: unknown) => {
          onError?.(clipboardError(err));
        });
      }}
    >
      {copied ? note : label}
    </button>
  );
}

/** The display mark ≈ is not part of the number. A paste should be the digits alone. */
export function displayedCopy(shown: string): { text: string; approximate: boolean } {
  const trimmed = shown.trim();
  const approximate = trimmed.startsWith("≈") || trimmed.endsWith("≈");
  const text = machineNumber(trimmed.replace(/^≈\s*/, "").replace(/\s*≈$/, ""));
  return { text, approximate };
}

/** Display text uses ×10^ and a unicode minus. A paste uses e and ASCII '-'. */
function machineNumber(shown: string): string {
  const plain = shown
    // Breaks inserted so a long integer can wrap: zero-width space, word
    // joiner, soft hyphen, and thin or narrow spaces.
    .replace(/[\u00ad\u00a0\u200b\u200c\u200d\u2060\u2009\u200a\u202f\ufeff]/g, "")
    .replaceAll("×10^−", "e-")
    .replaceAll("×10^+", "e")
    .replaceAll("×10^", "e")
    .replaceAll("−", "-")
    .replaceAll("∞", "Infinity");
  return plain.replace(/(\d)\s*([+-])\s*(?=\d|i)/g, "$1$2");
}

/** Shortest round-trip for one float64, with the sign of zero kept. */
function floatPart(n: number): string {
  if (Object.is(n, -0)) return "-0";
  if (n === 0) return "0";
  if (!Number.isFinite(n)) {
    if (Number.isNaN(n)) return "NaN";
    return n > 0 ? "Infinity" : "-Infinity";
  }
  return n.toString().replace("e+", "e");
}

function mantissaDigits(text: string): number {
  const mantissa = text.split(/e/i)[0] ?? text;
  return mantissa.match(/\d/g)?.length ?? 0;
}

/** Real and imaginary pieces actually printed, in machine form. */
function shownParts(text: string): { re?: string; im?: string } {
  if (text === "undefined" || text === "NaN") return { re: "NaN" };
  if (text === "i") return { im: "1" };
  if (text === "-i") return { im: "-1" };
  if (text === "Infinity" || text === "-Infinity") return { re: text };
  const number = String.raw`[+-]?(?:\d+(?:\.\d+)?(?:e[+-]?\d+)?|Infinity|NaN)`;
  const imagOnly = new RegExp(`^(${number})i$`).exec(text);
  if (imagOnly?.[1]) return { im: imagOnly[1] };
  const both = new RegExp(`^(${number})([+-]${number})i$`).exec(text);
  if (both?.[1] && both[2]) return { re: both[1], im: both[2] };
  return { re: text };
}

/**
 * A scientific abbreviation, or a full-width plain decimal, is the raw double
 * printed shorter. A short plain decimal that is a different number, such as
 * 0.5 for sin(pi/6), is the snapped value on the screen.
 */
function copyShownPart(printed: string, raw: number): { text: string; expanded: boolean } {
  if (printed === "NaN" || Number.isNaN(raw)) return { text: "NaN", expanded: false };
  if (printed === "Infinity" || printed === "-Infinity") return { text: printed, expanded: false };
  if (printed === "-0") return { text: "-0", expanded: false };
  if (printed === "0") return { text: "0", expanded: false };
  const parsed = Number(printed);
  if (Number.isFinite(parsed) && parsed === raw) return { text: floatPart(raw), expanded: false };
  const scientific = /e/i.test(printed);
  const digits = mantissaDigits(printed);
  if (scientific || digits >= 12) {
    // A shown ±1×10^k is that power. The gates can be a double a few ulps away.
    if (/^-?1(?:\.0+)?e/i.test(printed)) return { text: printed, expanded: parsed !== raw };
    const text = floatPart(raw);
    return { text, expanded: text !== printed };
  }
  return { text: printed, expanded: false };
}

/**
 * Exact integers held as a bigint copy every digit. Every other exact value
 * copies the screen. A float copies the round-trip of the parts on screen,
 * or the snapped screen text when that is a different short value.
 */
export function copiedValue(input: {
  shown: string;
  node?: Node | null;
  value?: C | null;
  overflowed?: boolean;
}): { text: string; copiedLabel: string } {
  const display = displayedCopy(input.shown);
  if (input.node && input.value == null) {
    if (display.text === "undefined" || display.text === "NaN") return { text: "NaN", copiedLabel: "Copied" };
    const whole = provenInteger(input.node);
    // The carried integer is the exact value, including past the float range.
    if (whole !== undefined) return { text: whole.toString(), copiedLabel: "Copied" };
    const digits = mantissaDigits(display.text);
    const noun = digits === 1 ? "digit" : "digits";
    return { text: display.text, copiedLabel: `Copied as shown (${digits} ${noun})` };
  }
  const value = input.value ?? { re: Number.NaN, im: Number.NaN };
  const parts = shownParts(display.text);
  if ((parts.re === "NaN" || Number.isNaN(value.re) || Number.isNaN(value.im)) && parts.im === undefined) {
    return { text: "NaN", copiedLabel: input.overflowed || display.approximate ? "Copied · ≈ not certified" : "Copied" };
  }
  let expanded = false;
  let text = "";
  if (parts.re !== undefined && parts.im === undefined) {
    const part = copyShownPart(parts.re, value.re);
    text = part.text;
    expanded = part.expanded;
  } else if (parts.im !== undefined && parts.re === undefined) {
    const part = copyShownPart(parts.im, value.im);
    const body = part.text;
    text = body === "1" ? "i" : body === "-1" ? "-i" : `${body}i`;
    expanded = part.expanded;
  } else {
    const re = copyShownPart(parts.re ?? "0", value.re);
    const im = copyShownPart(parts.im ?? "0", value.im);
    const negative = im.text.startsWith("-");
    const abs = im.text.replace(/^-/, "");
    const imag = abs === "1" ? "i" : `${abs}i`;
    text = `${re.text}${negative ? "-" : "+"}${imag}`;
    expanded = re.expanded || im.expanded;
  }
  const uncertified = display.approximate || input.overflowed === true || expanded;
  return { text, copiedLabel: uncertified ? "Copied · ≈ not certified" : "Copied" };
}

export function CopyValue({
  shown,
  node,
  value,
  overflowed,
  onError,
}: {
  shown: string;
  node?: Node | null;
  value?: C | null;
  overflowed?: boolean;
  onError?: (message: string) => void;
}) {
  const prepared = copiedValue({ shown, node, value, overflowed });
  return (
    <CopyChip
      text={prepared.text}
      label="Copy value"
      ariaLabel="Copy displayed value"
      copiedLabel={prepared.copiedLabel}
      prepare={() => copiedValue({ shown, node, value, overflowed })}
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
