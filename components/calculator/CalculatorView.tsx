"use client";

import { useCallback, useEffect, useState, type KeyboardEvent, type MouseEvent } from "react";
import { captionName } from "@/lib/eml/format";
import { FLOAT_DIFFERS } from "@/lib/eml/history";
import { BINARY_KEYS, CONSTANT_KEYS, UNARY_KEYS, constantNode } from "@/lib/eml/library";
import table from "@/lib/eml/best-known.json";
import { agreementNote } from "@/lib/eml/parse";
import { pressPreviewForNode } from "@/lib/eml/presses";
import { programIndexDigits } from "@/lib/eml/programIndex";
import { CopyChip, CopyNumber, CopyValue, GolfPanel, KeyButton } from "./chrome";
import { SequencePanel } from "./SequencePanel";
import { shownSingular } from "./screen";
import type { CalculatorModel } from "./useCalculatorModel";

/** Keep a real part, its sign, and an imaginary part each on one line. */
function ResultText({ shown }: { shown: string }) {
  const approx = shown.endsWith(" ≈");
  const body = approx ? shown.slice(0, -2) : shown;
  const match = body.match(/^(.*?)(\s+[+\u2212]\s+)(.+)$/);
  const mark = approx ? <span className="ti-lcd-term">≈</span> : null;
  if (!match) {
    return approx ? <>{body} {mark}</> : shown;
  }
  const sign = match[2].trim();
  return (
    <>
      <span className="ti-lcd-term">{match[1]}</span>
      {" "}
      <span className="ti-lcd-term">{sign} {match[3]}</span>
      {approx ? <> {mark}</> : null}
    </>
  );
}

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

export function CalculatorView(props: CalculatorModel) {
  const {
    model, xText, setXText, yText, setYText, expr, setExpr, programField, setProgramField,
    mode, twoButtons, heldShortcut, setHeldShortcut, freeInput, setFreeInput, fieldError, costs, writeTwoButtons,
    requestMode, cancelExact, pushOne, pushNode, pushScalar, applyEml, applyUnary, applyBinary,
    compute, swap, drop, undo, clearAll, loadProgramText, stepLoaded, reportError,
  } = props;
  const buried = model.stack.slice(-4, -1);
  const top = model.stack[model.stack.length - 1];
  const readout = top ? top.text : "Stack empty. Press 1.";
  const named = top && !fieldError && top.text !== "0" && top.text !== "−0" ? captionName(top.text, top.value, top.caption) : null;
  const preview = top ? pressPreviewForNode(top.node) : null;
  const agreement = top && top.notice !== "couldn't verify" ? agreementNote(top.caption, top.value, top.bound ?? {}, top.text) : null;
  const pressCount = preview?.presses.toString();
  const pressLine = pressCount
    ? `${pressCount} ${pressCount === "1" ? "press" : "presses"}${agreement === "same as float math (12 digits)" ? " · same as float math (12 digits)" : ""}`
    : null;
  const onlyOnes = model.stack.every((item) => item.text === "1" || item.caption === "1");
  const lightOne = model.stack.length < 2 && (model.stack.length === 0 || onlyOnes);
  const lightEml = model.stack.length === 2 && onlyOnes;
  const liveX = model.stack.length >= 2 ? model.stack[model.stack.length - 2]?.text ?? null : freeInput ? xText : null;
  const liveY = model.stack.length >= 2 ? model.stack[model.stack.length - 1]?.text ?? null : freeInput ? yText : null;
  const liveTip = (action: string) =>
    liveX !== null && liveY !== null ? `${action} if you press this now, with x = ${liveX} and y = ${liveY}` : action;
  const needsValue = !freeInput && model.stack.length < 1;
  const needsPair = !freeInput && model.stack.length < 2;
  const [showCard, setShowCard] = useState(false);
  const dismissCard = useCallback(() => {
    setShowCard(false);
    try {
      window.localStorage.setItem("eml-onboarding", "1");
    } catch {
      /* the card stays dismissed for this visit */
    }
  }, []);
  useEffect(() => {
    const earlyWindow = window as Window & { __emlLive?: boolean; __emlEarly?: string[] };
    const queued = earlyWindow.__emlEarly ?? [];
    earlyWindow.__emlLive = true;
    earlyWindow.__emlEarly = [];
    if (queued.length > 0) {
      // The presses already happened, before this render. Close the card with them.
      // eslint-disable-next-line react-hooks/set-state-in-effect
      dismissCard();
    }
    for (const key of queued) {
      if (key === "1") pushOne();
      else applyEml();
    }
  }, [applyEml, dismissCard, pushOne]);
  useEffect(() => {
    let open = false;
    try {
      open = window.localStorage.getItem("eml-onboarding") !== "1";
    } catch {
      open = true;
    }
    if (!open) return;
    // Client-only: the server render stays without the card so hydration matches.
    // eslint-disable-next-line react-hooks/set-state-in-effect
    setShowCard(true);
  }, []);
  useEffect(() => {
    if (!showCard) return;
    function onKey(event: globalThis.KeyboardEvent) {
      if (event.key === "Escape") {
        dismissCard();
        return;
      }
      const target = event.target;
      if (target instanceof HTMLElement && target.closest("input, textarea")) return;
      if (event.key === "1" || event.key === "e" || event.key === "E") dismissCard();
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [showCard, dismissCard]);
  function onFirstKey(event: MouseEvent<HTMLDivElement>) {
    if (!showCard) return;
    const target = event.target;
    if (target instanceof HTMLElement && target.closest("button")) dismissCard();
  }
  useEffect(() => {
    if (!heldShortcut) return;
    const timer = window.setTimeout(() => setHeldShortcut(null), 6000);
    return () => window.clearTimeout(timer);
  }, [heldShortcut, setHeldShortcut]);
  useEffect(() => {
    const lcd = document.querySelector(".ti-lcd");
    const result = document.querySelector(".ti-lcd-result");
    if (!(lcd instanceof HTMLElement) || !(result instanceof HTMLElement)) return;
    result.scrollTop = 0;
    const lcdBox = lcd.getBoundingClientRect();
    const resultBox = result.getBoundingClientRect();
    if (resultBox.top < lcdBox.top - 1 || resultBox.top > lcdBox.bottom - 24) {
      lcd.scrollTop += resultBox.top - lcdBox.top;
    }
    const mark = () => {
      const resultMore = result.scrollHeight > result.clientHeight + 1;
      const lcdMore = lcd.scrollHeight > lcd.clientHeight + lcd.scrollTop + 1;
      result.classList.toggle("has-more", resultMore);
      lcd.classList.toggle("has-more", lcdMore);
    };
    mark();
    lcd.addEventListener("scroll", mark);
    result.addEventListener("scroll", mark);
    const observer = typeof ResizeObserver === "undefined" ? null : new ResizeObserver(mark);
    observer?.observe(lcd);
    observer?.observe(result);
    return () => {
      lcd.removeEventListener("scroll", mark);
      result.removeEventListener("scroll", mark);
      observer?.disconnect();
    };
  }, [readout]);
  function onModeKey(event: KeyboardEvent<HTMLButtonElement>) {
    const key = event.key;
    if (key !== "ArrowLeft" && key !== "ArrowRight" && key !== "ArrowUp" && key !== "ArrowDown") return;
    event.preventDefault();
    const nextMode = mode === "exact" ? "float" : "exact";
    requestMode(nextMode);
    const target = event.currentTarget.parentElement?.querySelector<HTMLButtonElement>(`button[data-mode="${nextMode}"]`);
    target?.focus();
  }
  const pendingExact = model.stack.some((item) => item.pendingExact) || model.note === "Computing…" || model.note === "computing";
  const canCopyValue = Boolean(top && !top.pendingExact && top.text !== "—" && top.text !== "computing");
  const fullDigits = top ? programIndexDigits(top.node) : null;
  const fullNumber = fullDigits && fullDigits.length > 16 ? `#${fullDigits}` : null;

  return (
    <main className="ti-stage">
      <a className="ti-skip" href="#expression">Skip to expression</a>
      <div className={twoButtons ? "ti-device ti-device-two" : "ti-device"}>
        {showCard ? (
          <div className="ti-onboard" role="region" aria-label="First visit">
            <p>Try the two keys, or type an expression.</p>
            <div className="ti-onboard-actions">
              <button type="button" className="ti-text-btn" onClick={() => { pushOne(); pushOne(); applyEml(); dismissCard(); }}>Try 1, 1, EML</button>
              <button type="button" className="ti-text-btn" onClick={() => { compute("2*2"); dismissCard(); }}>Try 2*2</button>
              <button type="button" className="ti-text-btn" onClick={dismissCard}>Skip</button>
            </div>
          </div>
        ) : null}
        <div className="ti-top">
          <div>
            <h1 className="ti-wordmark">EML and One</h1>
            <p className="ti-model">a two-button calculator</p>
          </div>
        </div>

        <div className="ti-face">
        <div className="ti-bezel">
          <div className="ti-lcd" role="region" aria-label="Calculator screen">
            <p className="ti-lcd-status">
              <span>{mode === "exact" ? "exact mode · 120 digits" : "float (hardware)"}</span>
            </p>
            <div className="ti-lcd-stack" tabIndex={0} aria-label="Stack history">
              {buried.map((item, index) => (
                <p key={`${item.caption}-${index}`}>
                  <ResultText shown={item.text} />
                  <span className="ti-lcd-sep"> · </span>
                  {item.caption}
                </p>
              ))}
            </div>
            <div className="ti-lcd-pin">
            <div className="ti-lcd-readout">
              <p className={fieldError && top ? "ti-lcd-result is-previous" : "ti-lcd-result"} aria-live="polite" title={readout}>
                <ResultText shown={readout} />
                {fieldError && top ? " previous" : ""}
              </p>
              <div className="ti-lcd-copies">
                {canCopyValue && top ? (
                  <CopyValue key={top.text} shown={top.text} node={top.mode === "exact" ? top.node : null} value={top.mode === "float" ? top.value : null} bound={top.bound} onError={reportError} />
                ) : null}
                {fullNumber ? <CopyNumber key={fullNumber} text={fullNumber} onError={reportError} /> : null}
              </div>
            </div>
            <p className="ti-lcd-caption">
              {top ? (top.caption.length > 80 ? `${preview?.presses.toString() ?? "many"} presses` : top.caption) : "Press 1, then 1, then EML. That is e."}
              {named ? ` · ${named}` : ""}
            </p>
            <p className={model.error ? "ti-lcd-error" : "ti-lcd-error ti-lcd-error-empty"} role="alert">
              {model.error ?? ""}
            </p>
            {heldShortcut ? <p className="ti-lcd-hold">{heldShortcut}</p> : null}
            </div>
            {top?.sequence ? <SequencePanel source={top.sequence} typed={top.caption.length > 80 || /^\d+ presses$/.test(top.caption) ? "a loaded word" : top.caption} result={top.text} /> : null}
            {top?.floatDiffers && top.exactBeside ? <p className="ti-lcd-flag">{FLOAT_DIFFERS} · {top.exactBeside}</p> : null}
            {top && shownSingular(top) ? <p className="ti-lcd-flag">{shownSingular(top)}</p> : null}
            {pressLine ? <p className="ti-press">{pressLine}</p> : null}
            <details className="ti-fold">
              <summary>Details</summary>
              {model.note ? <p className="ti-lcd-note"><span title={fullNumber ?? undefined}>{model.note}</span></p> : null}
              {preview?.full ? <p className="ti-press-meta">bits {preview.full}</p> : null}
              <p className="ti-press-meta">1 = 1 key, 0 = EML. Within one length, a higher program number is a lower binary value, because 1 comes before E. A word over 20,000 presses cannot be copied or loaded again.</p>
              {preview?.copyable ? <CopyChip text={preview.full} label="Copy presses" ariaLabel="Copy press string" onError={reportError} /> : null}
            </details>
          </div>
        </div>
        <div className="ti-pad" onClick={onFirstKey}>

        {twoButtons ? null : (
          <form
            className="ti-form"
            onSubmit={(event) => {
              event.preventDefault();
              compute(expr);
            }}
          >
            <label className="ti-label" htmlFor="expression">
              Expression
              <input
                id="expression"
                value={expr}
                onChange={(event) => setExpr(event.target.value)}
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
            <button type="submit" className="ti-text-btn ti-text-btn-strong" aria-label="Compute">
              =
            </button>
            {fieldError ? <p className="ti-field-error" role="alert">{fieldError}</p> : null}
          </form>
        )}

        <div className="ti-modes">
          <button
            type="button"
            aria-pressed={twoButtons}
            onClick={() => writeTwoButtons(!twoButtons)}
            className={twoButtons ? "ti-btn ti-btn-2nd is-on" : "ti-btn ti-btn-2nd is-off"}
          >
            Two buttons only
            <span className="ti-mode-sub">{twoButtons ? "on" : "off"}</span>
          </button>
          <div role="radiogroup" aria-label="Evaluation" className="ti-radio">
            <button
              type="button"
              role="radio"
              aria-checked={mode === "float"}
              data-mode="float"
              tabIndex={mode === "float" ? 0 : -1}
              onClick={() => requestMode("float")}
              onKeyDown={onModeKey}
              className={mode === "float" ? "ti-btn ti-btn-alpha is-down" : "ti-btn ti-btn-alpha"}
            >
              float (hardware)
            </button>
            <button
              type="button"
              role="radio"
              aria-checked={mode === "exact"}
              data-mode="exact"
              tabIndex={mode === "exact" ? 0 : -1}
              onClick={() => requestMode("exact")}
              onKeyDown={onModeKey}
              className={mode === "exact" ? "ti-btn ti-btn-alpha is-down" : "ti-btn ti-btn-alpha"}
            >
              exact mode · 120 digits
            </button>
          </div>
        </div>
        <div className="ti-compute-slot">
          <button
            type="button"
            className="ti-btn ti-btn-cancel"
            onClick={cancelExact}
            disabled={!model.stack.some((item) => item.pendingExact)}
            aria-hidden={model.stack.some((item) => item.pendingExact) ? undefined : true}
          >
            Cancel
          </button>
          <p className={pendingExact ? "ti-case-note" : "ti-case-note is-idle"}>
            {mode === "exact"
              ? "Exact value of this circuit. Cancel stops it, and the previous number is not restored."
              : "Hardware view: the raw 64-bit float value of these gates. A disagreement is flagged, with the exact value beside it."}
          </p>
        </div>
          {twoButtons || !freeInput ? null : (
          <div className="ti-fields">
            <label className="ti-label">
              x
              <input
                value={xText}
                onChange={(event) => setXText(event.target.value)}
                onKeyDown={(event) => {
                  if (event.key !== "Enter") return;
                  event.preventDefault();
                  pushScalar(xText, "x");
                }}
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
                onKeyDown={(event) => {
                  if (event.key !== "Enter") return;
                  event.preventDefault();
                  pushScalar(yText, "y");
                }}
                className="ti-field"
                spellCheck={false}
                autoComplete="off"
              />
            </label>
          </div>
          )}

          <div className="ti-prime">
            <KeyButton tone="one" secondary="const" hot={lightOne} onClick={pushOne} title="Push the constant 1. This is one press: 1" ariaLabel="1">
              1
            </KeyButton>
            <KeyButton tone="eml" secondary="exp − ln" hot={lightEml} disabled={needsPair} describedBy={needsPair ? "gate-two" : undefined} onClick={applyEml} title={needsPair ? "EML needs two values. Press 1 first." : "EML. exp(x) − ln(y)"} ariaLabel="EML">
              EML
            </KeyButton>
          </div>
          {needsValue ? <p id="gate-one" className="ti-caption">Needs a value. Press 1 first.</p> : null}
          {needsPair ? <p id="gate-two" className="ti-caption">EML needs two values. Press 1 first.</p> : null}
          <p className="ti-caption">Keyboard: 1 · E · Backspace · Enter computes</p>
          {twoButtons ? null : <p className="ti-caption">Every other key is a shortcut that presses these two for you.</p>}

          {twoButtons ? null : (
          <div className="ti-block">
          <details className="ti-fold">
            <summary>Advanced stack</summary>
            <label className="ti-check-row">
              <input className="ti-check" type="checkbox" checked={freeInput} onChange={(event) => setFreeInput(event.target.checked)} />
              free input
            </label>
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
          </details>
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
              Program number (#110), presses, or a word of 1, E, x, and y
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
                  title={key.label}
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
                <KeyButton key={key.id} disabled={needsValue} describedBy={needsValue ? "gate-one" : undefined} onClick={() => applyUnary(key.id, key.label)} title={needsValue ? "Needs a value. Press 1 first." : liveTip(key.label)} secondary={costs[key.id]} onReveal={setHeldShortcut}>
                  {key.label}
                </KeyButton>
              ))}
            </div>
          </div>

          <div className="ti-group">
            <h2>Two values · older x, top y</h2>
            <div className="ti-keys">
              {BINARY_KEYS.map((key) => (
                <KeyButton key={key.id} disabled={needsPair} describedBy={needsPair ? "gate-two" : undefined} title={needsPair ? "EML needs two values. Press 1 first." : liveTip(key.hint)} secondary={costs[key.id]} onClick={() => applyBinary(key.id, key.label)} onReveal={setHeldShortcut}>
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
