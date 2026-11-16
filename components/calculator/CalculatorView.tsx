"use client";

import Link from "next/link";
import { captionName } from "@/lib/eml/format";
import { FLOAT_DIFFERS } from "@/lib/eml/history";
import { BINARY_KEYS, CONSTANT_KEYS, UNARY_KEYS, constantNode } from "@/lib/eml/library";
import table from "@/lib/eml/best-known.json";
import { programIndexDigits } from "@/lib/eml/programIndex";
import { recordLine } from "@/lib/eml/recordLabel";
import { CopyNumber, GolfPanel, KeyButton, PressLine } from "./chrome";
import { shownSingular } from "./screen";
import type { CalculatorModel } from "./useCalculatorModel";

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
    mode, twoButtons, heldShortcut, setHeldShortcut, costs, expansions, writeTwoButtons,
    requestMode, cancelExact, pushOne, pushNode, pushScalar, applyEml, applyUnary, applyBinary,
    compute, swap, drop, undo, clearAll, loadProgramText, stepLoaded,
  } = props;
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
          <Link className="ti-home" href="/count">Count to n</Link>
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
                id="expr"
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
                {row.value}, K {row.k}: {recordLine(row)}
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
