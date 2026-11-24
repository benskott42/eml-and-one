"use client";

import { useCallback, useEffect, useMemo, useRef, useState, useSyncExternalStore } from "react";
import { type C } from "@/lib/eml/complex";
import { captionName, recognize } from "@/lib/eml/format";
import {
  BINARY_KEYS,
  CONSTANT_KEYS,
  UNARY_KEYS,
  applyBinaryNode,
  applyUnaryNode,
  constantNode,
} from "@/lib/eml/library";
import { E, ONE, type Node, evaluateReport, nodeFromRpn } from "@/lib/eml/node";
import table from "@/lib/eml/best-known.json";
import { FLOAT_DIFFERS, applyModeSwitch, commitHistory, drainQueue, modeRequest, undoHistory, type History } from "@/lib/eml/history";
import { INITIAL_X, INITIAL_Y, type KeyTable, type KeyTables, keyCostEntries, keyCosts, keyExpansions, readScalar } from "@/components/keyTables";
import { parseProgramInput, rankProgram, stepProgram, unnumberedReason, unrankProgram } from "@/lib/eml/programIndex";
import {
  EMPTY,
  type Entry,
  type Mode,
  type Model,
  binaryCaption,
  clip,
  entry,
  failure,
  noteFor,
  programDigits,
  resultError,
  shownSingular,
  unaryCaption,
  valuesOf,
} from "@/components/calculator/entry";
import { readTwoButtons, subscribeTwoButtons, writeTwoButtons } from "@/components/calculator/twoButtons";
import { useExactJobs } from "@/components/calculator/useExactJobs";
import { CopyNumber, GolfPanel, KeyButton, PressLine } from "@/components/calculator/widgets";
import { compileSubmission, nextTurn } from "@/components/submitTurn";

/** False in the static HTML and during hydration, true once React owns the keys. */
const subscribeNothing = () => () => {};

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

export function EmlCalculator({ initialKeys }: { initialKeys?: KeyTables } = {}) {
  const [model, setModel] = useState<Model>(EMPTY);
  const [xText, setXText] = useState(INITIAL_X);
  const [yText, setYText] = useState(INITIAL_Y);
  const [expr, setExpr] = useState("sin(pi/6)");
  const [programField, setProgramField] = useState("");
  const [mode, setMode] = useState<Mode>("exact");
  const twoButtons = useSyncExternalStore(subscribeTwoButtons, readTwoButtons, () => false);
  // Presses on the static HTML before hydration do nothing; tests and scripts wait for data-ready.
  const hydrated = useSyncExternalStore(subscribeNothing, () => true, () => false);
  // A long-press caption belongs to the screen it was read on. The tape changes
  // with every press, undo, and clear, so the caption goes with the next one.
  const [held, setHeld] = useState<{ text: string; tape: string[] } | null>(null);
  const setHeldShortcut = useCallback((text: string) => setHeld({ text, tape: modelRef.current.tape }), []);
  const modelRef = useRef(model);
  const textRef = useRef({ xText, yText });
  const modeRef = useRef<Mode>("exact");
  const historyRef = useRef<History<Model>>({ past: [], current: EMPTY });
  const recomputeRef = useRef(false);
  const queueRef = useRef<Array<() => void>>([]);
  const jobRef = useRef(0);
  const twoButtonsRef = useRef(false);
  twoButtonsRef.current = twoButtons;
  // The first screen uses the tables app/page.tsx built at export time. With an
  // empty stack the captions depend only on the x and y text. Otherwise each
  // caption builds its key's circuit on the stack, about 10 ms in all for a large
  // result, so they are built in slices of a few ms after the result is painted
  // and the old captions stay until the new table is whole.
  const [costs, setCosts] = useState<KeyTable>(() => initialKeys?.costs ?? keyCosts([], INITIAL_X, INITIAL_Y));
  useEffect(() => {
    const atStart = initialKeys && model.stack.length === 0 && xText === INITIAL_X && yText === INITIAL_Y;
    const entries = atStart ? Object.entries(initialKeys.costs)[Symbol.iterator]() : keyCostEntries(model.stack, xText, yText);
    const table: KeyTable = {};
    let handle = 0;
    const slice = () => {
      const until = performance.now() + 8;
      for (;;) {
        const next = entries.next();
        if (next.done) {
          setCosts(table);
          return;
        }
        table[next.value[0]] = next.value[1];
        if (performance.now() >= until) break;
      }
      handle = window.setTimeout(slice, 0);
    };
    slice();
    return () => window.clearTimeout(handle);
  }, [initialKeys, model.stack, xText, yText]);

  // The handlers are the only writers of modelRef and modeRef: each one sets the
  // ref before its setState. Syncing them from an effect let a late passive effect
  // of an earlier render roll the ref back, so 1, 1, EML in one turn could see one
  // operand. textRef follows the inputs during render, so a press right after
  // typing reads the new text.
  textRef.current = { xText, yText };

  const { cancelExact } = useExactJobs({ stack: model.stack, modelRef, historyRef, recomputeRef, queueRef, setModel });


  const expansions = useMemo(() => initialKeys?.expansions ?? keyExpansions(), [initialKeys]);

  // Building the tables also fills the circuit caches in lib/eml. With the
  // tables handed in, that work would land on the first key press, so it runs
  // here once the page is idle. The results are discarded.
  useEffect(() => {
    if (!initialKeys) return;
    const warm = () => {
      try {
        keyCosts([], INITIAL_X, INITIAL_Y);
        keyExpansions();
      } catch {
        // The tables catch their own errors; nothing here is shown.
      }
    };
    if (typeof window.requestIdleCallback === "function") {
      const handle = window.requestIdleCallback(warm, { timeout: 2000 });
      return () => window.cancelIdleCallback(handle);
    }
    const handle = window.setTimeout(warm, 200);
    return () => window.clearTimeout(handle);
  }, [initialKeys]);

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
          stack.push(entry(item.node, item.caption, mode, item.bound));
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
        const node = readScalar(text, tapeLabel === "y" ? "y" : "x");
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
        x = { ...entry(readScalar(rawX, "x"), rawX.trim() || "x", modeRef.current), bound: numbers };
        y = { ...entry(readScalar(rawY, "y"), rawY.trim() || "y", modeRef.current), bound: numbers };
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
      const item = entry(node, caption, modeRef.current, { ...x.bound, ...y.bound });
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
          ...entry(readScalar(raw, "x"), raw.trim() || "x", modeRef.current),
          bound: valuesOf(raw, textRef.current.yText),
        };
        rest = [];
      }
      const node = applyUnaryNode(id, arg.node);
      const caption = clip(unaryCaption(id, label, arg.caption));
      const item = entry(node, caption, modeRef.current, arg.bound);
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
        x = { ...entry(readScalar(rawX, "x"), rawX.trim() || "x", modeRef.current), bound: numbers };
        y = { ...entry(readScalar(rawY, "y"), rawY.trim() || "y", modeRef.current), bound: numbers };
        rest = [];
      } else {
        fail("Push a second value. The older one is x and the top one is y.");
        return;
      }
      const node = applyBinaryNode(id, x.node, y.node);
      const caption = clip(binaryCaption(id, x.caption, y.caption));
      const item = entry(node, caption, modeRef.current, { ...x.bound, ...y.bound });
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
    // The compile runs in the next task (see submitTurn.ts), so the submit's own
    // task stays short. Presses in between queue, as during a recompute.
    const job = (jobRef.current += 1);
    const { xText, yText } = textRef.current;
    recomputeRef.current = true;
    const pending = { ...current, note: "Computing…", error: null };
    modelRef.current = pending;
    setModel(pending);
    nextTurn(() => {
      if (job !== jobRef.current) return;
      try {
        const { node, numbers } = compileSubmission(text, xText, yText);
        const item = { ...entry(node, text, modeRef.current), bound: numbers };
        const bits = [noteFor(item)].filter(Boolean);
        // An exact value for an older row can land between the submit and this
        // turn. It is in modelRef, not in the stack read at the submit.
        const latest = modelRef.current;
        commit({
          stack: [...latest.stack, item],
          tape: [...latest.tape, text],
          note: bits.length ? bits.join(" · ") : null,
          error: resultError(item),
        });
      } catch (err) {
        const latest = modelRef.current;
        const next = { ...latest, note: latest.note === pending.note ? current.note : latest.note, error: failure(err) };
        modelRef.current = next;
        setModel(next);
      }
      recomputeRef.current = false;
      drainQueue(queueRef.current);
    });
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
          built.push(entry(item.node, item.caption, modeNow, item.bound));
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

  function showProgram(node: Node, caption: string, replace: boolean, notice?: string | null, bound?: Record<string, C>) {
    if (recomputeRef.current) {
      queueRef.current.push(() => showProgram(node, caption, replace, notice, bound));
      return;
    }
    const job = (jobRef.current += 1);
    const previous = modelRef.current;
    const mode = modeRef.current;
    if (mode === "exact") {
      const item = { ...entry(node, caption, mode, bound), notice };
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
        const item = entry(node, caption, mode, bound);
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
      // A word of x and y reads the fields as they are now, as push x and push y do.
      const numbers: Record<string, C> = {};
      if (parsed.word.includes("x")) numbers.x = evaluateReport(readScalar(textRef.current.xText, "x")).value;
      if (parsed.word.includes("y")) numbers.y = evaluateReport(readScalar(textRef.current.yText, "y")).value;
      const bound = Object.keys(numbers).length > 0 ? numbers : undefined;
      showProgram(nodeFromRpn(parsed.word.split("")), parsed.word, false, notice, bound);
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
  const fullDigits = top ? programDigits(top.node) : null;
  const fullNumber = fullDigits && fullDigits.length > 16 ? `#${fullDigits}` : null;

  return (
    <main className="ti-stage" data-ready={hydrated ? "1" : undefined}>
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
                {fullNumber ? <CopyNumber key={fullNumber} text={fullNumber} /> : null}
              </div>
            ) : null}
            {model.error ? <p className="ti-lcd-error" role="alert">{model.error}</p> : null}
            <PressLine key={top?.node.id ?? 0} node={top?.node ?? null} />
            {held && held.tape === model.tape ? <p className="ti-lcd-hold">{held.text}</p> : null}
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
              tabIndex={mode === "float" ? 0 : -1}
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
              tabIndex={mode === "exact" ? 0 : -1}
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
          <p className="ti-caption">log(b, x) is log base b of x, as on the log key; log(x) and ln(x) are the natural log.</p>
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
