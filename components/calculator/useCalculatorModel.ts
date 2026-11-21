"use client";

import { useCallback, useEffect, useMemo, useRef, useState, useSyncExternalStore } from "react";
import { type C } from "@/lib/eml/complex";
import { recognize } from "@/lib/eml/format";
import { applyModeSwitch, commitHistory, drainQueue, modeRequest, undoHistory, type History } from "@/lib/eml/history";
import {
  BINARY_KEYS,
  CONSTANT_KEYS,
  UNARY_KEYS,
  applyBinaryNode,
  applyUnaryNode,
  binaryNode,
  constantNode,
  integerNode,
  unaryNode,
} from "@/lib/eml/library";
import { E, ONE, type Node, circuitStats, evaluateReport, nodeFromRpn } from "@/lib/eml/node";
import { compileExpression } from "@/lib/eml/parse";
import { parseProgramInput, rankProgram, stepProgram, unnumberedReason, unrankProgram } from "@/lib/eml/programIndex";
import {
  EMPTY,
  binaryCaption,
  clip,
  entry,
  failure,
  noteFor,
  readScalar,
  resultError,
  shortcutTitle,
  unaryCaption,
  valuesOf,
  type Entry,
  type Mode,
  type Model,
} from "./screen";
import { readTwoButtons, subscribeTwoButtons, writeTwoButtons } from "./twoButtons";
import { readCalculatorSession, writeCalculatorSession } from "./calculatorSession";
import { useExactScheduler } from "./useExactScheduler";

type Live = {
  pushNode: (node: Node, caption: string, tapeLabel: string) => void;
  pushOne: () => void;
  pushScalar: (text: string, tapeLabel: string) => void;
  applyEml: () => void;
  applyUnary: (id: string, label: string) => void;
  applyBinary: (id: string, label: string) => void;
  compute: (source: string) => void;
  swap: () => void;
  drop: () => void;
  requestMode: (next: Mode) => void;
  undo: () => void;
  clearAll: () => void;
  showProgram: (node: Node, caption: string, replace: boolean, notice?: string | null) => void;
  stepLoaded: (delta: 1 | -1) => void;
};

export function useCalculatorModel() {
  const remembered = readCalculatorSession();
  const [model, setModel] = useState<Model>(remembered?.model ?? EMPTY);
  const [xText, setXText] = useState(remembered?.xText ?? "0.5");
  const [yText, setYText] = useState(remembered?.yText ?? "2");
  const [expr, setExpr] = useState(remembered?.expr ?? "sin(pi/6)");
  const [programField, setProgramField] = useState(remembered?.programField ?? "");
  const [mode, setMode] = useState<Mode>(remembered?.mode ?? "exact");
  const twoButtons = useSyncExternalStore(subscribeTwoButtons, readTwoButtons, () => false);
  const [heldShortcut, setHeldShortcut] = useState<string | null>(null);
  const modelRef = useRef(model);
  const textRef = useRef({ xText, yText });
  const modeRef = useRef<Mode>(remembered?.mode ?? "exact");
  const historyRef = useRef<History<Model>>(remembered?.history ?? { past: [], current: remembered?.model ?? EMPTY });
  const recomputeRef = useRef(false);
  const queueRef = useRef<Array<() => void>>([]);
  const jobRef = useRef(0);
  const twoButtonsRef = useRef(false);
  const live = useRef<Live>({
    pushNode: () => {},
    pushOne: () => {},
    pushScalar: () => {},
    applyEml: () => {},
    applyUnary: () => {},
    applyBinary: () => {},
    compute: () => {},
    swap: () => {},
    drop: () => {},
    requestMode: () => {},
    undo: () => {},
    clearAll: () => {},
    showProgram: () => {},
    stepLoaded: () => {},
  });
  useEffect(() => {
    twoButtonsRef.current = twoButtons;
    modelRef.current = model;
    textRef.current = { xText, yText };
    modeRef.current = mode;
    writeCalculatorSession({ model, xText, yText, expr, programField, mode, history: historyRef.current });
  });

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

  const { cancel: cancelExact } = useExactScheduler({ modelRef, historyRef, setModel, stack: model.stack });

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
        queueRef.current.push(() => live.current.pushNode(node, caption, tapeLabel));
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
      queueRef.current.push(() => live.current.pushOne());
      return;
    }
    pushNode(ONE, "1", "1");
  }, [pushNode]);

  const pushScalar = useCallback(
    (text: string, tapeLabel: string) => {
      if (recomputeRef.current) {
        queueRef.current.push(() => live.current.pushScalar(text, tapeLabel));
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
      queueRef.current.push(() => live.current.applyEml());
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

  const fail = useCallback((error: string) => {
    const next = { ...modelRef.current, error };
    modelRef.current = next;
    setModel(next);
  }, []);

  const applyUnary = useCallback((id: string, label: string) => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.applyUnary(id, label));
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
  }, [commit, fail]);

  const applyBinary = useCallback((id: string, label: string) => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.applyBinary(id, label));
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
  }, [commit, fail]);

  const compute = useCallback((source: string) => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.compute(source));
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
  }, [commit, fail]);

  const swap = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.swap());
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
  }, [commit, fail]);

  const drop = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.drop());
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
  }, [commit, fail]);

  const requestMode = useCallback((next: Mode) => {
    const step = modeRequest(modeRef.current, next, recomputeRef.current);
    if (step.queue) {
      queueRef.current.push(() => live.current.requestMode(next));
      return;
    }
    if (step.current === modeRef.current) return;
    modeRef.current = step.current;
    setMode(step.current);
  }, []);

  const undo = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.undo());
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

  const clearAll = useCallback(() => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.clearAll());
      return;
    }
    setExpr("");
    commit(EMPTY);
  }, [commit]);

  const showProgram = useCallback((node: Node, caption: string, replace: boolean, notice?: string | null) => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.showProgram(node, caption, replace, notice));
      return;
    }
    const job = (jobRef.current += 1);
    const previous = modelRef.current;
    const modeNow = modeRef.current;
    if (modeNow === "exact") {
      const item = { ...entry(node, caption, modeNow), notice };
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
        const item = entry(node, caption, modeNow);
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
  }, []);

  const loadProgramText = useCallback((source: string) => {
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
  }, [fail, showProgram]);

  /** Load a word of 1 and E (from the Program ID panel). Replaces the top when it was a loaded program. */
  const loadWord = useCallback((word: string, caption: string, replace: boolean) => {
    try {
      showProgram(nodeFromRpn(word.split("")), caption, replace);
    } catch (err) {
      fail(failure(err));
    }
  }, [fail, showProgram]);

  const stepLoaded = useCallback((delta: 1 | -1) => {
    if (recomputeRef.current) {
      queueRef.current.push(() => live.current.stepLoaded(delta));
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
  }, [fail, showProgram]);

  useEffect(() => {
    live.current = {
      pushNode,
      pushOne,
      pushScalar,
      applyEml,
      applyUnary,
      applyBinary,
      compute,
      swap,
      drop,
      requestMode,
      undo,
      clearAll,
      showProgram,
      stepLoaded,
    };
  });

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

  return {
    model,
    xText,
    setXText,
    yText,
    setYText,
    expr,
    setExpr,
    programField,
    setProgramField,
    mode,
    twoButtons,
    heldShortcut,
    setHeldShortcut,
    costs,
    expansions,
    writeTwoButtons,
    requestMode,
    cancelExact,
    pushOne,
    pushNode,
    pushScalar,
    applyEml,
    applyUnary,
    applyBinary,
    compute,
    swap,
    drop,
    undo,
    clearAll,
    loadProgramText,
    stepLoaded,
    loadWord,
  };
}

export type CalculatorModel = ReturnType<typeof useCalculatorModel>;
