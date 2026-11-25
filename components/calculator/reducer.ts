import { commitHistory, exactScreen, type History } from "@/lib/eml/history";
import { EMPTY, type Entry, type Model, noteFor, resultError } from "@/components/calculator/entry";

export type CalcState = {
  history: History<Model>;
  model: Model;
  /** True while an async submit, mode switch, undo, or float program load is in flight. */
  busy: boolean;
};

export const INITIAL_CALC_STATE: CalcState = {
  history: { past: [], current: EMPTY },
  model: EMPTY,
  busy: false,
};

export type CalcAction =
  | { type: "COMMIT"; next: Model }
  | { type: "SET_ERROR"; error: string | null }
  | { type: "SET_BUSY"; busy: boolean }
  | { type: "BEGIN_PENDING"; note: string; markPendingExact?: boolean }
  | { type: "FINISH_SUBMIT"; item: Entry; tapeLabel: string }
  | { type: "FAIL_PENDING"; pendingNote: string; fallbackNote: string | null; fallbackError?: string | null; error: string }
  | {
      type: "FINISH_SHOW_PROGRAM";
      item: Entry;
      caption: string;
      replace: boolean;
      pendingNote: string;
      fallbackNote: string | null;
      fallbackError: string | null;
    }
  | { type: "FINISH_MODE_SWITCH"; snapshotLen: number; appliedStack: Entry[]; error: string | null }
  | { type: "FINISH_UNDO"; nextHistory: History<Model>; appliedStack: Entry[]; error: string | null }
  | { type: "PUBLISH_WATCH"; watch: number; next: Entry }
  | { type: "CANCEL_EXACT" };

/**
 * Pure state reducer for the calculator model, undo history, and busy flag.
 * Async handlers (submit, mode switch, undo, float program load, exact worker
 * replies) deliver their results as actions so they always merge against the
 * latest state rather than overwriting it with a stale snapshot.
 */
export function calcReducer(state: CalcState, action: CalcAction): CalcState {
  switch (action.type) {
    case "COMMIT": {
      const history = commitHistory(state.history, action.next);
      return { history, model: action.next, busy: false };
    }
    case "SET_ERROR": {
      const model = { ...state.model, error: action.error };
      return { ...state, model };
    }
    case "SET_BUSY": {
      if (state.busy === action.busy) return state;
      return { ...state, busy: action.busy };
    }
    case "BEGIN_PENDING": {
      const current = state.model;
      const stack = action.markPendingExact
        ? current.stack.map((item) => ({
            ...item,
            text: "computing",
            pendingExact: true,
            value: { re: Number.NaN, im: Number.NaN },
          }))
        : current.stack;
      const model: Model = { ...current, stack, note: action.note, error: null };
      return { ...state, model, busy: true };
    }
    case "FINISH_SUBMIT": {
      const latest = state.model;
      const note = noteFor(action.item);
      const next: Model = {
        stack: [...latest.stack, action.item],
        tape: [...latest.tape, action.tapeLabel],
        note,
        error: resultError(action.item),
      };
      const history = commitHistory(state.history, next);
      return { history, model: next, busy: false };
    }
    case "FAIL_PENDING": {
      const latest = state.model;
      const model: Model = {
        ...latest,
        note: latest.note === action.pendingNote ? action.fallbackNote : latest.note,
        error: action.error,
      };
      return { ...state, model, busy: false };
    }
    case "FINISH_SHOW_PROGRAM": {
      const latest = state.model;
      const base: Model = {
        ...latest,
        note: latest.note === action.pendingNote ? action.fallbackNote : latest.note,
        error: latest.error ?? action.fallbackError,
      };
      const rest = action.replace && base.stack.length > 0 ? base.stack.slice(0, -1) : base.stack;
      const next: Model = {
        stack: [...rest, action.item],
        tape: [...base.tape, action.caption],
        note: noteFor(action.item),
        error: resultError(action.item),
      };
      const history = commitHistory({ ...state.history, current: base }, next);
      return { history, model: next, busy: false };
    }
    case "FINISH_MODE_SWITCH": {
      const current = state.model;
      const shown = [...action.appliedStack, ...current.stack.slice(action.snapshotLen)];
      const top = shown[shown.length - 1];
      const next: Model = {
        ...current,
        stack: shown,
        note: action.error ? null : top ? noteFor(top) : null,
        error: action.error ?? (top ? resultError(top) : null),
      };
      return { history: { ...state.history, current: next }, model: next, busy: false };
    }
    case "FINISH_UNDO": {
      const previous = action.nextHistory.current;
      const top = action.appliedStack[action.appliedStack.length - 1];
      const restored: Model = {
        ...previous,
        // A fresh tape, so a long-press caption read on that earlier screen does not come back.
        tape: previous.tape.slice(),
        stack: action.appliedStack,
        note: action.error ? null : top ? noteFor(top) : previous.note,
        error: action.error ?? (top ? resultError(top) : null),
      };
      return { history: { ...action.nextHistory, current: restored }, model: restored, busy: false };
    }
    case "PUBLISH_WATCH": {
      // Do not overwrite an in-flight mode switch / submit rebuild with a stale reply from the prior mode.
      if (state.busy) return state;
      const current = state.model;
      if (!current.stack.some((row) => row.watch === action.watch)) return state;
      const stack = current.stack.map((row) => (row.watch === action.watch ? action.next : row));
      const top = stack[stack.length - 1];
      const updated: Model = {
        ...current,
        stack,
        note: top?.watch === action.watch ? noteFor(action.next) : current.note,
        // "Swap needs two values." pressed while the top computed stays up.
        error: top?.watch === action.watch ? (resultError(action.next) ?? current.error) : current.error,
      };
      return { ...state, history: { ...state.history, current: updated }, model: updated };
    }
    case "CANCEL_EXACT": {
      const blank = exactScreen("cancelled");
      const stack = state.model.stack.map((item) =>
        item.pendingExact
          ? { ...item, pendingExact: false, cancelled: true, text: blank.text, value: { re: Number.NaN, im: Number.NaN } }
          : item,
      );
      const top = stack[stack.length - 1];
      const updated: Model = {
        ...state.model,
        stack,
        note: top?.cancelled ? blank.note : state.model.note,
        error: null,
      };
      return { ...state, history: { ...state.history, current: updated }, model: updated };
    }
  }
}
