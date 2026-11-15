/**
 * Calculator history and mode-switch results.
 * The screen updates these synchronously, so a queued Backspace cannot
 * replay a snapshot that a keypress has already replaced.
 */

export type History<T> = { past: T[]; current: T };

export function commitHistory<T>(history: History<T>, next: T, limit = 80): History<T> {
  const past = history.past.length >= limit ? history.past.slice(history.past.length - limit + 1) : history.past.slice();
  past.push(history.current);
  return { past, current: next };
}

export function undoHistory<T>(history: History<T>): History<T> {
  const previous = history.past[history.past.length - 1];
  if (previous === undefined) return history;
  return { past: history.past.slice(0, -1), current: previous };
}

/** Run queued actions. An action may queue more; those wait for the next drain. */
export function drainQueue(queue: Array<() => void>): void {
  const runs = queue.splice(0);
  for (const run of runs) run();
}

/**
 * A mode click while a recompute is running is queued. The caller records the
 * applied mode immediately, so a second click in the same turn is compared
 * with that mode and is not dropped.
 */
export function modeRequest<T extends string>(current: T, next: T, busy: boolean): { current: T; queue: boolean } {
  if (busy) return { current, queue: true };
  if (next === current) return { current, queue: false };
  return { current: next, queue: false };
}

/**
 * A failed switch keeps values that already finished and marks the rest,
 * so an old-mode number is not shown under the new mode.
 */
export const FLOAT_DIFFERS = "float differs from exact";

/**
 * Exact mode never keeps a previous result up. Computing and cancel both
 * replace it. A finished value is the only number the screen may show.
 */
export function exactScreen(phase: "computing" | "cancelled" | "ready", readyText = ""): { text: string; note: string | null } {
  if (phase === "ready") return { text: readyText, note: null };
  if (phase === "cancelled") return { text: "—", note: "cancelled" };
  return { text: "computing", note: "computing" };
}

/**
 * The error line under a result. A node limit already says "couldn't verify",
 * so the finite-number line must not be printed as well.
 */
export function finiteLossMessage(input: {
  usable: boolean;
  notice: string | null | undefined;
  singular: string | null;
  mode: string;
  text: string;
}): string | null {
  if (input.usable) return null;
  if (input.notice === "couldn't verify") return null;
  if (input.singular) return null;
  if (input.mode === "exact" && input.text && !input.text.includes("∞") && input.text !== "undefined") return null;
  return "That left the finite numbers.";
}

export function underflowDisclosure(value: { re: number; im: number }, underflowed: boolean): string | null {
  if (!underflowed) return null;
  const zero = (n: number) => Object.is(n, 0) || Object.is(n, -0);
  if (zero(value.re) && zero(value.im)) return "underflowed to 0; not a mathematical zero";
  return "underflow";
}

export function applyModeSwitch<T>(input: {
  previous: T[];
  recomputed: T[];
  error: string | null;
  fail: (item: T, error: string) => T;
}): { stack: T[]; error: string | null } {
  if (!input.error) return { stack: input.recomputed, error: null };
  const message = input.error;
  const stack = input.previous.map((item, index) => input.recomputed[index] ?? input.fail(item, message));
  return { stack, error: message };
}
