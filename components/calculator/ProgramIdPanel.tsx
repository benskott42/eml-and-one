"use client";

import { useId, useMemo, useState } from "react";
import { rpnTokens, type Node } from "@/lib/eml/node";
import { isConstantCircuit } from "@/lib/eml/programIndex";
import { MAX_ID_KEYS, idBits, indexOf, isValidWord, jump, nextValid, prevValid, programAt, wordToId, idToWord } from "@/lib/eml/programId";

/** Long numbers are shown as head…tail with their full length; Copy gives every digit. */
function shorten(text: string, unit: string, keep = 24): string {
  if (text.length <= keep * 2 + 8) return text;
  return `${text.slice(0, keep)}…${text.slice(-keep)} (${text.length} ${unit})`;
}

type Current =
  | { kind: "empty" }
  | { kind: "none"; reason: string }
  | { kind: "word"; word: string; bits: string; id: bigint; index: bigint };

function currentOf(node: Node | undefined): Current {
  if (!node) return { kind: "empty" };
  if (!isConstantCircuit(node)) return { kind: "none", reason: "This value uses x, y or a typed number, so it is not a word of 1 and E and has no program ID." };
  const tokens = rpnTokens(node, MAX_ID_KEYS);
  if (!tokens) return { kind: "none", reason: `This word is longer than ${MAX_ID_KEYS} keys, so its ID is not shown.` };
  const word = tokens.join("");
  if (!isValidWord(word)) return { kind: "none", reason: "This value is not a single program." };
  return { kind: "word", word, bits: idBits(word), id: wordToId(word), index: indexOf(word) };
}

function copy(text: string): void {
  void navigator.clipboard?.writeText(text).catch(() => {});
}

export function ProgramIdPanel({
  node,
  loadWord,
}: {
  node: Node | undefined;
  loadWord: (word: string, caption: string, replace: boolean) => void;
}) {
  const uid = useId();
  const current = useMemo(() => currentOf(node), [node]);
  const [mode, setMode] = useState<"program" | "id">("program");
  const [field, setField] = useState("");
  const [error, setError] = useState<string | null>(null);
  const [status, setStatus] = useState<{ text: string; decoded: string | null } | null>(null);

  const isWord = current.kind === "word";
  const prevId = isWord ? prevValid(current.id) : null;
  const canPrev = isWord && prevId !== null;
  const canNext = current.kind !== "none";

  function step(delta: 1 | -1) {
    setError(null);
    setStatus(null);
    try {
      if (current.kind === "empty") {
        if (delta < 0) return;
        loadWord(programAt(BigInt(0)), "ID 2 · #0", false);
        return;
      }
      if (current.kind !== "word") return;
      const target = delta > 0 ? nextValid(current.id) : prevValid(current.id);
      if (target === null) return;
      const word = idToWord(target);
      loadWord(word, `ID ${shorten(target.toString(), "digits", 8)} · #${shorten(indexOf(word).toString(), "digits", 8)}`, true);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
    }
  }

  function submit() {
    const result = jump(field, mode);
    if (!result.ok) {
      setStatus(null);
      setError(result.error);
      return;
    }
    setError(null);
    const idText = shorten(result.id.toString(), "digits", 8);
    const indexText = shorten(result.index.toString(), "digits", 8);
    if (result.snappedFrom !== null) {
      setStatus({
        text: `ID ${shorten(result.snappedFrom.toString(), "digits", 8)} is not a program. Loaded the nearest program instead: ID ${idText}, #${indexText}.`,
        decoded: result.decodedFrom,
      });
    } else {
      setStatus({ text: `Loaded ID ${idText}, #${indexText}.`, decoded: null });
    }
    loadWord(result.word, `ID ${idText} · #${indexText}`, false);
  }

  const fieldId = `${uid}-n`;
  const errorId = `${uid}-err`;
  const hintId = `${uid}-hint`;

  return (
    <section className="ti-pid" aria-labelledby={`${uid}-h`}>
      <h2 id={`${uid}-h`}>Program ID</h2>
      {current.kind === "empty" ? <p className="ti-pid-note">Stack empty. Next loads the first program, #0, which is the word 1.</p> : null}
      {current.kind === "none" ? <p className="ti-pid-note">{current.reason}</p> : null}
      {current.kind === "word" ? (
        <dl className="ti-pid-list">
          <div>
            <dt>Word</dt>
            <dd className="ti-pid-mono">
              {current.word.length > 56 ? `${current.word.slice(0, 24)}…${current.word.slice(-24)}` : current.word}{" "}
              <span className="ti-pid-dim">({current.word.length} {current.word.length === 1 ? "key" : "keys"})</span>
            </dd>
          </div>
          <div>
            <dt>ID bits</dt>
            <dd className="ti-pid-mono">
              <span className="ti-pid-sentinel" title="The leading 1 is a marker, not a key">1</span>
              <span aria-hidden="true">·</span>
              {shorten(current.bits.slice(1), "bits") || <span className="ti-pid-dim">(no keys)</span>}
            </dd>
          </div>
          <div>
            <dt>ID</dt>
            <dd className="ti-pid-mono">{shorten(current.id.toString(), "digits")}</dd>
          </div>
          <div>
            <dt>Program number</dt>
            <dd className="ti-pid-mono">#{shorten(current.index.toString(), "digits")}</dd>
          </div>
        </dl>
      ) : null}
      <p className="ti-pid-note">
        ID bits: a leading 1, then one bit per key in order, E = 1 and the 1 key = 0. Program numbers count only the words
        that are programs, shortest first, from #0.
      </p>
      {current.kind === "word" && (current.bits.length > 56 || current.id.toString().length > 56) ? (
        <div className="ti-form-row">
          <button type="button" className="ti-text-btn" onClick={() => copy(current.bits)}>Copy ID bits</button>
          <button type="button" className="ti-text-btn" onClick={() => copy(current.id.toString())}>Copy ID</button>
        </div>
      ) : null}
      <div className="ti-form-row ti-pid-step">
        <button type="button" className="ti-text-btn" onClick={() => step(-1)} disabled={!canPrev}>
          Previous program
        </button>
        <button type="button" className="ti-text-btn" onClick={() => step(1)} disabled={!canNext}>
          Next program
        </button>
      </div>
      {isWord && !canPrev ? <p className="ti-pid-note">#0 is the first program, so there is no previous one.</p> : null}

      <form
        className="ti-form ti-pid-jump"
        noValidate
        onSubmit={(event) => {
          event.preventDefault();
          submit();
        }}
      >
        <fieldset className="ti-pid-modes">
          <legend>Jump by</legend>
          <label>
            <input type="radio" name={`${uid}-mode`} checked={mode === "program"} onChange={() => { setMode("program"); setError(null); }} />
            Program number #N
          </label>
          <label>
            <input type="radio" name={`${uid}-mode`} checked={mode === "id"} onChange={() => { setMode("id"); setError(null); }} />
            ID N
          </label>
        </fieldset>
        <label className="ti-label" htmlFor={fieldId}>
          {mode === "program" ? "Program number" : "ID"}
        </label>
        <p className="ti-pid-note" id={hintId}>
          {mode === "program"
            ? "Whole number from 0, with or without #. Every number names a program."
            : "Whole number from 1. If that ID is not a program, the nearest program is loaded and named here (the smaller ID on a tie)."}
        </p>
        <div className="ti-pid-row">
          <input
            id={fieldId}
            className="ti-field"
            inputMode="numeric"
            autoComplete="off"
            spellCheck={false}
            value={field}
            placeholder={mode === "program" ? "#1" : "9"}
            aria-invalid={error ? true : undefined}
            aria-describedby={error ? `${hintId} ${errorId}` : hintId}
            onChange={(event) => {
              setField(event.target.value);
              setError(null);
            }}
          />
          <button type="submit" className="ti-text-btn ti-text-btn-strong">Go</button>
        </div>
        {error ? (
          <p className="ti-pid-error" id={errorId} role="alert">
            {error}
          </p>
        ) : null}
        <p className="ti-pid-status" role="status">
          {status ? (
            <>
              {status.text}
              {status.decoded !== null ? (
                <>
                  {" "}
                  It decodes to <span className="ti-pid-mono ti-pid-dim">{status.decoded === "" ? "(empty)" : shorten(status.decoded, "keys")}</span>.
                </>
              ) : null}
            </>
          ) : null}
        </p>
      </form>
    </section>
  );
}
