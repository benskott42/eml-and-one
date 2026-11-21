"use client";

import Link from "next/link";
import { useCallback, useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { useExactScheduler } from "@/components/calculator/useExactScheduler";
import { EMPTY, type Entry, type Model } from "@/components/calculator/screen";
import { runCutRule } from "@/lib/eml/countCutDebug";
import { choose, pagePill, type CountChoice } from "@/lib/eml/countModel";
import { noteBeside } from "@/lib/eml/recordLabel";
import { PROVEN_MINIMAL, provedMinimal } from "@/lib/eml/statusLabels";
import { exactStatus, floatCertified, type ExactMsg } from "@/lib/eml/countStatus";
import { formatC } from "@/lib/eml/format";
import { type History } from "@/lib/eml/history";
import { evaluateReport, nodeFromRpn } from "@/lib/eml/node";
import { samePrincipal } from "@/lib/eml/principalBranch";
import { readCountHash, rememberCountHash } from "@/components/countMemory";
import "./count.css";

const DOCS = "/counting";
const N_MIN = -50;
const N_MAX = 50;
const N_ERROR = "Enter an integer from −50 to 50.";
const CUT_LINE = "Lower cut, Arg in [−π, π), ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log.";
const NO_GATES = "No gates, so no logarithm is taken; the cut does not apply.";

type Mode = "ln0" | "strict";

function clamp(n: number): number {
  if (!Number.isFinite(n)) return 0;
  return Math.max(-50, Math.min(50, Math.round(n)));
}

const hashListeners = new Set<() => void>();

function notifyHash(): void {
  for (const onStoreChange of hashListeners) onStoreChange();
}

function urlFor(hash: string): string {
  const params = new URLSearchParams(window.location.search);
  params.delete("back");
  const search = params.toString();
  return `${window.location.pathname}${search ? `?${search}` : ""}${hash}`;
}

/** Replace the current entry. Pushing each n would make Back take an extra step. */
function replaceUrl(hash: string): void {
  const next = urlFor(hash);
  const current = `${window.location.pathname}${window.location.search}${window.location.hash}`;
  if (current === next) return;
  window.history.replaceState(window.history.state, "", next);
}

type Parsed = { n: number | null; mode: Mode; error: string | null; raw: string | null };

function parseHash(hash: string): Parsed {
  const mode: Mode = /noln0/.test(hash) ? "strict" : "ln0";
  const match = /(?:^|#|&)n=([^&]*)/.exec(hash);
  if (!match) {
    const bare = hash.replace(/^#/, "");
    if (bare === "") return { n: null, mode, error: null, raw: null };
    return { n: null, mode, error: N_ERROR, raw: bare };
  }
  let token = match[1];
  try {
    token = decodeURIComponent(token);
  } catch {
    /* keep the raw token */
  }
  const normalized = token.replaceAll("−", "-").replace(/^\+/, "");
  if (!/^-?\d+$/.test(normalized)) return { n: null, mode, error: N_ERROR, raw: token };
  const value = Number(normalized);
  if (!Number.isSafeInteger(value) || value < N_MIN || value > N_MAX) return { n: null, mode, error: N_ERROR, raw: token };
  return { n: value, mode, error: null, raw: null };
}

function useLocationHash(): string | null {
  const [hash, setHash] = useState<string | null>(() => (typeof window === "undefined" ? null : window.location.hash));
  useLayoutEffect(() => {
    const read = () => setHash(window.location.hash);
    hashListeners.add(read);
    read();
    window.addEventListener("hashchange", read);
    window.addEventListener("popstate", read);
    return () => {
      hashListeners.delete(read);
      window.removeEventListener("hashchange", read);
      window.removeEventListener("popstate", read);
    };
  }, []);
  return hash;
}

function writeHash(n: number, mode: Mode): void {
  const hash = `#n=${n}${mode === "strict" ? "&noln0" : ""}`;
  replaceUrl(hash);
  rememberCountHash(hash);
  notifyHash();
}

function principalSentence(choice: CountChoice, agrees: boolean): string {
  if (!agrees || choice.K === 1) return "";
  if (choice.source === "family") return "The value is the same on the principal branch (see docs/counting.md).";
  return `The value is the same on the principal branch too${choice.table?.ln0 ? " (with ln 0 = −∞)" : ""}.`;
}

function cutSentence(hits: number): string {
  if (hits === 0) return "No ln of a negative real.";
  return `${hits} gate${hits === 1 ? " takes" : "s take"} ln of a negative real, where the cut decides Arg.`;
}

function Chip({ ch, gap }: { ch: string; gap?: boolean }) {
  return <b className={ch === "E" ? "is-e" : undefined} style={gap ? { marginLeft: 5 } : undefined}>{ch === "E" ? "E" : "1"}</b>;
}

export function CountApp() {
  const hash = useLocationHash();
  const parsed: Parsed = hash === null ? { n: null, mode: "ln0", error: null, raw: null } : parseHash(hash);
  const { n, mode } = parsed;
  const [primary, setPrimary] = useState<"exact" | "float">("exact");
  const [model, setModelState] = useState<Model>(EMPTY);
  const modelRef = useRef<Model>(EMPTY);
  const historyRef = useRef<History<Model>>({ past: [], current: EMPTY });
  const [job, setJob] = useState<{ word: string; watch: number } | null>(null);
  const [draft, setDraft] = useState<{ n: number | null; text: string } | null>(null);
  const [inputError, setInputError] = useState<string | null>(null);
  const [spoken, setSpoken] = useState("");
  const [copyNote, setCopyNote] = useState("");
  const typed = useRef("");
  const editing = draft !== null && draft.n === n;
  const fieldText = editing ? draft.text : parsed.raw ?? (n === null ? "" : String(n));
  const serial = useRef(0);
  const setModel = useCallback((next: Model) => {
    modelRef.current = next;
    setModelState(next);
  }, []);
  useExactScheduler({ modelRef, historyRef, setModel, stack: model.stack });

  const choice = useMemo(() => (n === null ? null : choose(n, mode)), [n, mode]);
  const node = useMemo(() => (choice ? nodeFromRpn(choice.word.split("")) : null), [choice]);
  const floated = useMemo(() => {
    if (!node) return null;
    const report = evaluateReport(node);
    return {
      text: formatC(report.value),
      re: report.value.re,
      im: report.value.im,
      underflowed: report.underflowed,
      overflowed: report.overflowed,
      singular: report.singular,
      touchedLn0: report.touchedLn0,
    };
  }, [node]);
  const agrees = useMemo(() => (choice ? samePrincipal(choice.word) : false), [choice]);

  useEffect(() => {
    if (hash === null) return;
    const returning = new URLSearchParams(window.location.search).get("back") === "1";
    const saved = readCountHash();
    if (returning && saved) {
      replaceUrl(saved);
      if (window.location.hash !== saved) window.location.hash = saved;
      notifyHash();
      return;
    }
    if (hash === "") {
      writeHash(7, "ln0");
      return;
    }
    if (parsed.error || n === null) return;
    const canonical = `#n=${n}${mode === "strict" ? "&noln0" : ""}`;
    if (hash !== canonical) writeHash(n, mode);
    else rememberCountHash(canonical);
  }, [hash, n, mode, parsed.error]);

  useEffect(() => {
    if (!choice || !node) return;
    const word = choice.word;
    const circuit = node;
    const timer = window.setTimeout(() => {
      const live = parseHash(window.location.hash);
      if (live.n === null) return;
      const liveWord = choose(live.n, live.mode).word;
      const watch = ++serial.current;
      const entry: Entry = {
        value: { re: Number.NaN, im: Number.NaN },
        text: "checking…",
        singular: null,
        mode: "exact",
        node: liveWord === word ? circuit : nodeFromRpn(liveWord.split("")),
        caption: "count",
        pendingExact: true,
        watch,
      };
      const next: Model = { stack: [entry], tape: [], note: null, error: null };
      historyRef.current = { past: [], current: next };
      setJob({ word: liveWord, watch });
      setModel(next);
    }, 120);
    return () => window.clearTimeout(timer);
  }, [choice, node, setModel]);

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    if (params.get("debug") !== "cut") return;
    const target = window as Window & { __countCutDebug?: (pairs?: Array<[string, string]>) => Promise<unknown> };
    target.__countCutDebug = (pairs) => runCutRule(pairs);
    return () => {
      delete target.__countCutDebug;
    };
  }, []);

  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      if (event.defaultPrevented || event.metaKey || event.ctrlKey || event.altKey) return;
      const target = event.target;
      const inField = target instanceof Element && Boolean(target.closest("a, button, input, textarea, select"));
      const stepKey = event.key === "ArrowRight" || event.key === "ArrowLeft" || event.key === "ArrowUp" || event.key === "ArrowDown";
      if (!stepKey) return;
      if ((event.key === "ArrowLeft" || event.key === "ArrowRight") && inField) return;
      const inText = target instanceof HTMLTextAreaElement || (target instanceof HTMLInputElement && target.type !== "range");
      if (inText && event.key !== "ArrowUp" && event.key !== "ArrowDown") return;
      if (n === null) return;
      event.preventDefault();
      const next = event.key === "ArrowLeft" || event.key === "ArrowDown" ? n - 1 : n + 1;
      writeHash(clamp(next), mode);
    };
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  }, [n, mode]);

  const row = job ? model.stack.find((item) => item.watch === job.watch) : undefined;
  const settled = Boolean(choice && job && row && !row.pendingExact && job.word === choice.word);
  const failed = Boolean(settled && row && (row.cancelled || row.notice === "couldn't verify" || row.cutHits === undefined));
  const message: ExactMsg | null = settled && row && !failed
    ? {
        text: row.text,
        re: row.value.re,
        im: row.value.im,
        singular: row.singular,
        touchedLn0: row.touchedLn0 === true,
        underflowedExact: row.underflowedExact === true,
        unverified: false,
        cutHits: row.cutHits,
      }
    : null;
  const status = message && n !== null ? exactStatus(message, n) : null;
  const floatOk = message && floated ? floatCertified(floated, message) : false;
  const hits = message?.cutHits ?? 0;
  const principal = message && choice ? principalSentence(choice, agrees) : "";
  const showValue = !choice ? "" : primary === "exact" ? (message?.text ?? "checking…") : (floated?.text ?? "");
  const proved = n !== null && provedMinimal(n, mode);
  const pill = choice ? pagePill(choice) : "";
  const pillClass = !choice ? "known" : choice.n === 1 || !choice.table ? "upper" : proved ? "proven" : "known";
  const basis = choice?.table ? noteBeside(choice.table.note, pill) : "";
  if (message && spoken !== showValue) setSpoken(showValue);

  async function copyText(text: string) {
    try {
      const clip = navigator.clipboard;
      if (!clip?.writeText) throw new Error("clipboard unavailable");
      await clip.writeText(text);
      setCopyNote("Copied");
    } catch {
      setCopyNote("Could not copy");
    }
  }

  function commitText(text: string) {
    const trimmed = text.trim().replaceAll("−", "-").replace(/^\+/, "");
    if (!/^-?\d+$/.test(trimmed)) {
      setInputError(N_ERROR);
      setDraft({ n, text });
      return;
    }
    const value = Number(trimmed);
    if (value < N_MIN || value > N_MAX) {
      setInputError(N_ERROR);
      setDraft({ n, text });
      return;
    }
    setInputError(null);
    setDraft(null);
    writeHash(value, mode);
  }

  const visibleError = parsed.error ?? (editing ? inputError : null);
  const nLabel = parsed.error ? "—" : n === null ? "" : n < 0 ? `−${-n}` : String(n);
  const field = (
    <div className="count-n">
      <label className="count-n-label" htmlFor="n">n, from −50 to 50</label>
      <div className="count-controls">
        <button type="button" className="ti-text-btn" aria-label="n minus 1" disabled={n === null || n <= N_MIN} onClick={() => n !== null && writeHash(clamp(n - 1), mode)}>−</button>
        <input
          id="n"
          type="text"
          inputMode="text"
          autoComplete="off"
          spellCheck={false}
          value={fieldText}
          aria-invalid={visibleError ? true : undefined}
          aria-describedby={visibleError ? "n-error" : undefined}
          onFocus={() => {
            typed.current = fieldText;
          }}
          onChange={(event) => {
            typed.current = event.target.value;
            setDraft({ n, text: event.target.value });
            setInputError(null);
          }}
          onBlur={(event) => commitText(event.target.value)}
          onKeyDown={(event) => {
            if (event.key !== "Enter") return;
            event.preventDefault();
            commitText(typed.current);
          }}
        />
        <button type="button" className="ti-text-btn" aria-label="n plus 1" disabled={n === null || n >= N_MAX} onClick={() => n !== null && writeHash(clamp(n + 1), mode)}>+</button>
      </div>
      {visibleError ? <p className="count-error" id="n-error" role="alert">{visibleError}</p> : null}
    </div>
  );

  if (!choice || !floated || n === null) {
    return (
      <main className="ti-stage">
        <div className="count-layout">
          <section className="ti-device">
            <div className="ti-top">
              <div>
                <h1 className="ti-wordmark">EML and One</h1>
                <p className="ti-model">count to n · words from 1 and EML only</p>
              </div>
              <Link className="ti-home" href="/">Calculator</Link>
            </div>
            <div className="ti-bezel">
              <div className="ti-lcd">
                <div className="ti-lcd-status"><span>count to n</span></div>
                <p className="ti-lcd-caption">n = <span id="nbig">{nLabel}</span></p>
                <p className="ti-lcd-result" id="big"></p>
              </div>
            </div>
            {field}
          </section>
        </div>
      </main>
    );
  }

  return (
    <main className="ti-stage">
      <div className="count-layout">
        <section className="ti-device">
          <div className="ti-top">
            <div>
              <h1 className="ti-wordmark">EML and One</h1>
              <p className="ti-model">count to n · words from 1 and EML only</p>
            </div>
            <Link className="ti-home" href="/">Calculator</Link>
          </div>
          <div className="ti-bezel">
            <div className="ti-lcd">
              <div className="ti-lcd-status">
                <span>count to n</span>
                <span className="count-badge" id="cut">
                  <span className={message && hits > 0 ? "lit" : undefined}>
                    cut ↓<span className="sr-only">{message && hits > 0 ? " (used)" : " (not used)"}</span>
                  </span>
                  <span className={message?.touchedLn0 ? "lit" : undefined}>
                    ln 0 = −∞<span className="sr-only">{message?.touchedLn0 ? " (used)" : " (not used)"}</span>
                  </span>
                </span>
              </div>
              <p className="ti-lcd-caption">n = <span id="nbig">{nLabel}</span></p>
              <p className="ti-lcd-caption" id="kline"><b>K {choice.K}</b> {choice.K === 1 ? "press" : "presses"} · {choice.source === "table" ? "word from the integer table" : choice.familyLabel}</p>
              <p className="ti-lcd-result" id="big">
                {!message ? <span className="count-pending">checking…</span> : showValue}
              </p>
              <p className="sr-only" aria-live="polite" aria-atomic="true">{spoken}</p>
              <div id="chips">
                {message && status ? (
                  primary === "exact" ? (
                    <>
                      {status === "exact" ? <span className="count-chip ok">exact mode · 120 digits</span> : null}
                      {status === "unverified" ? <span className="count-chip no">couldn’t verify</span> : null}
                      {status === "not-certified" ? <span className="count-chip no">≈ not certified</span> : null}
                      <span className="count-note">float (hardware): {floated.text}{floatOk ? "" : " ≈ not certified"}</span>
                    </>
                  ) : (
                    <>
                      <span className="count-chip">float (hardware)</span>
                      {floatOk ? null : <span className="count-chip no">≈ not certified</span>}
                      <span className="count-note">exact mode · 120 digits: {message.text}{status === "exact" ? "" : " (≈ not certified)"}</span>
                    </>
                  )
                ) : failed ? <span className="count-chip no">couldn’t verify</span> : null}
              </div>
              <p className="count-note" id="cutnote">{message ? <>{cutSentence(hits)}{principal ? <> <DocText text={principal} /></> : null}</> : null}</p>
            </div>
          </div>
          <div className="count-actions">
            <button type="button" id="mexact" className="ti-text-btn ti-text-btn-strong" aria-pressed={primary === "exact"} onClick={() => setPrimary("exact")}>exact mode · 120 digits</button>
            <button type="button" id="mfloat" className="ti-text-btn" aria-pressed={primary === "float"} onClick={() => setPrimary("float")}>float (hardware)</button>
          </div>
          {field}
          <input id="slider" className="count-slider" type="range" min={-50} max={50} step={1} aria-label="n from −50 to 50" value={n} onChange={(event) => writeHash(clamp(Number(event.target.value)), mode)} />
          <label className="count-opt">
            <input id="ln0" type="checkbox" checked={mode === "ln0"} onChange={(event) => writeHash(n, event.target.checked ? "ln0" : "strict")} /> allow ln 0 = −∞ (off = only words that avoid ln 0)
          </label>
          <p className="count-conv"><b>Conventions.</b> Lower cut: Arg in [−π, π), so ln of a negative real takes Arg −π (on this cut −iπ becomes +iπ under the principal Log). ln 0 = −∞ when allowed. K counts presses: one per 1, one per E.</p>
        </section>
        <div className="count-rail">
          <section className="count-panel">
            <h2>The count label</h2>
            <div id="label">
              <span className={`count-pill ${pillClass}`}>{pill}</span>
            </div>
            {basis ? <p className="count-src" id="basis">{basis}</p> : null}
            {choice.table && choice.K > 1 ? <p className="count-cutline">{CUT_LINE}</p> : null}
            {choice.K === 1 ? <p className="count-cutline">{NO_GATES}</p> : null}
            {choice.source === "table" && choice.table ? <p className="count-src">The counting-construction word here is K {choice.familyK}; the table word is shorter{choice.table.ln0 ? " and uses ln 0 = −∞" : ""}.</p> : null}
            {choice.table ? <p className="count-src">Source: {choice.table.source}.</p> : null}
          </section>
          <section className="count-panel">
            <h2>Sequence · outline</h2>
            <Outline choice={choice} />
            <p className="count-note">{choice.spans.length ? `${choice.spans.length} × EEE1EE11 highlighted (gold and blue bands alternate)` : "no repeating block in this word"}</p>
          </section>
          <section className="count-panel">
            <h2>Sequence · every press</h2>
            <Flat choice={choice} />
            <p className="sr-only">The full word, one character per press, is in the copy text below.</p>
            <div className="count-actions">
              <button type="button" className="ti-text-btn" onClick={() => void copyText(choice.word)}>Copy as 1 / E</button>
              <button type="button" className="ti-text-btn" onClick={() => void copyText(choice.word.replace(/[1E]/g, (key) => (key === "E" ? "1" : "0")))}>Copy as bits (E = 1, 1 = 0)</button>
            </div>
            {copyNote ? <p className="count-note" id="copy-status">{copyNote}</p> : null}
            <p className="count-copy" id="copytext">{choice.word}</p>
          </section>
          <section className="count-panel">
            <How choice={choice} />
            <p className="count-foot">Values come from the calculator&apos;s exact engine. 0, −1 and 2 are {PROVEN_MINIMAL}; other table lengths are shortest known; every other word is a construction.</p>
            <p className="count-foot">Why a counting construction gives n is in <Link id="docs-link" href={DOCS}>docs/counting.md</Link>.</p>
          </section>
        </div>
      </div>
    </main>
  );
}

function DocText({ text }: { text: string }) {
  const marker = "docs/counting.md";
  const at = text.indexOf(marker);
  if (at < 0) return <>{text}</>;
  return <>{text.slice(0, at)}<Link href={DOCS}>{marker}</Link>{text.slice(at + marker.length)}</>;
}

function Outline({ choice }: { choice: CountChoice }) {
  return (
    <div>
      {choice.chunks.map((chunk) => {
        const longPrefix = chunk.kind === "prefix" && chunk.end - chunk.start > 24;
        return (
          <div className="count-seg" key={`${chunk.kind}-${chunk.start}`}>
            <span>{chunk.label}{chunk.reps ? <span className="count-x">× {chunk.reps}</span> : null}</span>
            <span className="count-chips">
              {chunk.kind === "blocks" ? (
                <>
                  {chips(choice.word, chunk.start, chunk.start + 8)}
                  <span className="count-note">repeated {chunk.reps} time{chunk.reps === 1 ? "" : "s"} (one block = 8 presses = one count step)</span>
                </>
              ) : longPrefix ? (
                <>
                  <Chip ch="1" />
                  <span className="count-note">× {chunk.end - chunk.start}</span>
                </>
              ) : chips(choice.word, chunk.start, chunk.end)}
            </span>
            <span>{chunk.start + 1}–{chunk.end} · {chunk.end - chunk.start}</span>
          </div>
        );
      })}
    </div>
  );
}

function chips(word: string, start: number, end: number) {
  const out = [];
  for (let i = start; i < end; i += 1) out.push(<Chip key={i} ch={word[i] ?? "1"} gap={i > start && (i - start) % 5 === 0} />);
  return out;
}

function Flat({ choice }: { choice: CountChoice }) {
  const blockAt = new Array<number>(choice.word.length).fill(-1);
  choice.spans.forEach(([start, end], index) => {
    for (let i = start; i < end; i += 1) blockAt[i] = index;
  });
  return (
    <div className="count-flat" id="flat" aria-hidden="true">
      {choice.word.split("").map((ch, index) => {
        const band = blockAt[index] ?? -1;
        const paint = band < 0 ? "g" : band % 2 ? "b2" : "b1";
        return (
          <span className="cell" key={index}>
            <small>{index === 0 || (index + 1) % 10 === 0 ? index + 1 : ""}</small>
            <b className={ch === "E" ? "is-e" : undefined}>{ch === "E" ? "E" : "1"}</b>
            <u className={paint} />
          </span>
        );
      })}
    </div>
  );
}

function How({ choice }: { choice: CountChoice }) {
  if (choice.source === "family" && choice.spans.length && choice.n >= 2) {
    return <p className="count-note"><b>How it counts.</b> The prefix pushes {2 * choice.n + 2} ones. Each <b>EEE1EE11</b> block takes L with e<sup>L</sup> = e − k to e<sup>L</sup> = e − (k+1). After {choice.n - 1} block{choice.n === 2 ? "" : "s"}, the tail <b>EE1EE</b> outputs e + 1 − e<sup>L</sup> = {choice.n}.</p>;
  }
  if (choice.source === "family" && choice.spans.length && choice.n <= -1) {
    return <p className="count-note"><b>How it counts.</b> The same block runs {-choice.n} time{choice.n === -1 ? "" : "s"}, taking e<sup>L</sup> from e down to e − {-choice.n}; the tail <b>E1EE</b> outputs e<sup>L</sup> − Log e<sup>e</sup> = −{-choice.n}.</p>;
  }
  if (choice.source === "table") return <p className="count-note"><b>Table word.</b> Shorter than the counting-construction word, so the page shows the table&apos;s word and its status.</p>;
  return null;
}
