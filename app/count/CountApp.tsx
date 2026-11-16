"use client";

import { useCallback, useEffect, useMemo, useRef, useState, useSyncExternalStore } from "react";
import { PressLine } from "@/components/calculator/chrome";
import { useExactScheduler } from "@/components/calculator/useExactScheduler";
import { EMPTY, type Entry, type Model } from "@/components/calculator/screen";
import { runCutRule } from "@/lib/eml/countCutDebug";
import { choose, type CountChoice } from "@/lib/eml/countModel";
import { exactStatus, floatCertified, type ExactMsg } from "@/lib/eml/countStatus";
import { formatC } from "@/lib/eml/format";
import { type History } from "@/lib/eml/history";
import { evaluateReport, nodeFromRpn } from "@/lib/eml/node";
import { samePrincipal } from "@/lib/eml/principalBranch";
import "./count.css";

const DOCS = "https://github.com/benskott42/eml-and-one/blob/cursor/v1.1-count-to-n-f514/docs/counting.md";
const CUT_LINE = "Lower cut, Arg in [−π, π), ln 0 = −∞. On this cut −iπ becomes +iπ under the principal Log.";
const NO_GATES = "No gates, so no logarithm is taken; the cut does not apply.";

type Mode = "ln0" | "strict";

function clamp(n: number): number {
  if (!Number.isFinite(n)) return 0;
  return Math.max(-50, Math.min(50, Math.round(n)));
}

const hashListeners = new Set<() => void>();
let lastPush = -1e9;

function subscribeHash(onStoreChange: () => void): () => void {
  hashListeners.add(onStoreChange);
  window.addEventListener("hashchange", onStoreChange);
  window.addEventListener("popstate", onStoreChange);
  return () => {
    hashListeners.delete(onStoreChange);
    window.removeEventListener("hashchange", onStoreChange);
    window.removeEventListener("popstate", onStoreChange);
  };
}

function notifyHash(): void {
  for (const onStoreChange of hashListeners) onStoreChange();
}

function parseHash(hash: string): { n: number; mode: Mode } {
  const match = /n=(-?\d+)/.exec(hash);
  return { n: clamp(match ? Number(match[1]) : 7), mode: /noln0/.test(hash) ? "strict" : "ln0" };
}

function writeHash(n: number, mode: Mode): void {
  const hash = `#n=${n}${mode === "strict" ? "&noln0" : ""}`;
  if (window.location.hash !== hash) {
    const now = performance.now();
    if (now - lastPush > 800) history.pushState(null, "", hash);
    else history.replaceState(null, "", hash);
    lastPush = now;
  }
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
  const hash = useSyncExternalStore(subscribeHash, () => window.location.hash, () => "");
  const { n, mode } = parseHash(hash);
  const [primary, setPrimary] = useState<"exact" | "float">("exact");
  const [model, setModelState] = useState<Model>(EMPTY);
  const modelRef = useRef<Model>(EMPTY);
  const historyRef = useRef<History<Model>>({ past: [], current: EMPTY });
  const [job, setJob] = useState<{ word: string; watch: number } | null>(null);
  const serial = useRef(0);
  const setModel = useCallback((next: Model) => {
    modelRef.current = next;
    setModelState(next);
  }, []);
  useExactScheduler({ modelRef, historyRef, setModel, stack: model.stack });

  const choice = useMemo(() => choose(n, mode), [n, mode]);
  const node = useMemo(() => nodeFromRpn(choice.word.split("")), [choice.word]);
  const floated = useMemo(() => {
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
  const agrees = useMemo(() => samePrincipal(choice.word), [choice.word]);

  useEffect(() => {
    if (window.location.hash) return;
    writeHash(7, "ln0");
  }, []);

  useEffect(() => {
    const word = choice.word;
    const circuit = node;
    const timer = window.setTimeout(() => {
      const live = parseHash(window.location.hash);
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
  }, [choice.word, node, setModel]);

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
      if (event.defaultPrevented || event.target instanceof HTMLInputElement || event.target instanceof HTMLTextAreaElement) return;
      if (event.key === "ArrowRight") writeHash(clamp(n + 1), mode);
      if (event.key === "ArrowLeft") writeHash(clamp(n - 1), mode);
    };
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  }, [n, mode]);

  const row = job ? model.stack.find((item) => item.watch === job.watch) : undefined;
  const settled = Boolean(job && row && !row.pendingExact && job.word === choice.word);
  const failed = Boolean(settled && row && (row.cancelled || row.notice === "couldn't verify" || row.cutHits === undefined));
  const message: ExactMsg | null = settled && row && !failed
    ? {
        text: row.text,
        re: row.value.re,
        im: row.value.im,
        singular: row.singular,
        touchedLn0: row.touchedLn0 === true,
        underflowedExact: false,
        unverified: false,
        cutHits: row.cutHits,
      }
    : null;
  const status = message ? exactStatus(message, n) : null;
  const floatOk = message ? floatCertified(floated, message) : false;
  const hits = message?.cutHits ?? 0;
  const principal = message ? principalSentence(choice, agrees) : "";
  const showValue = primary === "exact" ? (message?.text ?? "checking…") : floated.text;
  const schanuel = choice.table?.note.includes("minimal conditional on Schanuel's conjecture")
    ? "minimal conditional on Schanuel's conjecture"
    : "";

  return (
    <main className="ti-stage">
      <div className="count-layout">
        <section className="ti-device">
          <div className="ti-top">
            <div>
              <h1 className="ti-wordmark">EML and One</h1>
              <p className="ti-model">count to n · words from 1 and EML only</p>
            </div>
            <a className="ti-home" href="../">Calculator</a>
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
              <p className="ti-lcd-caption">n = <span id="nbig">{n < 0 ? `−${-n}` : String(n)}</span></p>
              <p className="ti-lcd-caption" id="kline"><b>K {choice.K}</b> {choice.K === 1 ? "press" : "presses"} · {choice.source === "table" ? "word from the integer table" : "counting construction"}</p>
              <p className="ti-lcd-result" id="big" aria-live="polite">
                {!message ? <span className="count-pending">checking…</span> : showValue}
              </p>
              <div id="chips" aria-live="polite">
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
          <div className="count-controls">
            <button type="button" className="ti-text-btn" aria-label="n minus 1" onClick={() => writeHash(clamp(n - 1), mode)}>−</button>
            <input id="n" aria-label="n" type="number" min={-50} max={50} value={n} onChange={(event) => writeHash(clamp(Number(event.target.value)), mode)} />
            <button type="button" className="ti-text-btn" aria-label="n plus 1" onClick={() => writeHash(clamp(n + 1), mode)}>+</button>
          </div>
          <input id="slider" className="count-slider" type="range" min={-50} max={50} step={1} aria-label="n from −50 to 50" value={n} onChange={(event) => writeHash(clamp(Number(event.target.value)), mode)} />
          <label className="count-opt">
            <input type="checkbox" checked={mode === "ln0"} onChange={(event) => writeHash(n, event.target.checked ? "ln0" : "strict")} /> allow ln 0 = −∞ (off = only words that avoid ln 0)
          </label>
          <p className="count-conv"><b>Conventions.</b> Lower cut: Arg in [−π, π), so ln of a negative real takes Arg −π (on this cut −iπ becomes +iπ under the principal Log). ln 0 = −∞ when allowed. K counts presses: one per 1, one per E.</p>
        </section>
        <div className="count-rail">
          <section className="count-panel">
            <h2>The count label</h2>
            <div id="label">
              {choice.source === "table" && choice.table ? (
                <span className={`count-pill ${choice.table.kind}`}>{choice.table.status}</span>
              ) : (
                <span className="count-pill upper">{choice.familyLabel}</span>
              )}
              {choice.source === "family" && choice.table ? <span className={`count-pill ${choice.table.kind}`}>table: {choice.table.status}</span> : null}
              {choice.source === "family" && !choice.table ? <span className="count-pill upper">a construction, not a search record</span> : null}
            </div>
            {choice.table && choice.K > 1 ? <p className="count-cutline">{CUT_LINE}</p> : null}
            {choice.K === 1 ? <p className="count-cutline">{NO_GATES}</p> : null}
            {choice.source === "table" && choice.table ? <p className="count-src">The counting-construction word here is K {choice.familyK}; the table word is shorter{choice.table.ln0 ? " and uses ln 0 = −∞" : ""}.</p> : null}
            {schanuel ? <p className="count-note" id="schanuel">{schanuel}</p> : null}
            {choice.table ? <p className="count-src">Source: {choice.table.source}.</p> : null}
          </section>
          <section className="count-panel">
            <h2>Sequence · outline</h2>
            <Outline choice={choice} />
            <p className="count-note">{choice.spans.length ? `${choice.spans.length} × EEE1EE11 highlighted (gold and blue bands alternate)` : "no repeating block in this word"}</p>
            <PressLine node={node} />
          </section>
          <section className="count-panel">
            <h2>Sequence · every press</h2>
            <Flat choice={choice} />
            <p className="sr-only">The full word, one character per press, is in the copy text below.</p>
            <div className="count-actions">
              <button type="button" className="ti-text-btn" onClick={() => void navigator.clipboard?.writeText(choice.word)}>Copy as 1 / E</button>
              <button type="button" className="ti-text-btn" onClick={() => void navigator.clipboard?.writeText(choice.word.replace(/E/g, "0"))}>Copy as bits 1/0</button>
            </div>
            <p className="count-copy" id="copytext">{choice.word}</p>
          </section>
          <section className="count-panel">
            <How choice={choice} />
            <p className="count-foot">Values come from the calculator&apos;s exact engine. 0, −1 and 2 are proved minimal; other table lengths are shortest known; every other word is a construction.</p>
            <p className="count-foot">Why a counting construction gives n is in <a id="docs-link" href={DOCS}>docs/counting.md</a>.</p>
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
  return <>{text.slice(0, at)}<a href={DOCS}>{marker}</a>{text.slice(at + marker.length)}</>;
}

function Outline({ choice }: { choice: CountChoice }) {
  return (
    <div>
      {choice.chunks.map((chunk) => {
        const longPrefix = chunk.kind === "prefix" && chunk.end - chunk.start > 24;
        return (
          <div className="count-seg" key={`${chunk.kind}-${chunk.start}`}>
            <span>{chunk.label}{chunk.reps ? ` × ${chunk.reps}` : ""}</span>
            <span className="count-chips">
              {chunk.kind === "blocks" ? (
                <>
                  {chips(choice.word, chunk.start, chunk.start + 8)}
                  <span className="count-note">repeated {chunk.reps} time{chunk.reps === 1 ? "" : "s"}</span>
                </>
              ) : longPrefix ? (
                <>
                  <Chip ch="1" />
                  <span className="count-note">× {chunk.end - chunk.start}</span>
                </>
              ) : chips(choice.word, chunk.start, chunk.end)}
            </span>
            <span>{chunk.start + 1}–{chunk.end}</span>
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
    return <p className="count-note"><b>How it counts.</b> The prefix pushes {2 * choice.n + 2} ones. Each EEE1EE11 block takes one step toward {choice.n}. After {choice.n - 1} block{choice.n === 2 ? "" : "s"}, the tail EE1EE outputs {choice.n}.</p>;
  }
  if (choice.source === "family" && choice.spans.length && choice.n <= -1) {
    return <p className="count-note"><b>How it counts.</b> The same block runs {-choice.n} time{choice.n === -1 ? "" : "s"}; the tail E1EE outputs −{-choice.n}.</p>;
  }
  if (choice.source === "table") return <p className="count-note"><b>Table word.</b> Shorter than the counting-construction word, so the page shows the table&apos;s word and its status.</p>;
  return null;
}
