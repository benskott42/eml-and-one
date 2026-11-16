"use client";

import { useEffect, useRef, useState, useSyncExternalStore } from "react";
import { explainOutline, type Outline, type SequenceSnapshot } from "@/lib/eml/provenance";

const WINDOW = 400;
const openedLines: number[] = [];

function keepLineOpen(id: number): boolean {
  if (!openedLines.includes(id) && openedLines.length < 2) openedLines.push(id);
  return openedLines.includes(id);
}

function useNarrow(): boolean {
  return useSyncExternalStore(
    (notify) => {
      if (typeof window === "undefined" || !window.matchMedia) return () => {};
      const query = window.matchMedia("(max-width: 640px)");
      query.addEventListener("change", notify);
      return () => query.removeEventListener("change", notify);
    },
    () => typeof window !== "undefined" && !!window.matchMedia?.("(max-width: 640px)").matches,
    () => false,
  );
}

function copyText(text: string, done: () => void) {
  const clip = navigator.clipboard;
  if (!clip) return;
  void clip.writeText(text).then(done).catch(() => undefined);
}

function grouped(text: string): string {
  const parts: string[] = [];
  for (let i = 0; i < text.length; i += 5) parts.push(text.slice(i, i + 5).split("").join(" "));
  return parts.join(" · ");
}

export function SequencePanel({ sequence, typed, result }: { sequence: SequenceSnapshot; typed: string; result: string }) {
  const told = explainOutline(sequence.outline, BigInt(sequence.presses), typed, result);
  const narrow = useNarrow();
  const lineOpen = keepLineOpen(sequence.outline.node.id);
  const [show, setShow] = useState<"outline" | "flat">("outline");
  const [copied, setCopied] = useState("");
  const presses = sequence.presses;

  return (
    <div className="ti-sequence">
      <details key={sequence.outline.node.id} className="ti-fold" {...(lineOpen ? { open: true } : {})}>
        <summary>{told.line}</summary>
        <p>{told.full}</p>
      </details>
      <details className="ti-fold">
        <summary>Show all {presses} presses</summary>
        {sequence.copyable ? (
          <div className="ti-press-actions">
            <button type="button" className="ti-lcd-btn" onClick={() => copyText(sequence.oneE, () => setCopied("1/E"))}>
              {copied === "1/E" ? "Copied" : "Copy 1/E"}
            </button>
            <button type="button" className="ti-lcd-btn" onClick={() => copyText(sequence.bits, () => setCopied("bits"))}>
              {copied === "bits" ? "Copied" : "Copy bits"}
            </button>
          </div>
        ) : (
          <p>too long to list</p>
        )}
        <div className="ti-press-actions" role="group" aria-label="Sequence view">
          <button type="button" className="ti-text-btn" aria-pressed={show === "outline"} onClick={() => setShow("outline")}>Outline</button>
          <button type="button" className="ti-text-btn" aria-pressed={show === "flat"} disabled={!sequence.copyable} onClick={() => setShow("flat")}>Flat</button>
        </div>
        {show === "flat" && sequence.copyable ? (
          <>
            <p className="ti-flat-text">{presses} presses: {grouped(sequence.oneE)}</p>
            <FlatBoard root={sequence.outline} word={sequence.oneE} />
          </>
        ) : (
          <OutlineRows node={sequence.outline} depth={0} maxDepth={narrow ? 2 : 3} />
        )}
      </details>
    </div>
  );
}

function FlatBoard({ root, word }: { root: Outline; word: string }) {
  const rows = bands(root);
  return (
    <div className="ti-chip-board">
      {rows.map((row, index) => {
        const text = word.slice(Number(row.start), Number(row.end));
        const name = row.kind === "glue" ? row.name : blockName(row.node);
        return (
          <div key={index}>
            <p className={row.kind === "glue" ? "ti-glue" : "ti-flat-band"}>
              {name} {rangeLabel(row.start, row.end)}: {grouped(text.length > 80 ? `${text.slice(0, 80)}…` : text)}
            </p>
            {text ? <ChipChunk text={text} start={Number(row.start)} /> : null}
          </div>
        );
      })}
    </div>
  );
}

function ChipChunk({ text, start }: { text: string; start: number }) {
  const [cursor, setCursor] = useState(0);
  const [origin, setOrigin] = useState(0);
  const rowRef = useRef<HTMLDivElement>(null);
  const pending = useRef<number | null>(null);
  const end = Math.min(text.length, origin + WINDOW);
  useEffect(() => {
    const index = pending.current;
    if (index === null) return;
    pending.current = null;
    rowRef.current?.querySelector<HTMLElement>(`[data-index="${index}"]`)?.focus();
  }, [cursor, origin]);

  function move(next: number) {
    if (next < 0 || next >= text.length) return;
    pending.current = next;
    if (next < origin || next >= origin + WINDOW) setOrigin(Math.max(0, Math.min(next, text.length - WINDOW)));
    setCursor(next);
  }

  return (
    <div
      ref={rowRef}
      role="list"
      aria-label={`${text.length} presses from ${start + 1}`}
      className="ti-chip-row"
      onKeyDown={(event) => {
        if (event.key !== "ArrowRight" && event.key !== "ArrowLeft") return;
        event.preventDefault();
        move(event.key === "ArrowRight" ? cursor + 1 : cursor - 1);
      }}
    >
      {text.slice(origin, end).split("").map((token, offset) => {
        const index = origin + offset;
        const press = start + index + 1;
        return (
          <span
            role="listitem"
            key={press}
            data-index={index}
            tabIndex={index === cursor ? 0 : -1}
            className={index > 0 && index % 5 === 0 ? "ti-press-chip is-group" : "ti-press-chip"}
          >
            {token === "E" ? "EML" : "1"}
            {press % 10 === 0 ? <sup>{press}</sup> : null}
          </span>
        );
      })}
    </div>
  );
}

function OutlineRows({ node, depth, maxDepth }: { node: Outline; depth: number; maxDepth: number }) {
  const crowded = node.length > BigInt(60);
  const repeated = node.repeat && node.length > BigInt(1);
  const [open, setOpen] = useState(depth === 0 || (depth < maxDepth && !crowded && !repeated));
  const rows = bands(node);
  return (
    <div className="ti-outline">
      <button type="button" className="ti-outline-row" onClick={() => setOpen((value) => !value)}>
        <span>{blockName(node)}</span>
        <span>{rangeLabel(node.start, node.end)}</span>
        {node.record ? (
          <span className="ti-pill">
            {node.record.provenMinimal ? `${node.record.text} · shortest possible (lower cut, ln 0 = −∞ where used)` : node.record.text}
          </span>
        ) : null}
        {!open && crowded ? <span>▸ {node.length.toString()} presses inside</span> : null}
      </button>
      {open ? rows.map((row, index) => (
        row.kind === "glue" ? (
          <p key={index} className="ti-glue">{row.name} {rangeLabel(row.start, row.end)}</p>
        ) : (
          <OutlineRows key={index} node={row.node} depth={depth + 1} maxDepth={maxDepth} />
        )
      )) : null}
    </div>
  );
}

function blockName(node: Outline): string {
  if (node.node.type === "one") return "1";
  if (node.repeat && node.length > BigInt(1)) return "↺ same block again";
  return node.name;
}

type Band =
  | { kind: "glue"; name: string; start: bigint; end: bigint }
  | { kind: "block"; node: Outline; start: bigint; end: bigint };

function bands(node: Outline): Band[] {
  if (node.children.length === 0) return [];
  const rows: Band[] = [];
  let cursor = node.start;
  for (let index = 0; index < node.children.length; index += 1) {
    const child = node.children[index];
    if (!child) continue;
    if (child.start > cursor) {
      rows.push({ kind: "glue", name: cursor === node.start ? "start" : "combine", start: cursor, end: child.start });
    }
    rows.push({ kind: "block", node: child, start: child.start, end: child.end });
    cursor = child.end;
    if (index === node.children.length - 1 && cursor < node.end) {
      rows.push({ kind: "glue", name: "finish", start: cursor, end: node.end });
    }
  }
  return rows;
}

function rangeLabel(start: bigint, end: bigint): string {
  if (end <= start) return "";
  return `${(start + BigInt(1)).toString()}–${end.toString()}`;
}
