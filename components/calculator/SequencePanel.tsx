"use client";

import { useMemo, useState, useSyncExternalStore } from "react";
import { explainOutline, type Outline, type SequenceSnapshot } from "@/lib/eml/provenance";

const CHUNK = 50;
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
  const told = useMemo(
    () => explainOutline(sequence.outline, BigInt(sequence.presses), typed, result),
    [sequence, typed, result],
  );
  const narrow = useNarrow();
  const lineOpen = keepLineOpen(sequence.outline.node.id);
  const [show, setShow] = useState<"outline" | "flat">("outline");
  const [copied, setCopied] = useState("");
  const presses = sequence.presses;
  const chunks: string[] = [];
  if (sequence.copyable) {
    for (let i = 0; i < sequence.oneE.length; i += CHUNK) chunks.push(sequence.oneE.slice(i, i + CHUNK));
  }

  return (
    <div className="ti-sequence">
      <details key={sequence.outline.node.id} className="ti-fold" {...(lineOpen ? { open: true } : {})}>
        <summary>{told.line}</summary>
        <p>{told.full}</p>
      </details>
      <details className="ti-fold">
        <summary>Show all {presses}</summary>
        {sequence.copyable ? (
          <>
            <p className="ti-flat-text">{presses} presses: {grouped(sequence.oneE)}</p>
            <div className="ti-chip-board" aria-hidden="true">
              {chunks.map((chunk, index) => (
                <ChipChunk key={index} text={chunk} start={index * CHUNK} />
              ))}
            </div>
            <div className="ti-press-actions">
              <button type="button" className="ti-lcd-btn" onClick={() => copyText(sequence.oneE, () => setCopied("1/E"))}>
                {copied === "1/E" ? "Copied" : "Copy 1/E"}
              </button>
              <button type="button" className="ti-lcd-btn" onClick={() => copyText(sequence.bits, () => setCopied("bits"))}>
                {copied === "bits" ? "Copied" : "Copy bits"}
              </button>
            </div>
          </>
        ) : (
          <p>too long to list</p>
        )}
        <div className="ti-press-actions" role="group" aria-label="Sequence view">
          <button type="button" className="ti-text-btn" aria-pressed={show === "outline"} onClick={() => setShow("outline")}>Outline</button>
          <button type="button" className="ti-text-btn" aria-pressed={show === "flat"} disabled={!sequence.copyable} onClick={() => setShow("flat")}>Flat</button>
        </div>
        {show === "flat" && sequence.copyable ? (
          <FlatRows root={sequence.outline} word={sequence.oneE} />
        ) : (
          <OutlineRows node={sequence.outline} depth={0} maxDepth={narrow ? 1 : 2} />
        )}
      </details>
    </div>
  );
}

function ChipChunk({ text, start }: { text: string; start: number }) {
  const [cursor, setCursor] = useState(0);
  const label = `${text.length} presses from ${start + 1}`;
  return (
    <div
      role="list"
      aria-label={label}
      className="ti-chip-row"
      onKeyDown={(event) => {
        if (event.key === "ArrowRight") setCursor((value) => Math.min(text.length - 1, value + 1));
        if (event.key === "ArrowLeft") setCursor((value) => Math.max(0, value - 1));
      }}
    >
      {text.split("").map((token, index) => {
        const press = start + index + 1;
        return (
          <span
            role="listitem"
            key={press}
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
  const crowded = node.children.length > 60;
  const [open, setOpen] = useState(depth < maxDepth && !crowded && !node.repeat);
  const rows = bands(node);
  return (
    <div className="ti-outline">
      <button type="button" className="ti-outline-row" onClick={() => setOpen((value) => !value)}>
        <span>{node.repeat ? "↺ same block again" : node.name}</span>
        <span>{rangeLabel(node.start, node.end)}</span>
        {node.label?.kind === "record" ? <span className="ti-pill">{node.label.provenMinimal ? `shortest possible (lower cut, ln 0 = −∞ where used)` : node.label.text}</span> : null}
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

function FlatRows({ root, word }: { root: Outline; word: string }) {
  return (
    <div>
      {bands(root).map((row, index) => {
        const text = word.slice(Number(row.start), Number(row.end));
        const name = row.kind === "glue" ? row.name : row.node.repeat ? "↺ same block again" : row.node.name;
        return (
          <p key={index} className={row.kind === "glue" ? "ti-glue" : "ti-flat-band"}>
            {name} {rangeLabel(row.start, row.end)}: {grouped(text)}
          </p>
        );
      })}
    </div>
  );
}

type Band =
  | { kind: "glue"; name: string; start: bigint; end: bigint }
  | { kind: "block"; node: Outline; start: bigint; end: bigint };

function bands(node: Outline): Band[] {
  const rows: Band[] = [];
  let cursor = node.start;
  let gap = 0;
  const names = ["start", "combine", "finish"];
  for (const child of node.children) {
    if (child.start > cursor) {
      rows.push({ kind: "glue", name: names[Math.min(gap, names.length - 1)] ?? "glue", start: cursor, end: child.start });
      gap += 1;
    }
    rows.push({ kind: "block", node: child, start: child.start, end: child.end });
    cursor = child.end;
  }
  if (cursor < node.end) rows.push({ kind: "glue", name: "finish", start: cursor, end: node.end });
  return rows;
}

function rangeLabel(start: bigint, end: bigint): string {
  if (end <= start) return "";
  return `${(start + BigInt(1)).toString()}–${end.toString()}`;
}
