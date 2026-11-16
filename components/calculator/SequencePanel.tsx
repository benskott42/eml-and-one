"use client";

import { useEffect, useRef, useState, useSyncExternalStore } from "react";
import { explainOutline, snapshotSequence, type Outline, type SequenceSnapshot, type SequenceSource } from "@/lib/eml/provenance";

const WINDOW = 400;

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

function summaryLine(typed: string, result: string, presses: string): string {
  const trimmed = result.trim();
  const safe = !trimmed || trimmed === "0" || trimmed === "−0" || trimmed === "computing" || trimmed === "—" ? null : trimmed;
  return safe ? `${typed || "this"} → ${safe} in ${presses} presses.` : `${typed || "this"} in ${presses} presses.`;
}

export function SequencePanel({ source, typed, result }: { source: SequenceSource; typed: string; result: string }) {
  const narrow = useNarrow();
  const [show, setShow] = useState<"outline" | "flat">("outline");
  const [copied, setCopied] = useState("");
  const [snap, setSnap] = useState<SequenceSnapshot | null>(null);
  const [showOpen, setShowOpen] = useState(false);
  const [toldOpen, setToldOpen] = useState(false);
  const [told, setTold] = useState<string | null>(null);
  const presses = source.presses;
  const line = summaryLine(typed, result, presses);

  function build(): SequenceSnapshot {
    if (snap) return snap;
    const next = snapshotSequence(source.node, source.labels);
    setSnap(next);
    return next;
  }

  return (
    <div className="ti-sequence">
      <details
        className="ti-fold"
        onToggle={(event) => {
          const open = event.currentTarget.open;
          setToldOpen(open);
          if (!open || told !== null) return;
          const next = build();
          setTold(explainOutline(next.outline, BigInt(next.presses), typed, result).full);
        }}
      >
        <summary>{line}</summary>
        {toldOpen && told ? <p>{told}</p> : null}
      </details>
      <details
        className="ti-fold"
        onToggle={(event) => {
          const open = event.currentTarget.open;
          setShowOpen(open);
          if (open) build();
        }}
      >
        <summary>Show all {presses} presses</summary>
        {showOpen && snap ? (
          <>
            {snap.copyable ? (
              <div className="ti-press-actions">
                <button type="button" className="ti-lcd-btn" onClick={() => copyText(snap.oneE, () => setCopied("1/E"))}>
                  {copied === "1/E" ? "Copied" : "Copy 1/E"}
                </button>
                <button type="button" className="ti-lcd-btn" onClick={() => copyText(snap.bits, () => setCopied("bits"))}>
                  {copied === "bits" ? "Copied" : "Copy bits"}
                </button>
              </div>
            ) : (
              <p>too long to list</p>
            )}
            <div className="ti-press-actions" role="group" aria-label="Sequence view">
              <button type="button" className="ti-text-btn" aria-pressed={show === "outline"} onClick={() => setShow("outline")}>Outline</button>
              <button type="button" className="ti-text-btn" aria-pressed={show === "flat"} disabled={!snap.copyable} onClick={() => setShow("flat")}>Flat</button>
            </div>
            {show === "flat" && snap.copyable ? (
              <>
                <p className="ti-flat-text">{presses} presses: {grouped(snap.oneE)}</p>
                <FlatBoard root={snap.outline} word={snap.oneE} />
              </>
            ) : (
              <OutlineRows node={snap.outline} depth={0} maxDepth={narrow ? 2 : 3} origin={BigInt(0)} />
            )}
          </>
        ) : null}
      </details>
    </div>
  );
}

function FlatBoard({ root, word }: { root: Outline; word: string }) {
  const rows = bands(root, BigInt(0));
  const [cursor, setCursor] = useState(0);
  const [origin, setOrigin] = useState(0);
  const boardRef = useRef<HTMLDivElement>(null);
  const pending = useRef<number | null>(null);
  const end = Math.min(word.length, origin + WINDOW);
  useEffect(() => {
    const index = pending.current;
    if (index === null) return;
    pending.current = null;
    boardRef.current?.querySelector<HTMLElement>(`[data-abs="${index}"]`)?.focus();
  }, [cursor, origin]);

  function move(next: number) {
    if (next < 0 || next >= word.length) return;
    pending.current = next;
    if (next < origin || next >= origin + WINDOW) setOrigin(Math.max(0, Math.min(next, word.length - WINDOW)));
    setCursor(next);
  }

  return (
    <div
      ref={boardRef}
      className="ti-chip-board"
      onKeyDown={(event) => {
        if (event.key !== "ArrowRight" && event.key !== "ArrowLeft") return;
        event.preventDefault();
        move(event.key === "ArrowRight" ? cursor + 1 : cursor - 1);
      }}
    >
      {rows.map((row, index) => {
        const sliceStart = Math.max(Number(row.start), origin);
        const sliceEnd = Math.min(Number(row.end), end);
        if (sliceEnd <= sliceStart) return null;
        const text = word.slice(sliceStart, sliceEnd);
        const name = row.kind === "glue" ? row.name : blockName(row.node);
        return (
          <div key={index}>
            <p className={row.kind === "glue" ? "ti-glue" : "ti-flat-band"}>
              {name} {rangeLabel(row.start, row.end)}: {grouped(text.length > 80 ? `${text.slice(0, 80)}…` : text)}
            </p>
            <div role="list" aria-label={`${text.length} presses from ${sliceStart + 1}`} className="ti-chip-row">
              {text.split("").map((token, offset) => {
                const abs = sliceStart + offset;
                const press = abs + 1;
                return (
                  <span
                    role="listitem"
                    key={press}
                    data-abs={abs}
                    tabIndex={abs === cursor ? 0 : -1}
                    className={abs > 0 && abs % 5 === 0 ? "ti-press-chip is-group" : "ti-press-chip"}
                  >
                    {token === "E" ? "EML" : "1"}
                    {press % 10 === 0 ? <sup>{press}</sup> : null}
                  </span>
                );
              })}
            </div>
          </div>
        );
      })}
    </div>
  );
}

function OutlineRows({ node, depth, maxDepth, origin }: { node: Outline; depth: number; maxDepth: number; origin: bigint }) {
  const crowded = node.length > BigInt(60);
  const repeated = node.repeat && node.length > BigInt(1);
  const [open, setOpen] = useState(depth === 0 || (depth < maxDepth && !crowded && !repeated));
  const rows = bands(node, origin);
  return (
    <div className="ti-outline">
      <button type="button" className="ti-outline-row" onClick={() => setOpen((value) => !value)}>
        <span>{blockName(node)}</span>
        <span>{rangeLabel(origin, origin + node.length)}</span>
        {node.record ? (
          <span className="ti-pill">
            {node.record.provedMinimal ? `${node.record.text} · shortest possible (lower cut, ln 0 = −∞ where used)` : node.record.text}
          </span>
        ) : null}
        {!open && crowded ? <span>▸ {node.length.toString()} presses inside</span> : null}
      </button>
      {open ? rows.map((row, index) => (
        row.kind === "glue" ? (
          <p key={index} className="ti-glue">{row.name} {rangeLabel(row.start, row.end)}</p>
        ) : (
          <OutlineRows key={index} node={row.node} depth={depth + 1} maxDepth={maxDepth} origin={row.start} />
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

function bands(node: Outline, origin: bigint): Band[] {
  if (node.children.length === 0) return [];
  const rows: Band[] = [];
  let cursor = BigInt(0);
  for (let index = 0; index < node.children.length; index += 1) {
    const child = node.children[index];
    if (!child) continue;
    if (child.start > cursor) {
      rows.push({ kind: "glue", name: cursor === BigInt(0) ? "start" : "combine", start: origin + cursor, end: origin + child.start });
    }
    rows.push({ kind: "block", node: child, start: origin + child.start, end: origin + child.end });
    cursor = child.end;
    if (index === node.children.length - 1 && cursor < node.length) {
      rows.push({ kind: "glue", name: "finish", start: origin + cursor, end: origin + node.length });
    }
  }
  return rows;
}

function rangeLabel(start: bigint, end: bigint): string {
  if (end <= start) return "";
  return `${(start + BigInt(1)).toString()}–${end.toString()}`;
}
