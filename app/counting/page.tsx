import { readFileSync } from "node:fs";
import { join } from "node:path";
import Link from "next/link";
import { CountReturn } from "./CountReturn";
import type { ReactNode } from "react";
import "@/components/ti-calculator.css";
import "../count/count.css";

export const metadata = {
  title: "Why the counting construction gives n",
};

function mathText(text: string, key: string): ReactNode[] {
  const out: ReactNode[] = [];
  let plain = "";
  let i = 0;
  const flush = () => {
    if (!plain) return;
    out.push(plain);
    plain = "";
  };
  const supAt = (from: string) => /^\^\{([^}]+)\}/.exec(from) || /^\^\(([^)]+)\)/.exec(from) || /^\^([A-Za-z0-9]+)/.exec(from);
  while (i < text.length) {
    const rest = text.slice(i);
    const sub = /^([A-Za-zπ])_\{([^}]+)\}/.exec(rest) || /^([A-Za-zπ])_([A-Za-z0-9]+)/.exec(rest);
    const sup = /^([A-Za-zπ])\^\{([^}]+)\}/.exec(rest) || /^([A-Za-zπ])\^\(([^)]+)\)/.exec(rest) || /^([A-Za-zπ])\^([A-Za-z0-9]+)/.exec(rest);
    const lone = supAt(rest);
    if (sub) {
      flush();
      i += sub[0].length;
      const extra = supAt(text.slice(i));
      if (extra) i += extra[0].length;
      out.push(<span key={`${key}-${i}`}>{sub[1]}<sub>{sub[2]}</sub>{extra ? <sup>{extra[1]}</sup> : null}</span>);
      continue;
    }
    if (sup) {
      flush();
      out.push(<span key={`${key}-${i}`}>{sup[1]}<sup>{sup[2]}</sup></span>);
      i += sup[0].length;
      continue;
    }
    if (lone) {
      flush();
      out.push(<sup key={`${key}-${i}`}>{lone[1]}</sup>);
      i += lone[0].length;
      continue;
    }
    plain += text[i];
    i += 1;
  }
  flush();
  return out;
}

function inline(text: string): ReactNode[] {
  const out: ReactNode[] = [];
  for (const [index, part] of text.split(/(`[^`]+`)/g).entries()) {
    if (part.startsWith("`") && part.endsWith("`")) out.push(<code key={index}>{part.slice(1, -1)}</code>);
    else out.push(...mathText(part, String(index)));
  }
  return out;
}

function renderLines(lines: string[], key: string): ReactNode[] {
  const nodes: ReactNode[] = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i] ?? "";
    if (line.startsWith("# ")) {
      nodes.push(<h1 key={`${key}-h-${i}`}>{inline(line.slice(2))}</h1>);
      i += 1;
      continue;
    }
    if (line.startsWith("## ")) {
      nodes.push(<h2 key={`${key}-h-${i}`}>{inline(line.slice(3))}</h2>);
      i += 1;
      continue;
    }
    if (line.startsWith("- ")) {
      const items: string[] = [];
      const at = i;
      while (i < lines.length && (lines[i] ?? "").startsWith("- ")) {
        items.push((lines[i] ?? "").slice(2));
        i += 1;
      }
      nodes.push(<ul key={`${key}-ul-${at}`}>{items.map((item, itemIndex) => <li key={itemIndex}>{inline(item)}</li>)}</ul>);
      continue;
    }
    if (!line.trim()) {
      i += 1;
      continue;
    }
    const para: string[] = [];
    const at = i;
    while (i < lines.length) {
      const next = lines[i] ?? "";
      if (!next.trim() || next.startsWith("#") || next.startsWith("- ")) break;
      para.push(next);
      i += 1;
    }
    nodes.push(<p key={`${key}-p-${at}`}>{inline(para.join(" "))}</p>);
  }
  return nodes;
}

function renderDoc(markdown: string): ReactNode[] {
  return markdown.replace(/\r\n/g, "\n").trim().split(/\n\n+/).map((block, index) => (
    <div key={index}>{renderLines(block.split("\n"), String(index))}</div>
  ));
}

export default function CountingPage() {
  const text = readFileSync(join(process.cwd(), "docs/counting.md"), "utf8");
  return (
    <main className="ti-stage">
      <article className="count-doc">
        <nav className="count-doc-nav">
          <CountReturn />
          <Link className="ti-home" href="/">Calculator</Link>
        </nav>
        {renderDoc(text)}
      </article>
    </main>
  );
}
