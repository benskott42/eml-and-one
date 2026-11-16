import { readFileSync } from "node:fs";
import { join } from "node:path";
import Link from "next/link";
import type { ReactNode } from "react";
import "@/components/ti-calculator.css";
import "../count/count.css";

export const metadata = {
  title: "Why the counting construction gives n",
};

function inline(text: string): ReactNode[] {
  return text.split(/(`[^`]+`)/g).map((part, index) => (
    part.startsWith("`") && part.endsWith("`") ? <code key={index}>{part.slice(1, -1)}</code> : part
  ));
}

function renderDoc(markdown: string): ReactNode[] {
  return markdown.replace(/\r\n/g, "\n").trim().split(/\n\n+/).map((block, index) => {
    const lines = block.split("\n");
    if (lines[0]?.startsWith("# ")) return <h1 key={index}>{inline(lines[0].slice(2))}</h1>;
    if (lines[0]?.startsWith("## ")) return <h2 key={index}>{inline(lines[0].slice(3))}</h2>;
    if (lines.every((line) => line.startsWith("- "))) {
      return (
        <ul key={index}>
          {lines.map((line, item) => <li key={item}>{inline(line.slice(2))}</li>)}
        </ul>
      );
    }
    return <p key={index}>{inline(lines.join(" "))}</p>;
  });
}

export default function CountingPage() {
  const text = readFileSync(join(process.cwd(), "docs/counting.md"), "utf8");
  return (
    <main className="ti-stage">
      <article className="count-doc">
        <p>
          <Link className="ti-home" href="/count">Count to n</Link>
          {" "}
          <Link className="ti-home" href="/">Calculator</Link>
        </p>
        {renderDoc(text)}
      </article>
    </main>
  );
}
