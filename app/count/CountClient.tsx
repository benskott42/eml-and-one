"use client";

import dynamic from "next/dynamic";

const CountApp = dynamic(() => import("./CountApp").then((mod) => mod.CountApp), {
  ssr: false,
  loading: () => (
    <main className="ti-stage">
      <p className="ti-model">count to n</p>
      <p className="ti-lcd-caption">n = <span id="nbig"></span></p>
      <p id="big"></p>
    </main>
  ),
});

export function CountClient() {
  return <CountApp />;
}
