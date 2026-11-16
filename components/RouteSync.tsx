"use client";

import { usePathname } from "next/navigation";
import { useEffect, useRef } from "react";

function browserAppPath(): string {
  const base = document.documentElement.dataset.basePath ?? "";
  let path = window.location.pathname;
  if (base && path.startsWith(base)) path = path.slice(base.length) || "/";
  return path;
}

function norm(path: string): string {
  if (path.length > 1 && path.endsWith("/")) return path.slice(0, -1);
  return path || "/";
}

function focusHeading(): boolean {
  const heading = document.querySelector("main h1");
  const main = document.querySelector("main");
  const target = heading instanceof HTMLElement ? heading : main instanceof HTMLElement ? main : null;
  if (!target) return false;
  if (target.tabIndex < 0) target.tabIndex = -1;
  target.focus();
  return true;
}

/** Keep the rendered page on the URL after Back, and move focus to the new page's heading. */
export function RouteSync() {
  const pathname = usePathname();
  const pathnameRef = useRef(pathname);
  const first = useRef(true);

  useEffect(() => {
    pathnameRef.current = pathname;
  }, [pathname]);

  useEffect(() => {
    const onPop = (event: PopStateEvent) => {
      const state = event.state as { __NA?: unknown } | null;
      if (state?.__NA) return;
      if (norm(browserAppPath()) === norm(pathnameRef.current)) return;
      window.location.reload();
    };
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, []);

  useEffect(() => {
    if (first.current) {
      first.current = false;
      return;
    }
    let cancelled = false;
    let tries = 0;
    const place = () => {
      if (cancelled) return;
      tries += 1;
      if (!focusHeading() && tries < 20) {
        window.setTimeout(place, 50);
        return;
      }
      // Firefox moves focus to the body after the old page's focused node is removed,
      // and that reset can land after this effect. Put the heading back once it has.
      window.setTimeout(() => {
        if (!cancelled) focusHeading();
      }, 50);
    };
    const frame = window.requestAnimationFrame(place);
    return () => {
      cancelled = true;
      window.cancelAnimationFrame(frame);
    };
  }, [pathname]);

  return null;
}
