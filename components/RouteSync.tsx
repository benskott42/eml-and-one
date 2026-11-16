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
    const heading = document.querySelector("main h1");
    if (!(heading instanceof HTMLElement)) return;
    heading.tabIndex = -1;
    heading.focus();
  }, [pathname]);

  return null;
}
