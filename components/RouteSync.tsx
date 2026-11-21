"use client";

import { usePathname, useRouter } from "next/navigation";
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

/** Move focus to the new page's heading, and follow Back when the URL and the page disagree. */
export function RouteSync() {
  const pathname = usePathname();
  const router = useRouter();
  const pathnameRef = useRef(pathname);
  const routerRef = useRef(router);
  const first = useRef(true);

  useEffect(() => {
    pathnameRef.current = pathname;
    routerRef.current = router;
  }, [pathname, router]);

  useEffect(() => {
    const onPop = () => {
      // An address-bar hash edit is not a router entry, so Back can leave the
      // previous page on screen. Ask the public router to show that URL.
      if (window.history.state != null) return;
      const path = browserAppPath();
      if (norm(path) === norm(pathnameRef.current)) return;
      const hash = window.location.hash;
      routerRef.current.replace(`${path}${window.location.search}${hash}`, { scroll: false });
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
