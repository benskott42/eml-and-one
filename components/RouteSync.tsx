"use client";

import { usePathname } from "next/navigation";
import { useEffect, useRef } from "react";

/** Move focus to the new page's heading. */
export function RouteSync() {
  const pathname = usePathname();
  const first = useRef(true);

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
