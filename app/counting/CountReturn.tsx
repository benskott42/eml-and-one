"use client";

import Link from "next/link";
import { useRouter } from "next/navigation";
import { readCountHash } from "@/components/countMemory";

export function CountReturn() {
  const router = useRouter();
  return (
    <Link
      className="ti-home"
      href="/count"
      onClick={(event) => {
        if (!readCountHash()) return;
        event.preventDefault();
        // The hash on router.push is dropped. A query flag tells the count page
        // to put the saved n back, instead of the empty-address default of 7.
        router.push("/count/?back=1");
      }}
    >
      Count to n
    </Link>
  );
}
