import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { close } from "../complex";
import { exactReport } from "../exact";
import { formatC } from "../format";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckContext } from "./_types";

export const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../../..");
export const tsxCli = path.join(repoRoot, "node_modules", "tsx", "dist", "cli.mjs");

/** The screen's worker path: parse, pack, unpack, then the exact engine. */
export function workerReport(source: string) {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  return exactReport(unpackCircuit(packed.tokens, packed.root), {}, { maxNodes: 80_000 });
}

/** A fresh node process. `npx` and `URL.pathname` both break on Windows. */
export function runTsx(script: string, input: string, timeout = 180_000) {
  return spawnSync(process.execPath, [tsxCli, path.join(repoRoot, script)], {
    cwd: repoRoot,
    input,
    encoding: "utf8",
    timeout,
  });
}

export function relClose(
  got: { re: number; im: number },
  want: { re: number; im: number },
  tol = 1e-12,
): boolean {
  const scale = Math.max(Math.hypot(want.re, want.im), 1e-320);
  return Math.hypot(got.re - want.re, got.im - want.im) <= tol * scale;
}

export function makeCheckHelpers(ctx: CheckContext) {
  function check(
    name: string,
    got: { re: number; im: number },
    want: { re: number; im: number },
    tol = 1e-6,
  ) {
    const ok = close(got, want, tol) && Number.isFinite(got.re) && Number.isFinite(got.im);
    if (!ok) {
      ctx.fail("FAIL", name, "got", formatC(got), got, "want", want);
    }
  }

  function absClose(
    name: string,
    got: { re: number; im: number },
    re: number,
    im: number,
    tol = 1e-8,
  ) {
    if (Math.abs(got.re - re) > tol || Math.abs(got.im - im) > tol) {
      ctx.fail("FAIL", name, "got", got, "want", { re, im });
    }
  }

  return { check, absClose };
}
