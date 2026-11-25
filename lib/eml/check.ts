import { existsSync, readdirSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import shardWeights from "./check-shards.json";
import type { CheckContext, CheckModule, CheckModuleExport } from "./checks/_types";

/**
 * EML check runner.
 *
 * Auto-discovers all standalone check modules under `lib/eml/checks/*.ts`
 * (ignoring `_*.ts` helpers). Each file default-exports a `CheckModule` or
 * `CheckModule[]`.
 *
 * Environment flags:
 * - `EML_SHARD=i/N`: run only checks assigned to shard `i` (0-based) of `N`.
 *   Numeric ids present in `check-shards.json` are dealt greedy heaviest-first;
 *   unweighted numeric ids go round-robin (`id % N`), and string ids hash by name.
 * - `EML_ONLY_BLOCK=<id|filename>[,...]`: run only matching checks or files
 *   (overrides `EML_SHARD`).
 * - `EML_BLOCK_TIMES=1`: print each check's wall time.
 * - `EML_WRITE_TIMINGS=<path>`: write recorded timings as JSON.
 */

const shardMatch = /^(\d+)\/(\d+)$/.exec(process.env.EML_SHARD ?? "");
const shardIndex = shardMatch ? Number(shardMatch[1]) : 0;
const shardCount = shardMatch ? Math.max(1, Number(shardMatch[2])) : 1;
const shardOf = assignShards(shardCount);
const onlyBlockTokens = process.env.EML_ONLY_BLOCK
  ? new Set(
      process.env.EML_ONLY_BLOCK.split(",")
        .map((s) => s.trim())
        .filter(Boolean),
    )
  : null;
const blockTimes = process.env.EML_BLOCK_TIMES === "1";
const writeTimingsPath = process.env.EML_WRITE_TIMINGS || "";

function assignShards(count: number): Map<number, number> {
  const owner = new Map<number, number>();
  if (count <= 1) return owner;
  const load = Array.from({ length: count }, () => 0);
  const weights = Object.entries(shardWeights as Record<string, number>).map(
    ([id, ms]) => [Number(id), ms] as const,
  );
  weights.sort((a, b) => b[1] - a[1] || a[0] - b[0]);
  for (const [id, ms] of weights) {
    let best = 0;
    for (let k = 1; k < count; k += 1) {
      if (load[k] < load[best]) best = k;
    }
    owner.set(id, best);
    load[best] += ms;
  }
  return owner;
}

function hashName(name: string): number {
  let h = 0;
  for (let i = 0; i < name.length; i += 1) {
    h = (h * 31 + name.charCodeAt(i)) >>> 0;
  }
  return h;
}

function isSelected(base: string, id: number | string | undefined): boolean {
  if (onlyBlockTokens) {
    return onlyBlockTokens.has(base) || (id !== undefined && onlyBlockTokens.has(String(id)));
  }
  if (shardCount <= 1) return true;
  if (typeof id === "number") {
    return (shardOf.get(id) ?? id % shardCount) === shardIndex;
  }
  const key = id !== undefined ? String(id) : base;
  return hashName(key) % shardCount === shardIndex;
}

async function runAllChecks(): Promise<void> {
  let failed = 0;
  const recordedTimings: Record<string, number> = {};
  const ctx: CheckContext = {
    fail(message: string, ...details: unknown[]) {
      failed += 1;
      console.log(message, ...details);
    },
    addFailures(count: number) {
      failed += count;
    },
  };

  const checksDir = path.join(path.dirname(fileURLToPath(import.meta.url)), "checks");
  if (existsSync(checksDir)) {
    const files = readdirSync(checksDir)
      .filter((name) => name.endsWith(".ts") && !name.startsWith("_"))
      .sort();

    for (const file of files) {
      const base = file.slice(0, -3);
      const mod = (await import(pathToFileURL(path.join(checksDir, file)).href)) as {
        default?: CheckModuleExport;
      };
      const exported = mod.default;
      if (!exported) continue;
      const list: CheckModule[] = Array.isArray(exported) ? exported : [exported];

      for (const checkMod of list) {
        if (!checkMod || typeof checkMod.run !== "function") continue;
        const id = checkMod.id;
        if (!isSelected(base, id)) continue;
        const t0 = performance.now();
        await checkMod.run(ctx);
        const ms = Math.round(performance.now() - t0);
        const key = id !== undefined ? String(id) : base;
        recordedTimings[key] = ms;
        if (blockTimes) console.log(`block ${key} ${ms} ms`);
      }
    }
  }

  if (shardCount > 1) console.log(`shard ${shardIndex}/${shardCount}`);

  if (writeTimingsPath) {
    writeFileSync(writeTimingsPath, `${JSON.stringify(recordedTimings, null, 2)}\n`, "utf8");
  }

  if (failed) {
    console.log(`\n${failed} failed`);
    process.exit(1);
  }
  console.log("all passed");
}

runAllChecks().catch((err) => {
  console.error(err);
  process.exit(1);
});
