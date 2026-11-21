/**
 * Single-threaded timings for searchConstants.
 * Median of 5 runs, default path against sound mode. Each run is a fresh
 * process: exact.ts keeps a process-wide cache, and a second search in the
 * same process would not time the exact confirmations.
 *
 *   npx tsx scripts/sound-bench.ts
 */
import { spawnSync } from "node:child_process";
import { searchConstants, type SoundReport } from "../lib/eml/golf";

const KS = [17, 19, 21];
const RUNS = 5;

if (process.env.SOUND_BENCH_ONCE === "1") {
  const maxK = Number(process.env.SOUND_BENCH_K);
  const sound = process.env.SOUND_BENCH_SOUND === "1";
  const started = performance.now();
  const result = searchConstants(maxK, sound ? { sound: true } : {});
  process.stdout.write(
    `${JSON.stringify({ ms: performance.now() - started, pool: result.pool, sound: result.sound ?? null })}\n`,
  );
  process.exit(0);
}

function median(values: number[]): number {
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[(sorted.length - 1) >> 1] ?? 0;
}

function time(maxK: number, sound: boolean): { ms: number; report: SoundReport | null; pool: number } {
  const child = spawnSync(process.execPath, [...process.execArgv, process.argv[1] ?? ""], {
    env: {
      ...process.env,
      SOUND_BENCH_ONCE: "1",
      SOUND_BENCH_K: String(maxK),
      SOUND_BENCH_SOUND: sound ? "1" : "0",
    },
    encoding: "utf8",
  });
  if (child.status !== 0) throw new Error(child.stderr || `bench child exited ${child.status}`);
  const line = child.stdout.trim().split("\n").pop() ?? "";
  const parsed = JSON.parse(line) as { ms: number; pool: number; sound: SoundReport | null };
  return { ms: parsed.ms, pool: parsed.pool, report: parsed.sound };
}

type Row = {
  k: number;
  defaultMs: number;
  soundMs: number;
  defaultPool: number;
  soundPool: number;
  report: SoundReport;
};

const rows: Row[] = [];
for (const k of KS) {
  const plain: number[] = [];
  const sound: number[] = [];
  let report: SoundReport | null = null;
  let defaultPool = 0;
  let soundPool = 0;
  for (let run = 0; run < RUNS; run += 1) {
    const left = time(k, false);
    const right = time(k, true);
    plain.push(left.ms);
    sound.push(right.ms);
    defaultPool = left.pool;
    soundPool = right.pool;
    report = right.report;
  }
  if (!report) throw new Error("sound report missing");
  rows.push({
    k,
    defaultMs: median(plain),
    soundMs: median(sound),
    defaultPool,
    soundPool,
    report,
  });
  console.error(`K=${k} default ${median(plain).toFixed(0)} ms, sound ${median(sound).toFixed(0)} ms`);
}

console.log("| K | default ms | sound ms | overhead | default pool | sound pool | nominations | confirmations | rejections | distinct | exact checks |");
console.log("| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
for (const row of rows) {
  const overhead = row.soundMs / row.defaultMs;
  console.log(
    `| ${row.k} | ${row.defaultMs.toFixed(0)} | ${row.soundMs.toFixed(0)} | ${overhead.toFixed(2)}× | ${row.defaultPool} | ${row.soundPool} | ${row.report.nominations} | ${row.report.confirmations} | ${row.report.rejections} | ${row.report.distinct} | ${row.report.exactChecks} |`,
  );
}

console.log("");
console.log("Escalation is the share of clean candidates sent to at least one exact comparison.");
console.log("");
console.log("| K | level | candidates | escalated | rate |");
console.log("| ---: | ---: | ---: | ---: | ---: |");
for (const row of rows) {
  for (const level of row.report.escalation) {
    const rate = level.candidates === 0 ? 0 : level.escalated / level.candidates;
    console.log(`| ${row.k} | ${level.k} | ${level.candidates} | ${level.escalated} | ${(100 * rate).toFixed(1)}% |`);
  }
}
