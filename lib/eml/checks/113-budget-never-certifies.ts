import { exactReport, formatExact } from "../exact";
import { EmlLimitError } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * Running out of budget is never a certificate. With a deadline,
 * (−5 − 10^(−300) i) − (10^(−236) + 10^(−236) i) timed out inside the tiny-part
 * recovery and was certified as −5, dropping −10^(−236) i (found by the nightly
 * fuzzer on seed 3). The refinements now rethrow the limit error, and so does the
 * ball enclosure that confirms results far below a value past float range.
 *
 * A fake clock makes this deterministic: the walk reads performance.now() every
 * 32 steps, and each read advances the clock by 1, so `deadline = k` stops the
 * evaluation at its k-th check. For every cut point the result is either the
 * full-budget answer or a limit error, never a different certified value.
 */
const rows = [
  "(-5-10^(-300)*i)-(10^(-236)+10^(-236)*i)",
  "sqrt(-4-i*10^-200)",
  "((1+10^(-136))-1)+i*3/2",
  "ln(ln(-5-i*10^-300))",
  "acos(1-10^-200)",
];

/**
 * Kept only if the ball enclosure confirms it (exact-ball.ts), which runs at the
 * end of the evaluation. A deadline inside the enclosure returned "not confirmed",
 * so 10^(−240) − atanh(exp(800)) said it could not verify under the fuzzer's 10 s
 * budget and certified with more time (seed 74). These rows cut at every clock
 * read near the end, where the enclosure runs.
 */
const tailRows = ["sqrt(4*10^(-400))", "ln(10^(-400))+cos(1)"];
const TAIL = 48;

function withFakeClock<T>(run: () => T): T {
  const real = performance.now.bind(performance);
  let tick = 0;
  Object.defineProperty(performance, "now", { value: () => ++tick, configurable: true, writable: true });
  try {
    return run();
  } finally {
    Object.defineProperty(performance, "now", { value: real, configurable: true, writable: true });
  }
}

const checkModule: CheckModule = {
  id: 113,
  weight: 42000,
  run(ctx) {
    for (const source of [...rows, ...tailRows]) {
      // A fresh circuit per run: the pure-subcircuit cache would otherwise skip the walk.
      const fresh = () => compileExpression(source, {});
      const full = exactReport(fresh());
      const want = full.unverified ? "unverified" : formatExact(full.value);
      // Count the clock reads of a full run, then cut at geometric points below it.
      let reads = 0;
      withFakeClock(() => {
        exactReport(fresh(), {}, { deadline: Number.MAX_SAFE_INTEGER });
        reads = performance.now();
      });
      const cuts = new Set<number>();
      for (let k = 1; k < reads; k = Math.ceil(k * 1.35)) cuts.add(k);
      if (tailRows.includes(source)) for (let k = Math.max(1, reads - TAIL); k < reads; k += 1) cuts.add(k);
      let limited = 0;
      for (const k of cuts) {
        let got: string;
        try {
          const node = fresh();
          const r = withFakeClock(() => exactReport(node, {}, { deadline: k }));
          got = r.unverified ? "unverified" : formatExact(r.value);
        } catch (err) {
          if (err instanceof EmlLimitError) {
            limited += 1;
            continue;
          }
          throw err;
        }
        if (got !== want) ctx.fail(`FAIL budget cut ${source} at check ${k}/${reads}: got ${got}, full budget gives ${want}`);
      }
      console.log("budget cuts", source, `${cuts.size} cuts, ${limited} limit errors, full ${want}`);
    }
  },
};

export default checkModule;
