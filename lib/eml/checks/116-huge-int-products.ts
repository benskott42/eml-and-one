import { entry } from "../../../components/calculator/entry";
import { compileSubmission } from "../../../components/submitTurn";
import { exactReport, formatExact } from "../exact";
import { intDecade } from "../facts";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * Exact integers in a circuit stay bounded (found by tools/fuzz/parse-fuzz.ts, seed 3).
 * x·x·…·x with x = 1e1000000 multiplied ever larger exact integers and counted each
 * one's decimal digits, and compiling 40 factors took 32 s on the page's main thread.
 * Products now stay exact up to about 2.1 million digits (twice the largest literal)
 * and digits are counted from the bit length (intDecade). Exact answers that need
 * literal-sized integers are unchanged.
 */
const exactRows: [string, string][] = [
  ["(10^1000+1)*(10^1000-1)-10^2000", "−1"],
  ["(1e30000+1)-1e30000", "1"],
  ["1e7000*1e7000-1e14000", "0"],
  ["(1e7000*1e7000+1)-1e7000*1e7000", "1"],
];

const checkModule: CheckModule = {
  id: 116,
  weight: 6000,
  run(ctx) {
    // floor(log10 n) at and around powers of ten, past the decimal-conversion threshold.
    for (const k of [1, 1899, 1900, 2500, 30000]) {
      const p = BigInt(10) ** BigInt(k);
      for (const n of [p, p - BigInt(1), p + BigInt(1), p * BigInt(9), BigInt(2) * p - BigInt(1)]) {
        const want = n.toString().length - 1;
        const got = intDecade(n);
        if (got !== want) ctx.fail(`FAIL intDecade of a ${want + 1}-digit integer: ${got}`);
      }
    }
    // The chain that took 32 s: generous bound so a slow runner does not flake.
    const text = Array.from({ length: 40 }, () => "x").join("*");
    const t0 = performance.now();
    const { node, numbers } = compileSubmission(text, "1e1000000", "1");
    entry(node, text, "float", numbers);
    const ms = performance.now() - t0;
    if (ms > 10_000) ctx.fail(`FAIL x^40 as a product with x = 1e1000000 took ${Math.round(ms)} ms to compile`);
    for (const [source, want] of exactRows) {
      const r = exactReport(compileExpression(source, {}));
      const got = r.unverified ? "could not verify" : formatExact(r.value);
      if (got !== want) ctx.fail(`FAIL ${source}: ${got}, want ${want}`);
    }
    console.log("huge integer products", `x^40 product compiled in ${Math.round(ms)} ms`);
  },
};

export default checkModule;
