import { exactReport, formatExact } from "../exact";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * tan(acos(x)) for a small positive x is the real number cot(asin(x)).
 * The exp form of tan dropped x² near π/2, so exact mode certified a spurious
 * imaginary part (tan(acos(10^(−30))) was 10^30 − 10^(−60)i, tan(acos(10^(−60)))
 * was 10^60 − i) and, once x fell inside the quarter-turn snap, a pole
 * (tan(acos(10^(−120))) was undefined). The true values are 10^30, 10^60 and 10^120.
 */
const checkModule: CheckModule = {
  id: 117,
  weight: 15000,
  run(ctx) {
    const rows: [string, string][] = [
      ["tan(acos(1e-30))", "1×10^30"],
      ["tan(acos(1e-60))", `1${"0".repeat(60)}`],
      ["tan(acos(1e-120))", "1×10^120"],
    ];
    for (const [src, want] of rows) {
      const rep = exactReport(compileExpression(src, {}), {}, { maxNodes: 200_000 });
      const got = formatExact(rep.value).replace(/\u200b/g, "");
      if (rep.unverified || got !== want) {
        ctx.fail(`FAIL ${src} got=${rep.unverified ? "unverified" : got} want=${want}`);
      }
    }
    // x² for x = 10^(−250) does not fit in 480 digits, so the lost square must not
    // be certified as a real 1 beside 10^250. A refusal, or the real value, is honest.
    const past = exactReport(compileExpression("tan(acos(1e-250))", {}), {}, { maxNodes: 200_000 });
    const pastText = formatExact(past.value).replace(/\u200b/g, "");
    if (!past.unverified && pastText.includes("i")) {
      ctx.fail(`FAIL tan(acos(1e-250)) certified a spurious imaginary part: ${pastText}`);
    }
  },
};

export default checkModule;
