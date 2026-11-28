import { LEAN_VERIFIED_THEOREMS } from "../export";
import { SHORT_PROGRAMS } from "../programs";
import type { CheckModule } from "./_types";

/**
 * Every closed word in best-known.json has a Lean theorem link. A new stored word
 * without a proof fails here, so the "every record is machine-checked" claim in
 * formal/lean/README.md cannot silently go stale. The Lean CI (lean.yml) checks
 * that each linked theorem exists and applies to exactly that word.
 */
const checkModule: CheckModule = {
  id: 112,
  weight: 50,
  run(ctx) {
    const linked = new Set(Object.keys(LEAN_VERIFIED_THEOREMS));
    const missing = Object.entries(SHORT_PROGRAMS)
      .filter(([, word]) => !/[xy]/.test(word) && !linked.has(word))
      .map(([id, word]) => `${id} (K ${word.length})`);
    if (missing.length > 0) ctx.fail(`FAIL stored words with no Lean theorem link: ${missing.join(", ")}`);
  },
};

export default checkModule;
