/**
 * Full containment sample for the 300-digit balls in lib/eml/enclose.ts:
 * 3010 exp points, 2004 ln points, the stretch and cut-edge balls, and every pure
 * circuit with up to 8 leaves (626). lib/eml/check.ts runs a smaller prefix.
 *
 *   npx tsx scripts/enclose-containment.ts
 */
import { FULL_SAMPLE, runEncloseChecks } from "../lib/eml/check-enclose";

const started = performance.now();
const failed = runEncloseChecks(FULL_SAMPLE);
console.log(failed ? `enclose containment: ${failed} failed` : "enclose containment passed", `${Math.round((performance.now() - started) / 1000)}s`);
process.exit(failed ? 1 : 0);
