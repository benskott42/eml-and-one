import type { CheckModule } from "./_types";
import { branchChecks, runPropertyChecks } from "../check-properties";
import { runCertifyChecks } from "../check-certify";

/**
 * Algebraic property checks, branch-cut checks, and certification suite.
 */
const checks: CheckModule[] = [
  {
    id: 44,
    weight: 16515,
    run(ctx) {
      ctx.addFailures?.(runPropertyChecks());
    },
  },
  {
    id: 66,
    weight: 14840,
    run(ctx) {
      ctx.addFailures?.(branchChecks());
    },
  },
  {
    id: 45,
    weight: 33477,
    run(ctx) {
      ctx.addFailures?.(runCertifyChecks());
    },
  },
];

export default checks;
