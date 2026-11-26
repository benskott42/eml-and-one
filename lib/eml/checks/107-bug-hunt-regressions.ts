import { exactReport, formatExact } from "../exact";
import { nodeToLatex, nodeToLean4 } from "../export";
import { E, ONE, nodeFromRpn } from "../node";
import { compileExpression } from "../parse";
import { deriveProof } from "../proof";
import type { CheckModule } from "./_types";

/**
 * Regressions from adversarial bug-hunting waves:
 * - atan(±i) pole detection beyond pointer identity (sqrt(-1), -sqrt(-1), 2*i - i)
 *   so 1 + exp(-atan(sqrt(-1))) never falsely certifies 1
 * - ASCII minus in Lean 4 and LaTeX exports for negative input nodes
 * - Indeterminate ∞ − ∞ rejection in deriveProof
 */
const checkModule: CheckModule = {
  id: 107,
  weight: 60,
  run(ctx) {
    const assert = (label: string, ok: boolean, detail?: string) => {
      if (!ok) ctx.fail(`FAIL ${label}${detail ? ` (${detail})` : ""}`);
    };

    // 1. atan(±i) poles via non-canonical expressions
    for (const [expr, want] of [
      ["atan(sqrt(-1))", "∞i"],
      ["atan(-sqrt(-1))", "−∞i"],
      ["atan(2*i - i)", "∞i"],
      ["atan(i - 2*i)", "−∞i"],
      ["atan(exp(i*pi/2))", "∞i"],
    ] as const) {
      const rep = exactReport(compileExpression(expr, {}));
      const text = formatExact(rep.value);
      assert(`${expr} => ${want}`, text === want, `got ${text} unv=${rep.unverified}`);
    }

    // 1 + exp(-atan(sqrt(-1))) must NOT certify 1 (exp(-∞i) has no limit!)
    const badExp = exactReport(compileExpression("1 + exp(-atan(sqrt(-1)))", {}));
    assert(
      "1 + exp(-atan(sqrt(-1))) must not certify 1",
      Boolean(badExp.unverified || badExp.singular || !badExp.value.re.isFinite()),
      `got ${formatExact(badExp.value)} unv=${badExp.unverified} sing=${badExp.singular}`,
    );

    // 2. Lean 4 and LaTeX exports use ASCII '-' rather than Unicode '−'
    const negInput = { type: "input" as const, value: { re: -3, im: 0 }, label: "-3", id: 999_998 };
    assert("nodeToLean4 uses ASCII minus", nodeToLean4(negInput) === "(-3)", `got ${nodeToLean4(negInput)}`);
    assert("nodeToLatex uses ASCII minus", nodeToLatex(negInput) === "-3", `got ${nodeToLatex(negInput)}`);

    // 3. deriveProof returns null on indeterminate +∞ − +∞
    const zero = nodeFromRpn("111E1EE".split(""));
    const posInf = E(ONE, zero);
    const indet = E(posInf, E(posInf, ONE)); // exp(+∞) - ln(exp(+∞)) -> +∞ - +∞
    assert("deriveProof rejects +∞ − +∞", deriveProof(indet) === null, `got ${deriveProof(indet)?.resultText}`);
  },
};

export default checkModule;
