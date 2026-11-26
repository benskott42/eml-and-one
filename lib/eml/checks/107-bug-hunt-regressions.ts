import { exactReport, formatExact } from "../exact";
import { nodeToLatex, nodeToLean4 } from "../export";
import { clearProvenInt, isUnverified, learn, markUnverified, provenInteger } from "../facts";
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

    // 4. Huge scientific literals (1e-999999, 1e999999) must compile instantly (no O(n^2) BigInt hang)
    const t0 = performance.now();
    const tinyNode = compileExpression("1e-999999", {});
    const hugeNode = compileExpression("1e999999", {});
    const compileMs = performance.now() - t0;
    const tinyRep = exactReport(tinyNode);
    const hugeRep = exactReport(hugeNode);
    assert(
      "1e-999999 & 1e999999 compile fast and evaluate accurately",
      compileMs < 5000 && formatExact(tinyRep.value) === "1×10^−999999" && formatExact(hugeRep.value) === "1×10^999999",
      `compileMs=${Math.round(compileMs)}ms tiny=${formatExact(tinyRep.value)} huge=${formatExact(hugeRep.value)}`,
    );

    // 5. clearProvenInt preserves non-integer facts such as unverified
    const probe = E(ONE, E(ONE, ONE));
    learn(probe, { integer: { value: BigInt(42) } });
    markUnverified(probe);
    clearProvenInt(probe);
    assert(
      "clearProvenInt clears integer while preserving unverified",
      provenInteger(probe) === undefined && isUnverified(probe) === true,
    );

    // 6. Series-shortcut error bounds survive algebraic cancellation AND scale amplification (*, /, exp)
    for (const expr of [
      "sinh(1e-7) - (1e-7 + 1e-25)",
      "atanh(1e-7) - (1e-7 + 1e-25)",
      "(sinh(1e-7) + 1e-25) - 1e-7",
      "(atanh(1e-7) + 1e-25) - 1e-7",
      "(sinh(1e-7) - (1e-7 + 1e-25)) * 1e20",
      "(sinh(1e-7) * 1e20) - (1e13 + 1e-5)",
      "exp(sinh(1e-7) * 1e20)",
    ]) {
      const rep = exactReport(compileExpression(expr, {}));
      assert(`${expr} must be refused (contaminated by dropped z^3 term)`, rep.unverified === true, `got ${formatExact(rep.value)}`);
    }
  },
};

export default checkModule;
