import { layoutBinaryTree, nodeToEmlExpr, nodeToLatex, nodeToLean4, traceRpnSteps } from "../export";
import { searchNearestConstant } from "../golf";
import { E, ONE, nodeFromRpn } from "../node";
import type { CheckModule } from "./_types";

/**
 * Formula exporters (EML, LaTeX, Lean 4), step-by-step RPN trace,
 * binary tree layout, and nearest-constant target finder.
 */
const checkModule: CheckModule = {
  id: 105,
  weight: 80,
  run(ctx) {
    const assert = (label: string, ok: boolean, detail?: string) => {
      if (!ok) ctx.fail(`FAIL ${label}${detail ? ` (${detail})` : ""}`);
    };

    // Export formats for e = eml(1, 1) and 0 = eml(1, eml(eml(1, 1), 1))
    const eNode = E(ONE, ONE);
    const zeroNode = nodeFromRpn("111E1EE".split(""));

    assert("nodeToEmlExpr(e)", nodeToEmlExpr(eNode) === "eml(1, 1)");
    assert("nodeToLean4(e)", nodeToLean4(eNode) === "eml 1 1");
    assert("nodeToLatex(e)", nodeToLatex(eNode) === "\\exp\\!\\left(1\\right) - \\ln\\!\\left(1\\right)");

    assert("nodeToEmlExpr(0)", nodeToEmlExpr(zeroNode) === "eml(1, eml(eml(1, 1), 1))");
    assert("nodeToLean4(0)", nodeToLean4(zeroNode) === "eml 1 (eml (eml 1 1) 1)");
    assert("nodeToLatex(0)", typeof nodeToLatex(zeroNode) === "string" && nodeToLatex(zeroNode)!.includes("\\ln"));

    // Step-by-step RPN trace for 0 = 111E1EE (binary 1110100)
    const steps = traceRpnSteps("1110100");
    assert("traceRpnSteps length is K+1", steps.length === 8, `got ${steps.length}`);
    assert("traceRpnSteps step 0 empty", steps[0]?.depth === 0 && steps[0]?.top === "empty");
    assert("traceRpnSteps step 3 depth 3", steps[3]?.depth === 3 && steps[3]?.token === "1");
    assert(
      "traceRpnSteps step 4 builds e",
      steps[4]?.depth === 2 && steps[4]?.token === "E" && Boolean(steps[4]?.top.startsWith("2.718")),
    );
    assert("traceRpnSteps final step builds 0", steps[7]?.depth === 1 && steps[7]?.top === "0");

    // Binary tree layout for 0 = 111E1EE
    const layout = layoutBinaryTree("111E1EE");
    assert("layoutBinaryTree node count", layout.nodes.length === 7, `got ${layout.nodes.length}`);
    assert("layoutBinaryTree edge count", layout.edges.length === 6, `got ${layout.edges.length}`);
    assert("layoutBinaryTree leaf count", layout.leafCount === 4, `got ${layout.leafCount}`);
    assert("layoutBinaryTree maxDepth", layout.maxDepth === 3, `got ${layout.maxDepth}`);

    // Nearest-constant search (symbolic regression / constant finder)
    const nearE = searchNearestConstant(Math.E, 0, 11, { limit: 3 });
    assert(
      "searchNearestConstant(e) finds K=3 exact",
      nearE.hits[0]?.k === 3 && nearE.hits[0]?.rpn === "11E" && (nearE.hits[0]?.absError ?? 1) < 1e-14,
    );

    const nearZero = searchNearestConstant(0, 0, 11, { limit: 3 });
    assert(
      "searchNearestConstant(0) finds K=7 exact",
      nearZero.hits[0]?.k === 7 && nearZero.hits[0]?.rpn === "111E1EE" && (nearZero.hits[0]?.absError ?? 1) < 1e-14,
    );

    // Golden ratio approximation within K <= 15 should get within ~0.03!
    const phi = (1 + Math.sqrt(5)) / 2;
    const nearPhi = searchNearestConstant(phi, 0, 15, { limit: 3 });
    assert(
      "searchNearestConstant(phi, K<=15) finds close hit",
      nearPhi.hits.length === 3 && (nearPhi.hits[0]?.absError ?? 1) < 0.03,
      `best err=${nearPhi.hits[0]?.absError}`,
    );
  },
};

export default checkModule;
