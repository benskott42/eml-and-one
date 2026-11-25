import { c } from "../complex";
import { exactReport, formatExact } from "../exact";
import { factsOf, learn } from "../facts";
import { applyBinaryNode, applyUnaryNode, integerNode, recognizedNote } from "../library";
import { input, type Node } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * v1.0.4 follow-ups, Step 1c exact-decimal propagation, and Step 3 exact-recognition policy.
 */
const checkModule: CheckModule = {
  id: 99,
  weight: 500,
  run(ctx) {
    // Refused float-0 operands stay refused on keypad builders (exactZero/signedZero/arsinh),
    // (-i)^n and (±1*i)^n resolve via facts.ts, exp(pi/i) resolves, and learn() ignores shared input leaves.
    const bad = compileExpression("(((0.2 + exp(300)) + exp(800)) + 1e310)", {});
    const keypadRefused: [string, Node][] = [
      ["mul", applyBinaryNode("mul", bad, integerNode(5))],
      ["pow", applyBinaryNode("pow", integerNode(5), bad)],
      ["arsinh", applyUnaryNode("arsinh", bad)],
    ];
    for (const [label, node] of keypadRefused) {
      const report = exactReport(node, {}, { maxNodes: 80_000 });
      if (!report.unverified) {
        ctx.fail("FAIL keypad refused zero", label, formatExact(report.value));
      }
    }

    const rows: [string, string][] = [
      ["(-i)^2 + 1", "0"],
      ["(-i)^3", "i"],
      ["(-i)^-1", "i"],
      ["(1*i)^2 + 1", "0"],
      ["((-1)*i)^2 + 1", "0"],
      ["exp(pi/i) + 1", "0"],
      ["exp(pi/(-i)) + 1", "0"],
      ["1/10 + 2/10 - 3/10", "0"],
      ["0.1*3 - 0.3", "0"],
      ["0.5^2 - 0.25", "0"],
      ["cos(0.5*pi)", "0"],
      ["cos((1/2)*pi)", "0"],
      ["sin(0.5*pi)", "1"],
      ["tan(0.25*pi)", "1"],
      ["exp(0.5*pi*i)", "i"],
    ];
    for (const [source, want] of rows) {
      const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
      const got = report.unverified ? "unverified" : formatExact(report.value);
      if (got !== want) {
        ctx.fail("FAIL v1.0.4 followup", source, got, "want", want);
      }
    }

    const leaf = input(c(0, 0), "0");
    learn(leaf, { imaginaryUnit: 1 });
    if (factsOf(leaf).imaginaryUnit !== undefined) {
      ctx.fail("FAIL learn on input leaf");
    }

    // Architecture plan step 3: every exact recognition shows "recognized exactly", and
    // ordinary literals/circuits do not leak the flag from ONE or interned -0.
    const recognizedCases = [
      "2^0",
      "0^0",
      "0^(-0)",
      "i^0",
      "i^1",
      "i^2",
      "i^3",
      "(-i)^3",
      "exp(i*pi)",
      "exp(i*pi/2)",
      "sin(0)",
      "sin(-0)",
      "tan(0)",
      "sinh(0)",
      "tanh(0)",
      "arcsin(0)",
      "arctan(0)",
      "arsinh(0)",
      "artanh(0)",
      "sin(pi/6)",
      "sin(pi/2)",
      "sin(pi)",
      "cos(pi/3)",
      "cos(pi/2)",
      "cos(pi)",
      "tan(pi)",
      "tan(pi/4)",
      "tan(3*pi/4)",
      "arcsin(1)",
      "arcsin(-1)",
      "arccos(1)",
      "arccos(-1)",
      "arsinh(i)",
      "arsinh(-i)",
    ];
    for (const source of recognizedCases) {
      const note = recognizedNote(compileExpression(source, {}));
      if (note !== "recognized exactly") {
        ctx.fail("FAIL recognizedNote missing", source, note);
      }
    }

    const nonRecognizedCases = ["0", "1", "-1", "-0", "1/2", "i", "1+1", "sin(1)", "cos(0)", "2^3", "exp(1)", "ln(-1)"];
    for (const source of nonRecognizedCases) {
      const note = recognizedNote(compileExpression(source, {}));
      if (note !== null) {
        ctx.fail("FAIL recognizedNote leaked", source, note);
      }
    }
  },
};

export default checkModule;
