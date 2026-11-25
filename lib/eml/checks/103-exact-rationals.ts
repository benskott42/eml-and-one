import { exactFractionNote } from "../../../components/calculator/entry";
import { exactReport, formatExact } from "../exact";
import { exactRationalOf, isRecognized } from "../facts";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Exact rational tracking beyond terminating decimals: sums, differences,
 * products, quotients, integer powers, rational π-multiples, and wire round-trips.
 */
const checkModule: CheckModule = {
  id: 103,
  weight: 200,
  run(ctx) {
    const exactZeros = [
      "1/3 + 2/3 - 1",
      "1/6 + 1/3 - 1/2",
      "(1/3)*3 - 1",
      "1/7 + 6/7 - 1",
      "(2/3)^2 - 4/9",
      "(1/3)^(-1) - 3",
      "(1/3 + 2/3)*0.5 - 0.5",
      "(1/3 - 1/6) - 1/6",
      "((1/3) / (2/3)) - 0.5",
      "log(2, 8) - 3",
      "log(10, 1000) - 3",
      "log(1/2, 4) + 2",
      "log(2, 1/8) + 3",
      "log(4, 8) - 3/2",
      "log(8, 2) - 1/3",
    ];
    for (const src of exactZeros) {
      const node = compileExpression(src, {});
      const packed = packCircuit(node);
      const wireNode = unpackCircuit(packed.tokens, packed.root);
      for (const [label, target] of [
        ["direct", node],
        ["wire", wireNode],
      ] as const) {
        const rep = exactReport(target, {}, { maxNodes: 800_000 });
        const got = formatExact(rep.value);
        if (rep.unverified || got !== "0") {
          ctx.fail(`FAIL exact-rational-zero ${label} ${src} got=${rep.unverified ? "unverified" : got}`);
        }
      }
    }

    // Rational facts survive wire serialization on non-zero rationals too.
    const thirdNode = compileExpression("1/3", {});
    const thirdWire = unpackCircuit(packCircuit(thirdNode).tokens, packCircuit(thirdNode).root);
    const q1 = exactRationalOf(thirdNode);
    const q2 = exactRationalOf(thirdWire);
    if (!q1 || q1.n !== BigInt(1) || q1.d !== BigInt(3) || !q2 || q2.n !== BigInt(1) || q2.d !== BigInt(3)) {
      ctx.fail(`FAIL exact-rational-wire 1/3 direct=${JSON.stringify(q1)} wire=${JSON.stringify(q2)}`);
    }

    // Rational multiples of π recognize cleanly via angleOf.
    const angleRows: [string, string][] = [
      ["cos((1/3)*pi)", "0.5"],
      ["sin((1/6)*pi)", "0.5"],
      ["cos((2/3)*pi)", "−0.5"],
      ["sin((5/6)*pi)", "0.5"],
      ["cos(pi / (3/2))", "−0.5"],
    ];
    for (const [src, want] of angleRows) {
      const node = compileExpression(src, {});
      const rep = exactReport(node, {}, { maxNodes: 800_000 });
      const got = formatExact(rep.value);
      if (rep.unverified || got !== want || !isRecognized(node)) {
        ctx.fail(`FAIL exact-rational-angle ${src} got=${rep.unverified ? "unverified" : got} want=${want} recognized=${isRecognized(node)}`);
      }
    }
    // UI exact fraction note: shows `= n/d` for non-terminating rationals, null for integers/terminating decimals.
    const fracNotes: [string, string | null][] = [
      ["1/3", "= 1/3"],
      ["-2/3", "= −2/3"],
      ["(2/3)^2", "= 4/9"],
      ["log(8, 2)", "= 1/3"],
      ["1/2", null],
      ["1/3 + 2/3", null],
      ["1/3 + 1/6", null],
    ];
    for (const [src, want] of fracNotes) {
      const got = exactFractionNote(compileExpression(src, {}));
      if (got !== want) {
        ctx.fail(`FAIL exact-fraction-note ${src} got=${got} want=${want}`);
      }
    }
  },
};

export default checkModule;
