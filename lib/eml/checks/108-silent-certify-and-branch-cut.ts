import { noteFor, type Entry } from "../../../components/calculator/entry";
import { exactReport, exactToFloat, formatExact } from "../exact";
import { tMul } from "../library";
import { compileExpression } from "../parse";
import { nodeFromCompact } from "../programs";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Regressions for exact-mode tower impostors (A) and negative-real-axis branch-cut notes (B):
 * A. Deep towers whose extra term is absorbed past working precision (111E1E1E1EE11EE,
 *    111E1E1E1EE1E1E, 111111EEEE1E1E1EE11EE), sits inside the exactInteger dust band
 *    (1111EE1E1E1EE11EE), overflows/underflows decimal.js range (111E1E1E1E1EE1E), or
 *    triggers a huge trig angle (11E1E1111E1E1EEEE1E1E) must be refused ("couldn't verify")
 *    rather than certified as an exact integer or crashing. True exact tower cancellations
 *    (11E1E11E1E1E1EE = 0, 11E1E11E1E1E1EE1E = 1) remain certified.
 * B. Words whose displayed imaginary part comes from the lower-cut convention on the
 *    negative real axis (111111E1EEEE11E1E1EEE, ln(-1), ln(-2)) set `nearCut: true` in
 *    exact mode and render "on or very near the branch cut" in `noteFor`. Values off the
 *    cut (ln(-2 - 10^(-20)*i)) or real results (exp(ln(-1))) do not.
 */
const checkModule: CheckModule = {
  id: 108,
  weight: 500,
  run(ctx) {
    const assert = (label: string, ok: boolean, detail?: string) => {
      if (!ok) ctx.fail(`FAIL ${label}${detail ? ` (${detail})` : ""}`);
    };

    // A1. Tower impostors must never certify as exact integers or crash (direct & wire)
    const towerImpostors = [
      "111E1E1E1EE11EE",       // -1 + e/T4 (~10^-1656520)
      "111E1E1E1EE1E1E",       // 1 + e/T4 (~10^-1656520)
      "111E1E1E1E1EE1E",       // exp(e - T4) (~10^(-10^1656520), decimal overflow in T5)
      "1111E1E1E1E1EEE1E",     // -e/(T4 - e) (decimal overflow in T5)
      "1111EE1E1E1EE11EE",     // -1 + 4.388e-116 (inside exactInteger dust band)
      "1111EE1E1E1EE1E1E",     // 1 + 4.388e-116
      "1111EE1E1E1EE1E11EE1E", // exp(exp(4.388e-116) - 1) = 1 + 4.388e-116 (snapped inner cancel)
      "111111EEEE1E1E1EE11EE", // -1 + O(10^-456)
      "11E111E1E1EEE1E11EE",   // -1 + O(10^-133203) without passing through T4
      "11E1E1111E1E1EEEE1E1E", // huge trig angle past PI_PRECISION (must refuse, not throw)
    ];
    for (const word of towerImpostors) {
      const node = nodeFromCompact(word);
      const packed = packCircuit(node);
      const wireNode = unpackCircuit(packed.tokens, packed.root);
      for (const [label, target] of [
        ["direct", node],
        ["wire", wireNode],
      ] as const) {
        const rep = exactReport(target, {}, { maxNodes: 80_000 });
        assert(
          `impostor ${word} (${label}) refused`,
          rep.unverified === true,
          `got ${formatExact(rep.value)} sing=${rep.singular}`,
        );
      }
    }

    // A2. Genuine exact tower cancellations remain certified
    const trueTowers: [string, string][] = [
      ["11E1E11E1E1E1EE", "0"],   // exp(T2) - ln(T4) = T3 - T3 = 0
      ["11E1E11E1E1E1EE1E", "1"], // exp(T3 - T3) = 1
    ];
    for (const [word, want] of trueTowers) {
      const rep = exactReport(nodeFromCompact(word), {}, { maxNodes: 80_000 });
      assert(
        `exact tower ${word} => ${want}`,
        !rep.unverified && formatExact(rep.value) === want,
        `got ${rep.unverified ? "unverified" : formatExact(rep.value)}`,
      );
    }

    // A3. Underflow-lost non-finite results and scaled pure tower impostors below 1e-6 stay refused
    for (const expr of ["ln(exp(-1e20))", "1 / exp(-1e20)", "exp(-1e20)^(-1)", "ln(1 / exp(-1e20))"]) {
      const rep = exactReport(compileExpression(expr, {}), {}, { maxNodes: 80_000 });
      assert(`underflow-lost ${expr} refused`, rep.unverified === true, `certified ${formatExact(rep.value)}`);
    }
    const scaledTowerRep = exactReport(tMul(nodeFromCompact("111E1E1E1EE11EE"), compileExpression("1e-7", {})), {}, { maxNodes: 80_000 });
    assert(
      "scaled pure tower impostor below 1e-6 refused",
      scaledTowerRep.unverified === true,
      `certified ${formatExact(scaledTowerRep.value)}`,
    );

    // B1. Words on the negative real axis carry nearCut in exact mode and noteFor
    const cutWords: [string, ReturnType<typeof nodeFromCompact>][] = [
      ["111111E1EEEE11E1E1EEE", nodeFromCompact("111111E1EEEE11E1E1EEE")],
      ["ln(-1)", compileExpression("ln(-1)", {})],
      ["ln(-2)", compileExpression("ln(-2)", {})],
    ];
    for (const [label, node] of cutWords) {
      const packed = packCircuit(node);
      const wireNode = unpackCircuit(packed.tokens, packed.root);
      for (const [pathLabel, target] of [
        ["direct", node],
        ["wire", wireNode],
      ] as const) {
        const rep = exactReport(target, {}, { maxNodes: 80_000 });
        assert(
          `${label} (${pathLabel}) nearCut=true`,
          !rep.unverified && rep.nearCut === true,
          `got ${formatExact(rep.value)} nearCut=${rep.nearCut} unv=${rep.unverified}`,
        );
        const item: Entry = {
          node: target,
          caption: label,
          mode: "exact",
          value: exactToFloat(rep.value),
          text: formatExact(rep.value),
          singular: rep.singular,
          touchedLn0: rep.touchedLn0,
          nearCut: rep.nearCut === true,
        };
        const note = noteFor(item) ?? "";
        assert(
          `${label} (${pathLabel}) noteFor includes branch-cut note`,
          note.includes("on or very near the branch cut"),
          `got note="${note}"`,
        );
      }
    }

    // B2. Values off the cut or whose imaginary part is not from the lower cut do NOT set nearCut
    const nonCutCases: [string, ReturnType<typeof compileExpression>][] = [
      ["ln(-2 - 10^(-20)*i)", compileExpression("ln(-2 - 10^(-20)*i)", {})],
      ["exp(ln(-1))", compileExpression("exp(ln(-1))", {})],
      ["i", compileExpression("i", {})],
      ["pi", compileExpression("pi", {})],
    ];
    for (const [label, node] of nonCutCases) {
      const rep = exactReport(node, {}, { maxNodes: 80_000 });
      assert(
        `${label} nearCut=false`,
        !rep.unverified && rep.nearCut !== true,
        `got ${formatExact(rep.value)} nearCut=${rep.nearCut}`,
      );
    }
  },
};

export default checkModule;
