import { exactReport, formatExact } from "../exact";
import { formatC } from "../format";
import { SINGULAR_LN0, evaluateReport, type Node } from "../node";
import { compileExpression } from "../parse";
import { packCircuit } from "../wire";
import { reportUnpacked } from "../packed-eval";
import type { CheckModule } from "./_types";

/**
 * IEEE: the sign of 0·a is the sign of a, for a literal, a computed value,
 * or a variable bound to either. Division by that zero keeps the ln 0 note.
 * An enclosure that does not decide the sign is refused.
 * Composed ln(−0) stays −∞ + iπ.
 */
const rows: Array<[string, string, string, string | null]> = [
  ["(1/3-1)*0", "−0", "−0", null],
  ["1/((1/3-1)*0)", "−∞", "−∞", SINGULAR_LN0],
  ["ln(0*(1/3-1))", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(-ln(2))*0", "−0", "−0", null],
  ["ln(0*(-ln(2)))", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["ln(-0)", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(-2)*0", "−0", "−0", null],
  ["1/(-2*0)", "−∞", "−∞", SINGULAR_LN0],
  ["1/(-((ln(1/3))*0))", "∞", "∞", SINGULAR_LN0],
  ["ln((ln(1/3))*0)", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(1/(-3/2))*0", "−0", "−0", null],
  ["((-1/2)/2)*0", "−0", "−0", null],
  ["(-ln(2)/2)*0", "−0", "−0", null],
  ["((-e)/2)*0", "−0", "−0", null],
  ["(2/(-0.5))*0", "−0", "−0", null],
    ["(atan(-3))*0", "−0", "−0", null],
  ["((-2/3)*0)*((-2/3)*0)", "0", "0", null],
  ["((-2/3)*0)^-1", "−∞", "−∞", SINGULAR_LN0],
  ["i/((1/3-1)*0)", "−∞i", "−∞i", SINGULAR_LN0],
  ["-(((-2/3)*0)*((e*0)*(-3/2)))", "−0", "−0", null],
  ["(((0)*0*(-3/2))*0*(atan(-2/3)))+((-ln(2)/2)*0)", "0", "0", null],
  ["0*cos(1)", "0", "0", null],
  ["0*cos(2)", "−0", "−0", null],
  ["(-0)+(-0)", "−0", "−0", null],
  ["0+(-0)", "0", "0", null],
];

function show(node: Node): { float: string; exact: string; floatNote: string | null; exactNote: string | null; floatUnverified: boolean; exactUnverified: boolean } {
  const floated = evaluateReport(node);
  const exact = exactReport(node, {}, { maxNodes: 80_000 });
  return {
    float: formatC(floated.value),
    exact: exact.unverified ? "unverified" : formatExact(exact.value),
    floatNote: floated.singular,
    exactNote: exact.singular,
    floatUnverified: floated.unverified === true,
    exactUnverified: exact.unverified === true,
  };
}

const checkModule: CheckModule = {
  id: 117,
  weight: 800,
  run(ctx) {
    for (const [source, floatText, exactText, note] of rows) {
      const got = show(compileExpression(source, {}));
      if (got.floatUnverified || got.float !== floatText || got.floatNote !== note) {
        ctx.fail("FAIL signed zero float", source, got.float, got.floatNote, got.floatUnverified, "want", floatText, note);
      }
      if (got.exactUnverified || got.exact !== exactText || got.exactNote !== note) {
        ctx.fail("FAIL signed zero exact", source, got.exact, got.exactNote, "want", exactText, note);
      }
    }

    // The same negative, built three ways, is the same −0, and 1 over it is −∞.
    const factors = ["-3/2", "1/(-3/2)", "atan(-3)"];
    for (const factor of factors) {
      const literal = compileExpression(`(${factor})*0`, {});
      const reciprocal = compileExpression(`1/((${factor})*0)`, {});
      const bound = compileExpression(factor, {});
      const variable = compileExpression("x*0", { x: bound });
      const variableReciprocal = compileExpression("1/(x*0)", { x: bound });
      for (const [label, node] of [
        ["product", literal],
        ["variable", variable],
      ] as const) {
        const got = show(node);
        if (got.float !== "−0" || got.exact !== "−0" || got.floatNote !== null || got.exactNote !== null || got.floatUnverified || got.exactUnverified) {
          ctx.fail("FAIL signed zero path", factor, label, got.float, got.exact, got.floatNote, got.exactNote);
        }
      }
      for (const [label, node] of [
        ["reciprocal", reciprocal],
        ["variable reciprocal", variableReciprocal],
      ] as const) {
        const got = show(node);
        if (got.float !== "−∞" || got.exact !== "−∞" || got.floatNote !== SINGULAR_LN0 || got.exactNote !== SINGULAR_LN0) {
          ctx.fail("FAIL signed zero reciprocal", factor, label, got.float, got.exact, got.floatNote, got.exactNote);
        }
      }
    }

    const atan = compileExpression("(atan(-3))*0", {});
    const packed = packCircuit(atan);
    const wire = reportUnpacked(packed.tokens, packed.root).report;
    const wireText = wire.unverified ? "unverified" : formatExact(wire.value);
    if (wireText !== "−0" || wire.singular !== null) {
      ctx.fail("FAIL atan zero wire", wireText, wire.singular);
    }

    // 1 − cos(0) is the real 0, but that factor records no sign. 0 times it
    // must be refused rather than printed as a certified zero.
    const refused = show(compileExpression("0*(1-1*cos(0))", {}));
    if (!refused.floatUnverified || !refused.exactUnverified) {
      ctx.fail("FAIL uncertified sign", refused.float, refused.floatUnverified, refused.exact, refused.exactUnverified);
    }
  },
};

export default checkModule;
