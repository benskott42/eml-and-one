import { exactReport, formatExact } from "../exact";
import { formatC } from "../format";
import { SINGULAR_LN0, evaluateReport } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * Signed zero after a constant word is tagged as an exact point.
 * A negative non-integer times +0 stays +0 (the product program's sign).
 * A proven negative integer times +0 stays −0. Division by either zero,
 * and ln of either zero, keep the ln 0 note. Composed ln(−0) is −∞ + iπ.
 */
const rows: Array<[string, string, string, string | null]> = [
  ["(1/3-1)*0", "0", "0", null],
  ["1/((1/3-1)*0)", "∞", "∞", SINGULAR_LN0],
  ["ln(0*(1/3-1))", "−∞", "−∞", SINGULAR_LN0],
  ["(-ln(2))*0", "0", "0", null],
  ["ln(0*(-ln(2)))", "−∞", "−∞", SINGULAR_LN0],
  ["ln(-0)", "−∞ + 3.14159265359i", "−∞ + 3.14159265359i", SINGULAR_LN0],
  ["(-2)*0", "−0", "−0", null],
  ["1/(-2*0)", "−∞", "−∞", SINGULAR_LN0],
];

const checkModule: CheckModule = {
  id: 117,
  weight: 250,
  run(ctx) {
    for (const [source, floatText, exactText, note] of rows) {
      const node = compileExpression(source, {});
      const floated = evaluateReport(node);
      const exact = exactReport(node, {}, { maxNodes: 80_000 });
      const gotFloat = formatC(floated.value);
      const gotExact = exact.unverified ? "unverified" : formatExact(exact.value);
      if (gotFloat !== floatText || floated.singular !== note) {
        ctx.fail("FAIL signed zero float", source, gotFloat, floated.singular, "want", floatText, note);
      }
      if (gotExact !== exactText || exact.singular !== note) {
        ctx.fail("FAIL signed zero exact", source, gotExact, exact.singular, "want", exactText, note);
      }
    }
  },
};

export default checkModule;
