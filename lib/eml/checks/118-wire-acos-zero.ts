import { compileSubmission } from "../../../components/submitTurn";
import { exactReport, formatExact } from "../exact";
import { reportUnpacked } from "../packed-eval";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * acos of a computed exact 0 is π/2. The arcsin series of that 0 used to
 * stamp the shared integer 0 unverified. In-process, π/2 − 0 folded back to
 * the half already built, so the certificate stood. The worker rebuilds that
 * half after the mark, so the same digits came back unverified.
 */
const sources = ["acos((-1)*(-0))", "acos(((-1+10^(-120)*i)*(-0)))"];
const want = "1.570796326795";

const checkModule: CheckModule = {
  id: 118,
  weight: 200,
  run(ctx) {
    for (const source of sources) {
      const { node } = compileSubmission(source, "", "");
      const app = exactReport(node, {}, { maxNodes: 80_000 });
      const packed = packCircuit(node);
      const wire = reportUnpacked(packed.tokens, packed.root).report;
      const appText = app.unverified ? "unverified" : formatExact(app.value);
      const wireText = wire.unverified ? "unverified" : formatExact(wire.value);
      if (appText !== want || wireText !== appText || app.singular !== wire.singular) {
        ctx.fail("FAIL acos of exact zero", source, "app", appText, app.singular, "wire", wireText, wire.singular, "want", want);
      }
    }
  },
};

export default checkModule;
