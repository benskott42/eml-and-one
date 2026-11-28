import { compileSubmission } from "../../../components/submitTurn";
import { exactReport, formatExact } from "../exact";
import { reportUnpacked } from "../packed-eval";
import { packCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * acos of a real exact 0 is π/2. The arcsin series of that 0 used to stamp
 * the shared integer 0 unverified. In-process, π/2 − 0 folded back to the
 * half already built, so the certificate stood. The worker rebuilds that
 * half after the mark, so the same digits came back unverified.
 * A signed zero times a non-real factor is unverified on purpose, so acos of
 * that product is unverified on both paths and does not touch the shared 0.
 */
const kept = ["acos((-1)*(-0))"];
const refused = ["acos(((-1+10^(-120)*i)*(-0)))"];
const want = "1.570796326795";

function report(source: string): { app: string; wire: string; appNote: string | null; wireNote: string | null } {
  const { node } = compileSubmission(source, "", "");
  const app = exactReport(node, {}, { maxNodes: 80_000 });
  const packed = packCircuit(node);
  const wire = reportUnpacked(packed.tokens, packed.root).report;
  return {
    app: app.unverified ? "unverified" : formatExact(app.value),
    wire: wire.unverified ? "unverified" : formatExact(wire.value),
    appNote: app.singular,
    wireNote: wire.singular,
  };
}

const checkModule: CheckModule = {
  id: 118,
  weight: 200,
  run(ctx) {
    for (const source of kept) {
      const got = report(source);
      if (got.app !== want || got.wire !== got.app || got.appNote !== got.wireNote) {
        ctx.fail("FAIL acos of exact zero", source, "app", got.app, got.appNote, "wire", got.wire, got.wireNote, "want", want);
      }
    }
    for (const source of refused) {
      const got = report(source);
      if (got.app !== "unverified" || got.wire !== "unverified") {
        ctx.fail("FAIL acos of non-real zero", source, "app", got.app, "wire", got.wire);
      }
    }
  },
};

export default checkModule;
