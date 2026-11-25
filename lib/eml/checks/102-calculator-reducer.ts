import { calcReducer, INITIAL_CALC_STATE } from "../../../components/calculator/reducer";
import { entry } from "../../../components/calculator/entry";
import { ONE } from "../node";
import type { CheckModule } from "./_types";

/**
 * Step 6: pure calculator state reducer invariants (stale watch replies ignored
 * while busy or after removal, top error preserved when an exact row lands,
 * cancel marks pending rows, submit merges onto latest stack).
 */
const checkModule: CheckModule = {
  id: 102,
  weight: 100,
  run(ctx) {
    const row1 = entry(ONE, "1", "float");
    const row2 = { ...entry(ONE, "pi", "exact"), pendingExact: true, text: "computing" };

    // Commit two rows and set a top error ("Swap needs two values.").
    let s = calcReducer(INITIAL_CALC_STATE, {
      type: "COMMIT",
      next: { stack: [row1], tape: ["1"], note: null, error: null },
    });
    s = calcReducer(s, {
      type: "COMMIT",
      next: { stack: [row1, row2], tape: ["1", "pi"], note: "computing", error: null },
    });
    s = calcReducer(s, { type: "SET_ERROR", error: "Swap needs two values." });

    // Stale watch reply for a non-existent row is a no-op.
    const stale = calcReducer(s, { type: "PUBLISH_WATCH", watch: 999_999, next: { ...row2, text: "stale" } });
    if (stale !== s) ctx.fail("FAIL reducer accepted stale watch");

    // Watch reply while busy (e.g. during mode switch) is ignored.
    const busy = calcReducer(s, { type: "SET_BUSY", busy: true });
    const ignored = calcReducer(busy, {
      type: "PUBLISH_WATCH",
      watch: row2.watch ?? -1,
      next: { ...row2, pendingExact: false, text: "3.14159" },
    });
    if (ignored !== busy) ctx.fail("FAIL reducer accepted watch reply while busy");

    // Watch reply when idle updates the matching row and keeps the swap error.
    const landed = calcReducer(s, {
      type: "PUBLISH_WATCH",
      watch: row2.watch ?? -1,
      next: { ...row2, pendingExact: false, text: "3.14159", value: { re: Math.PI, im: 0 } },
    });
    if (landed.model.stack[1]?.text !== "3.14159" || landed.model.error !== "Swap needs two values.") {
      ctx.fail("FAIL reducer publish watch", landed.model.stack[1]?.text, landed.model.error);
    }

    // CANCEL_EXACT marks pending rows cancelled and leaves finished rows intact.
    const cancelled = calcReducer(s, { type: "CANCEL_EXACT" });
    if (!cancelled.model.stack[1]?.cancelled || cancelled.model.stack[1]?.text !== "—" || cancelled.model.note !== "cancelled") {
      ctx.fail("FAIL reducer cancel exact", cancelled.model.stack[1]?.text, cancelled.model.note);
    }
  },
};

export default checkModule;
