import { exactReport, formatExact } from "../exact";
import { ballConfirmsValue } from "../exact-ball";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Step 2: rigorous ball enclosure improvements (exact unit-circle ln, Comp.key
 * symmetry, atan2Fast, Step 1 exact facts, wire invariance, absorbed-term rescue,
 * and vanished second-order refusal).
 */
const checkModule: CheckModule = {
  id: 100,
  weight: 600,
  run(ctx) {
    // Ball directly confirms basic constants, ln(-1), cos(1), and large hypot cases
    // both in-process and after a packCircuit/unpackCircuit wire round-trip.
    const ballOk = [
      "0",
      "1",
      "-1",
      "2",
      "1/2",
      "i",
      "pi",
      "ln(-1)",
      "cos(1)",
      "hypot(10^160, -1)",
      "hypot(10^400, 10^400)",
    ];
    for (const src of ballOk) {
      const node = compileExpression(src, {});
      const packed = packCircuit(node);
      const wireNode = unpackCircuit(packed.tokens, packed.root);
      for (const [label, target] of [
        ["direct", node],
        ["wire", wireNode],
      ] as const) {
        const rep = exactReport(target, {}, { maxNodes: 800_000 });
        if (rep.unverified || !rep.value.re.isFinite() || !rep.value.im.isFinite()) {
          ctx.fail(`FAIL ball-ok ${label} ${src} not certified finite`);
          continue;
        }
        const prec = Math.min(600, Math.max(120, rep.digits ?? 120) + 60);
        if (!ballConfirmsValue(target, {}, rep.value, prec, 24, { maxNodes: 800_000 })) {
          ctx.fail(`FAIL ball-ok ${label} ${src} ball did not confirm ${formatExact(rep.value)}`);
        }
      }
    }

    // Over-refused absorbed-term expressions rescued by the ball enclosure (direct & wire),
    // plus sin(2/exp(200)) which must stay certified.
    const certifiedRows: [string, string][] = [
      ["10^(-500) + 10^400", "1×10^400"],
      ["avg(10^(-400), 10^400)", "5×10^399"],
      ["hypot(exp(700), 10^350)", "1×10^350"],
      ["arsinh(exp(-1000) + 2)", "1.443635475179"],
      ["hypot(10^160, -1)", "1×10^160"],
      ["hypot(10^400, 10^400)", "1.414213562373×10^400"],
      ["sin(2/exp(200))", "2.767793053473×10^−87"],
    ];
    for (const [src, want] of certifiedRows) {
      const node = compileExpression(src, {});
      const packed = packCircuit(node);
      const wireNode = unpackCircuit(packed.tokens, packed.root);
      for (const [label, target] of [
        ["direct", node],
        ["wire", wireNode],
      ] as const) {
        const rep = exactReport(target, {}, { maxNodes: 800_000 });
        const got = formatExact(rep.value);
        if (rep.unverified || got !== want) {
          ctx.fail(`FAIL ball-rescue ${label} ${src} got=${rep.unverified ? "unverified" : got} want=${want}`);
        }
      }
    }

    // Vanished second-order cancellation must be refused rather than certified as 0,
    // and ballConfirmsValue must reject all known-wrong second-order expressions.
    const mustRefuse = [
      "sqrt(1 + 10^(-250)) - 1 - 10^(-250)/2",
      "exp(3*10^(-238)) - 1 - 3*10^(-238)",
      "ln(exp(7*10^(-120))) - 7*10^(-120)",
      "sqrt(1 + 1.5*10^(-239)) - 1 - 1.5*10^(-239)/2",
    ];
    for (const src of mustRefuse) {
      const node = compileExpression(src, {});
      const rep = exactReport(node, {}, { maxNodes: 800_000 });
      if (!rep.unverified) {
        ctx.fail(`FAIL must-refuse ${src} certified as ${formatExact(rep.value)}`);
      }
    }

    const ballMustReject = [
      "exp(10^(-237)) - 1 - 10^(-237)",
      "sqrt(1 + 10^(-250)) - 1 - 10^(-250)/2",
      "(arctan(-3*10^(-122)*i) + 3*10^(-122)*i)*10^100",
      "ln(tanh(10^(-236) + 10^(-236)*i))",
    ];
    for (const src of ballMustReject) {
      const node = compileExpression(src, {});
      const rep = exactReport(node, {}, { maxNodes: 800_000 });
      if (rep.value.re.isFinite() && rep.value.im.isFinite()) {
        const prec = Math.min(600, Math.max(120, rep.digits ?? 120) + 60);
        if (ballConfirmsValue(node, {}, rep.value, prec, 24, { maxNodes: 800_000 })) {
          ctx.fail(`FAIL ball-reject ${src} falsely confirmed ${formatExact(rep.value)}`);
        }
      }
    }
  },
};

export default checkModule;
