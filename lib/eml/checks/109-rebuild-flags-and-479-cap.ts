import { exactReport, formatExact } from "../exact";
import {
  SINGULAR_POLE,
  SINGULAR_PRECISION,
  SINGULAR_TRIG,
  V,
  evaluateReport,
  isolateCircuit,
  nodeFromRpn,
  rpnTokens,
} from "../node";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * Regressions for:
 * A. Rebuilding a pure circuit from its press string / RPN tokens (across
 *    isolateCircuit clears) preserves low-precision, pole, and large-angle flags
 *    in float mode, exact mode, and across the worker wire.
 * B. exp(3.5e-479) - 1 and its neighbours (1e-479, 9.9e-480, -3.5e-479,
 *    ln(1+3.5e-479), sqrt(1+3.5e-479)-1) certify soundly via the extended
 *    leading-term series shortcut + exact-decimal decade, while cancellations
 *    exposing the dropped x² term and the power spelling exp(3.5*10^(-479))-1
 *    stay refused.
 */
const checkModule: CheckModule = {
  id: 109,
  weight: 3588,
  run(ctx) {
    // --- A. Press-string / RPN rebuild preserves precision, pole, and large-angle flags ---
    const rebuildCases: Array<{
      label: string;
      src: string;
      vars: Record<string, ReturnType<typeof V>>;
      env: Record<string, { re: number; im: number }>;
      wantFloat: string;
      checkExact?: string;
    }> = [
      { label: "tan(pi/2)", src: "tan(pi/2)", vars: {}, env: {}, wantFloat: SINGULAR_POLE, checkExact: SINGULAR_POLE },
      { label: "tan(3*pi/2)", src: "tan(3*pi/2)", vars: {}, env: {}, wantFloat: SINGULAR_POLE, checkExact: SINGULAR_POLE },
      { label: "sin(1e7)", src: "sin(1e7)", vars: {}, env: {}, wantFloat: SINGULAR_TRIG, checkExact: SINGULAR_TRIG },
      { label: "cos(1e7)", src: "cos(1e7)", vars: {}, env: {}, wantFloat: SINGULAR_TRIG, checkExact: SINGULAR_TRIG },
      { label: "tan(1e7)", src: "tan(1e7)", vars: {}, env: {}, wantFloat: SINGULAR_TRIG, checkExact: SINGULAR_TRIG },
      { label: "sin(x)@1e7", src: "sin(x)", vars: { x: V("x") }, env: { x: { re: 1e7, im: 0 } }, wantFloat: SINGULAR_TRIG, checkExact: SINGULAR_TRIG },
      { label: "tan(x)@pi/2", src: "tan(x)", vars: { x: V("x") }, env: { x: { re: Math.PI / 2, im: 0 } }, wantFloat: SINGULAR_POLE, checkExact: SINGULAR_POLE },
      { label: "asinh(x)@1e-13", src: "asinh(x)", vars: { x: V("x") }, env: { x: { re: 1e-13, im: 0 } }, wantFloat: SINGULAR_PRECISION },
      { label: "x+1@-1+1e-10", src: "x + 1", vars: { x: V("x") }, env: { x: { re: -1 + 1e-10, im: 0 } }, wantFloat: SINGULAR_PRECISION },
      { label: "x+y@cancel", src: "x + y", vars: { x: V("x"), y: V("y") }, env: { x: { re: 1, im: 0 }, y: { re: -1 + 1e-10, im: 0 } }, wantFloat: SINGULAR_PRECISION },
    ];

    for (const tc of rebuildCases) {
      const orig = compileExpression(tc.src, tc.vars);
      const tokens = rpnTokens(orig, 200_000);
      if (!tokens) {
        ctx.fail(`FAIL rebuild-rpn-extract ${tc.label}`);
        continue;
      }
      // Clear hash-consing table via an unrelated isolateCircuit so nodeFromRpn builds fresh nodes.
      compileExpression("1 + 1", {});
      const rebuilt = isolateCircuit(() => nodeFromRpn(tokens));

      const fl = evaluateReport(rebuilt, tc.env, { maxNodes: 200_000 });
      if (fl.singular !== tc.wantFloat) {
        ctx.fail(`FAIL rebuild-float-flag ${tc.label} got="${fl.singular}" want="${tc.wantFloat}"`);
      }

      if (tc.checkExact) {
        const ex = exactReport(rebuilt, tc.env, { maxNodes: 200_000 });
        if (ex.singular !== tc.checkExact) {
          ctx.fail(`FAIL rebuild-exact-flag ${tc.label} got="${ex.singular}" want="${tc.checkExact}"`);
        }
        const packed = packCircuit(rebuilt);
        const wireNode = unpackCircuit(packed.tokens, packed.root);
        const wireEx = exactReport(wireNode, tc.env, { maxNodes: 200_000 });
        if (wireEx.singular !== tc.checkExact) {
          ctx.fail(`FAIL rebuild-wire-flag ${tc.label} got="${wireEx.singular}" want="${tc.checkExact}"`);
        }
      }
    }

    // --- B. exp(3.5e-479)-1 and neighbours certify accurately (direct & wire), cancellations stay refused ---
    const certified479: [string, string][] = [
      ["exp(3.5e-479)-1", "3.5×10^−479"],
      ["exp(1e-479)-1", "1×10^−479"],
      ["exp(9.9e-480)-1", "9.9×10^−480"],
      ["exp(-3.5e-479)-1", "−3.5×10^−479"],
      ["1-exp(3.5e-479)", "−3.5×10^−479"],
      ["ln(1+3.5e-479)", "3.5×10^−479"],
      ["ln(1-3.5e-479)", "−3.5×10^−479"],
      ["sqrt(1+3.5e-479)-1", "1.75×10^−479"],
    ];

    for (const [src, want] of certified479) {
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
          ctx.fail(`FAIL 479-certify ${label} ${src} got=${rep.unverified ? "unverified" : got} want=${want}`);
        }
      }
    }

    // Soundness: cancellations exposing the dropped x² term and power spellings past the cap must stay refused.
    const refused479 = [
      "exp(3.5e-479)-1-3.5e-479",
      "(exp(3.5e-479)-1)/3.5e-479-1",
      "ln(1+3.5e-479)-3.5e-479",
      "sqrt(1+3.5e-479)-1-3.5e-479/2",
      "exp(3.5*10^(-479))-1",
      "exp(1e-433)-1",
      "exp((exp(3.5e-479)-1)*exp(2205)-3.5e-479*exp(2205))",
      "exp((ln(1+3.5e-479))*exp(2205)-3.5e-479*exp(2205))",
      "exp((exp(3.5e-479)-1)/exp(-2205)-3.5e-479/exp(-2205))",
    ];
    for (const src of refused479) {
      const node = compileExpression(src, {});
      const rep = exactReport(node, {}, { maxNodes: 800_000 });
      if (!rep.unverified) {
        ctx.fail(`FAIL 479-refuse ${src} unexpectedly certified as ${formatExact(rep.value)}`);
      }
    }
  },
};

export default checkModule;
