import type { CheckModule } from "./_types";
import { evaluate, evaluateReport, SINGULAR_INDET } from "../node";
import { compileExpression, referenceExpression } from "../parse";
import { exactEvaluate, exactReport, formatExact } from "../exact";
import { formatC } from "../format";
import { packCircuit, unpackCircuit } from "../wire";
import { runTsx } from "./_helpers";
import { programNode } from "../programs";
import { provenInteger } from "../facts";
import { literalNode } from "../library";
import { applyModeSwitch, commitHistory, drainQueue, undoHistory } from "../history";

/**
 * Signed zero, infinity/singularity semantics, wide exact values, and calculator history/mode queue.
 */
const checks: CheckModule[] = [
  {
    id: 33,
    weight: 0,
    run(ctx) {
      const circuit = evaluate(compileExpression("1/(-0)", {}));
      const ref = referenceExpression("1/(-0)", {});
      if (circuit.re !== -Infinity || ref?.re !== -Infinity || circuit.im !== 0 || ref?.im !== 0) {
        ctx.fail("FAIL 1/(-0) agreement", circuit, ref);
      }
    },
  },
  {
    id: 34,
    weight: 2247,
    run(ctx) {
      const typed = evaluateReport(compileExpression("0*inf", {}));
      const typedExact = exactReport(compileExpression("0*inf", {}), {}, { maxNodes: 20_000 });
      if (typed.singular !== SINGULAR_INDET || !Number.isNaN(typed.value.re) || !Number.isNaN(typed.value.im)) {
        ctx.fail("FAIL typed 0*inf", typed);
      }
      if (typedExact.singular !== SINGULAR_INDET || !typedExact.value.re.isNaN()) {
        ctx.fail("FAIL exact typed 0*inf", formatExact(typedExact.value), typedExact.singular);
      }
      for (const source of ["ln(0)*0", "0*ln(0)", "ln(0)*(1-1)"]) {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, { maxNodes: 20_000 });
        const ex = exactReport(node, {}, { maxNodes: 20_000 });
        const text = formatExact(ex.value).replace(/\u200b/g, "");
        if (
          hw.singular === null ||
          !Number.isNaN(hw.value.re) ||
          !Number.isNaN(hw.value.im) ||
          ex.singular !== SINGULAR_INDET ||
          !ex.value.re.isNaN() ||
          !ex.value.im.isNaN() ||
          text === "0" ||
          text === "−0"
        ) {
          ctx.fail("FAIL 0 times ln 0", source, hw.singular, hw.value, ex.singular, text);
        } else {
          console.log("indet", source, text, ex.singular);
        }
      }
      const gap = compileExpression("inf-inf", {});
      const gapReport = evaluateReport(gap);
      const gapExact = exactReport(gap, {}, { maxNodes: 20_000 });
      const extended = [
        ["ln(0)*2", "−∞"],
        ["ln(0)*(-2)", "∞"],
        ["(-2)*ln(0)", "∞"],
        ["2*ln(0)", "−∞"],
        ["ln(0)*0", "undefined"],
        ["sin(inf)", "undefined"],
        ["sin(ln(0))", "undefined"],
        ["cos(inf)", "undefined"],
        ["cos(ln(0))", "undefined"],
        ["sin((inf+1)-1)", "undefined"],
        ["tan(inf)", "undefined"],
        ["tan(ln(0))", "undefined"],
        ["sqrt(ln(0))", "∞i"],
        ["ln(0)*i", "−∞i"],
        ["inf*i", "∞i"],
        ["i*inf", "∞i"],
        ["i*ln(0)", "−∞i"],
        ["sqrt(inf)", "∞"],
        ["sqrt(ln(0))^2", "−∞"],
        ["(-inf)*i", "−∞i"],
        ["i*(-inf)", "−∞i"],
        ["-(sqrt(ln(0)))", "−∞i"],
        ["(inf*i)*i", "−∞"],
        ["ln(0)*i*i", "∞"],
        ["sqrt(inf)^2", "∞"],
        ["1/(inf*i)", "0"],
        ["(inf*i)*(inf*i)", "−∞"],
        ["inf*(inf*i)", "∞i"],
        ["(-inf)*(-inf)", "∞"],
        ["inf*(1+i)", "unverified"],
        ["(inf*i)^3", "−∞i"],
        ["(inf*i)^4", "∞"],
        ["(inf*i)^5", "∞i"],
        ["(inf*i)^-1", "0"],
        ["(inf*i)^-2", "0"],
        ["(-inf)^3", "−∞"],
        ["(-inf)^2", "∞"],
        ["(inf*i)^0.5", "unverified"],
        ["ln(0)-1", "unverified"],
        ["ln(0)+i", "unverified"],
        ["(inf*i)/2", "unverified"],
        ["ln(ln(0)*i)", "unverified"],
        ["ln(0)+0", "−∞"],
        ["ln(0)-0", "−∞"],
        ["ln(0)+1", "unverified"],
        ["ln(0)*i+1", "unverified"],
        ["inf+1", "unverified"],
        ["1+inf", "unverified"],
        ["1+2+inf", "unverified"],
        ["inf+inf", "unverified"],
        ["1+ln(0)", "unverified"],
        ["ln(0)+ln(0)", "unverified"],
        ["1+inf*i", "unverified"],
        ["inf-ln(0)", "∞"],
        ["inf*i+0", "∞i"],
        ["sqrt(ln(0))+0", "∞i"],
        ["ln(0)*i-0", "−∞i"],
        ["sqrt(inf*i)", "unverified"],
        ["ln(inf*i)", "unverified"],
        ["(inf*i)/i", "unverified"],
        ["ln(ln(0))", "∞ + 3.14159265359i"],
        ["exp(800)-exp(800)", "0"],
        ["exp(800)-exp(800)+1", "1"],
        ["exp(1000)/exp(1000)", "1"],
      ] as const;
      for (const [source, want] of extended) {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, { maxNodes: 200_000 });
        const ex = exactReport(node, {}, { maxNodes: 200_000 });
        const floatText = formatC(hw.value);
        const exactText = formatExact(ex.value).replace(/\u200b/g, "");
        const flagged = want === "unverified";
        const floatOk = flagged ? hw.unverified === true && floatText !== "∞" : floatText === want;
        const exactOk = flagged ? ex.unverified === true && exactText !== "∞" : exactText === want;
        if (!floatOk || !exactOk || (!flagged && floatText !== exactText)) {
          ctx.fail("FAIL extended value", source, floatText, exactText, hw.singular, ex.singular, hw.unverified, ex.unverified);
        }
      }
      // The in-process rows never pack. The screen's exact worker evaluates the packed circuit.
      const freshAngles = ["sin(inf)", "cos(inf)", "sin(ln(0))", "cos(ln(0))", "tan(inf)", "tan(ln(0))"];
      const freshDirected = [
        ["sqrt(ln(0))", "∞i"],
        ["ln(0)*i", "−∞i"],
        ["inf*i", "∞i"],
        ["i*inf", "∞i"],
        ["i*ln(0)", "−∞i"],
        ["sqrt(inf)", "∞"],
        ["sqrt(ln(0))^2", "−∞"],
        ["(-inf)*i", "−∞i"],
        ["i*(-inf)", "−∞i"],
        ["-(sqrt(ln(0)))", "−∞i"],
        ["(inf*i)*i", "−∞"],
        ["ln(0)*i*i", "∞"],
        ["sqrt(inf)^2", "∞"],
        ["1/(inf*i)", "0"],
        ["(inf*i)*(inf*i)", "−∞"],
        ["inf*(inf*i)", "∞i"],
        ["(-inf)*(-inf)", "∞"],
        ["inf*(1+i)", "unverified"],
        ["(inf*i)^3", "−∞i"],
        ["(inf*i)^4", "∞"],
        ["(inf*i)^5", "∞i"],
        ["(inf*i)^-1", "0"],
        ["(inf*i)^-2", "0"],
        ["(-inf)^3", "−∞"],
        ["(-inf)^2", "∞"],
        ["(inf*i)^0.5", "unverified"],
        ["ln(0)-1", "unverified"],
        ["ln(0)+i", "unverified"],
        ["(inf*i)/2", "unverified"],
        ["ln(ln(0)*i)", "unverified"],
        ["ln(0)+0", "−∞"],
        ["ln(0)-0", "−∞"],
        ["ln(0)+1", "unverified"],
        ["ln(0)*i+1", "unverified"],
        ["inf+1", "unverified"],
        ["1+inf", "unverified"],
        ["1+2+inf", "unverified"],
        ["inf+inf", "unverified"],
        ["1+ln(0)", "unverified"],
        ["ln(0)+ln(0)", "unverified"],
        ["1+inf*i", "unverified"],
        ["inf-ln(0)", "∞"],
        ["inf*i+0", "∞i"],
        ["sqrt(ln(0))+0", "∞i"],
        ["ln(0)*i-0", "−∞i"],
        ["sqrt(inf*i)", "unverified"],
        ["ln(inf*i)", "unverified"],
        ["(inf*i)/i", "unverified"],
        ["ln(ln(0))", "∞ + 3.14159265359i"],
        ["exp(800)-exp(800)", "0"],
        ["exp(800)-exp(800)+1", "1"],
        ["exp(1000)/exp(1000)", "1"],
      ] as const;
      const freshJobs = [...freshAngles, ...freshDirected.map(([source]) => source)].map((source) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root };
      });
      const freshAnglesRun = runTsx("scripts/fresh-exact.ts", JSON.stringify(freshJobs));
      if (freshAnglesRun.status !== 0) {
        ctx.fail("FAIL fresh trig infinity", freshAnglesRun.status, freshAnglesRun.stderr);
      } else {
        const rows = JSON.parse(freshAnglesRun.stdout) as Array<{ source: string; text: string; singular: string | null; unverified: boolean }>;
        const directed = new Map<string, string>(freshDirected.map(([source, want]) => [source, want]));
        for (const row of rows) {
          const text = row.text.replace(/\u200b/g, "");
          const want = directed.get(row.source);
          if (want === "unverified") {
            if (!row.unverified || text === "∞") {
              ctx.fail("FAIL fresh directed infinity", row.source, text, row.singular, row.unverified);
            }
          } else if (want !== undefined) {
            if (text !== want || row.unverified) {
              ctx.fail("FAIL fresh directed infinity", row.source, text, row.singular, row.unverified);
            }
          } else if (text !== "undefined" || row.singular === null) {
            ctx.fail("FAIL fresh trig infinity", row.source, text, row.singular);
          }
        }
      }
      // Direct compile is checked in `extended`. The screen packs the same circuit
      // for the exact worker; unpack here so a packed overflow difference cannot
      // ship a certified −∞.
      for (const [source, want] of [
        ["exp(800)-exp(800)", "0"],
        ["exp(800)-exp(800)+1", "1"],
        ["exp(1000)/exp(1000)", "1"],
      ] as const) {
        const packed = packCircuit(compileExpression(source, {}));
        const rebuilt = unpackCircuit(packed.tokens, packed.root);
        const direct = exactReport(compileExpression(source, {}), {}, { maxNodes: 200_000 });
        const wire = exactReport(rebuilt, {}, { maxNodes: 200_000 });
        const directText = formatExact(direct.value).replace(/\u200b/g, "");
        const wireText = formatExact(wire.value).replace(/\u200b/g, "");
        if (direct.unverified || wire.unverified || directText !== want || wireText !== want) {
          ctx.fail("FAIL packed overflow cancel", source, directText, wireText, direct.unverified, wire.unverified);
        }
      }
      if (gap === programNode("0") || gapReport.singular !== SINGULAR_INDET) {
        ctx.fail("FAIL inf-inf", gapReport, gap === programNode("0"));
      }
      if (!Number.isNaN(gapReport.value.re) || !gapExact.value.re.isNaN()) {
        ctx.fail("FAIL inf-inf value", gapReport.value, formatExact(gapExact.value));
      }
      const powDiff = evaluate(compileExpression("(2^53+1)-2^53", {}));
      if (powDiff.re !== 1 || powDiff.im !== 0) {
        ctx.fail("FAIL float (2^53+1)-2^53", powDiff);
      }
      const hugeReal = evaluate(compileExpression("1e300+i", {}));
      const hugeExact = exactEvaluate(compileExpression("1e300+i", {}), {}, { maxNodes: 400_000 });
      // 10^300 is large enough that a unit imaginary is below exact mode's cancellation
      // tolerance after scaling, and float reconstruction does not keep it either.
      if (Math.abs(hugeReal.re - 1e300) / 1e300 > 1e-9 || hugeExact.re.minus("1e300").abs().div("1e300").gt("1e-12")) {
        ctx.fail("FAIL 1e300+i", hugeReal, hugeExact.re.toString(), hugeExact.im.toString());
      }
      const overflow = evaluateReport(compileExpression("10^400/7", {}), {}, { maxNodes: 400_000 });
      if (overflow.value.re !== Infinity || !overflow.overflowed) {
        ctx.fail("FAIL 10^400/7 overflow", overflow.value, overflow.overflowed, overflow.singular);
      }
      const bigInt = "1234567890123456789012345678901234567890";
      const shown = formatExact(exactEvaluate(compileExpression("9007199254740993", {}), {}, { maxNodes: 200_000 }));
      const shown40 = formatExact(exactEvaluate(compileExpression(bigInt, {}), {}, { maxNodes: 400_000 }));
      if (shown.replace(/\u200b/g, "") !== "9007199254740993" || shown40.replace(/\u200b/g, "") !== bigInt) {
          const lit = compileExpression("9007199254740993", {});
        ctx.fail("FAIL exact integer text", shown, shown40, provenInteger(lit)?.toString());
      }
      const signed = evaluate(literalNode("-0"));
      if (!Object.is(signed.re, -0) || signed.im !== 0) {
        ctx.fail("FAIL literal -0", signed);
      }
    },
  },
  {
    id: 35,
    weight: 94,
    run(ctx) {
      const wide = exactEvaluate(compileExpression("1e40+i", {}));
      if (wide.re.toExponential(2) !== "1.00e+40" || wide.im.minus(1).abs().gt("1e-6")) {
        ctx.fail("FAIL exact 1e40+i drops the imaginary part", wide.re.toString(), wide.im.toString());
      }
    },
  },
  {
    id: 36,
    weight: 0,
    run(ctx) {
      let history = { past: [] as string[], current: "empty" };
      history = commitHistory(history, "one");
      history = commitHistory(history, "two");
      const queue: Array<() => void> = [];
      queue.push(() => {
        history = undoHistory(history);
      });
      queue.push(() => {
        history = undoHistory(history);
      });
      drainQueue(queue);
      if (history.current !== "empty" || history.past.length !== 0) {
        ctx.fail("FAIL queued undo replayed a stale snapshot", history);
      }
      const switched = applyModeSwitch({
        previous: ["old-a", "old-b"],
        recomputed: ["new-a"],
        error: "exact timed out",
        fail: (item, error) => `${item}:${error}`,
      });
      if (switched.error !== "exact timed out" || switched.stack[0] !== "new-a" || switched.stack[1] !== "old-b:exact timed out") {
        ctx.fail("FAIL mode switch left an old value", switched);
      }
    },
  },
];

export default checks;
