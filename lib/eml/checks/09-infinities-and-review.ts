import type { CheckModule } from "./_types";
import { compileExpression } from "../parse";
import { circuitStats, E, EmlError, evaluateReport, ONE, rpnTokens, V } from "../node";
import { exactClose, exactReport, formatExact } from "../exact";
import { formatC } from "../format";
import { c, close } from "../complex";
import { packCircuit } from "../wire";
import { runTsx } from "./_helpers";

/**
 * Marked infinities, outside-review section A regressions, and parser error messages.
 */
const checks: CheckModule[] = [
  {
    id: 52,
    weight: 1310,
    run(ctx) {
      // Marked infinities. mpmath dps 50: ln(0) is -inf and 0/0 raises ZeroDivisionError.
      // tan(pi/2) there is the finite -1.9788349012695708716820519525808990497221781173111e+51,
      // because a 50-digit pi/2 is not the symbolic pole. The self-differences below are undefined,
      // with a singular flag, in both modes. (1/0)-(1/0) is the same kind of control.
      // exp(ln(0)) is 0, so that difference stays the folded 0.
      // mpmath dps 420: (10^400-1)-10^400 = -1, (10^400+1)-10^400 = 1,
      // 10^400-(10^400-1) = 1, (10^400-10^300)/10^300 = 10^100-1.
      // At dps 50, 10^100-1 prints as 1.0000000000000000000000000000000000000000000000000e+100,
      // the same text as 10^100. The exact check uses 110 digits, where they differ.
      const budget = { maxNodes: 400_000 };
      const undef = (source: string) => {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        if (formatC(hw.value) !== "undefined" || hw.singular === null || formatExact(ex.value) !== "undefined" || ex.singular === null) {
          ctx.fail("FAIL marked cancellation", source, hw.singular, hw.value, ex.singular, formatExact(ex.value));
        }
      };
      undef("(0/0)-(0/0)");
      undef("tan(pi/2)-tan(pi/2)");
      undef("tan(3*pi/2)-tan(3*pi/2)");
      undef("ln(ln(0))-ln(ln(0))");
      undef("ln(0)-ln(0)");
      undef("tan(pi/2)+(-tan(pi/2))");
      undef("(0/0)+(-(0/0))");
      undef("(1/0)-(1/0)");

      const finiteZero = (source: string) => {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        if (hw.value.re !== 0 || hw.value.im !== 0 || hw.singular !== null || ex.singular !== null || !ex.value.re.isZero() || !ex.value.im.isZero()) {
          ctx.fail("FAIL finite cancellation", source, hw.singular, hw.value, ex.singular, formatExact(ex.value));
        }
      };
      finiteZero("exp(ln(0))-exp(ln(0))");
      const zeroGates = circuitStats(compileExpression("0", {})).dagGates;
      const sinDiff = compileExpression("sin(1)-sin(1)", {});
      const sinGates = circuitStats(compileExpression("sin(1)", {})).dagGates;
      if (circuitStats(sinDiff).dagGates !== zeroGates || sinGates <= zeroGates) {
        ctx.fail("FAIL sin(1)-sin(1) was not the folded zero", circuitStats(sinDiff).dagGates, sinGates, zeroGates);
      }
      finiteZero("sin(1)-sin(1)");
      const near = "tan(1.5707963267948966)-tan(1.5707963267948966)";
      const nearNode = compileExpression(near, {});
      if (circuitStats(nearNode).dagGates !== zeroGates) {
        ctx.fail("FAIL nearby tan fold", circuitStats(nearNode).dagGates, zeroGates);
      }
      finiteZero(near);

      const expectInt = (source: string, wantNum: number, wantText: string) => {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        const text = formatExact(ex.value).replace(/\u200b/g, "");
        if (hw.value.re !== wantNum || hw.value.im !== 0 || hw.singular !== null || ex.singular !== null || text !== wantText) {
          ctx.fail("FAIL huge exact difference", source, hw.value, hw.singular, text, ex.singular);
        }
      };
      expectInt("(10^400-1)-10^400", -1, "−1");
      expectInt("(10^400+1)-10^400", 1, "1");
      expectInt("10^400-(10^400-1)", 1, "1");

      // mpmath dps 50. A finite non-integer beside 10^400 cancels back to itself.
      // i = 0 + i, −i = 0 − i, 0.5 = 0.5,
      // pi = 3.1415926535897932384626433832795028841971693993751,
      // sqrt(2) = 1.4142135623730950488016887242096980785696718753769.
      const beside = (source: string, re: string, im = "0") => {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        if (
          hw.singular !== null ||
          ex.singular !== null ||
          !close(hw.value, c(Number(re), Number(im)), 1e-12) ||
          !exactClose(ex.value, re, im, 40)
        ) {
          ctx.fail("FAIL huge plus small part", source, hw.value, hw.singular, formatExact(ex.value), ex.singular);
        }
      };
      beside("(10^400+i)-10^400", "0", "1");
      beside("(10^400+pi)-10^400", "3.1415926535897932384626433832795028841971693993751");
      beside("(10^400+sqrt(2))-10^400", "1.4142135623730950488016887242096980785696718753769");
      beside("(10^400+0.5)-10^400", "0.5");
      beside("(10^400+(-i))-10^400", "0", "-1");

      const gap = exactReport(compileExpression("10^400-10^300", {}), {}, budget);
      const gapText = "9".repeat(100) + "0".repeat(300);
      if (exactClose(gap.value, "1e400", 0, 110) || !exactClose(gap.value, gapText, 0, 110)) {
        ctx.fail("FAIL exact 10^400-10^300 dropped 10^300", formatExact(gap.value));
      }
      const quotNode = compileExpression("(10^400-10^300)/10^300", {});
      const quotHw = evaluateReport(quotNode, {}, budget);
      const quotEx = exactReport(quotNode, {}, budget);
      const nines = "9".repeat(100);
      const quotText = formatExact(quotEx.value).replace(/\u200b/g, "");
      if (
        !Number.isFinite(quotHw.value.re) ||
        Math.abs(quotHw.value.re - 1e100) / 1e100 > 1e-12 ||
        quotHw.value.im !== 0 ||
        quotHw.singular !== null ||
        quotEx.singular !== null ||
        quotText !== nines ||
        !exactClose(quotEx.value, nines, 0, 110) ||
        exactClose(quotEx.value, "1e100", 0, 110)
      ) {
        ctx.fail("FAIL (10^400-10^300)/10^300", quotHw.value, quotHw.singular, quotText, quotEx.singular);
      }

      // mpmath: (10^400+3)-(10^400+1) = 2, (10^400+1)-(10^400+2) = -1,
      // ((10^400+3)+(10^400+1))-2*10^400 = 4,
      // (10^400+10^300)-(10^400-10^300) = 2*10^300,
      // (10^401+1)-(10^400+1) = 9*10^400.
      const two300 = `2${"0".repeat(300)}`;
      const nine400 = `9${"0".repeat(400)}`;
      const gap400 = `${"9".repeat(100)}${"0".repeat(300)}`;
      const expectDiff = (source: string, re: number, text: string) => {
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        const got = formatExact(ex.value).replace(/\u200b/g, "");
        if (hw.singular !== null || ex.singular !== null || !close(hw.value, c(re, 0), 1e-12) || got !== text) {
          ctx.fail("FAIL distinct huge difference", source, hw.value, hw.singular, got, ex.singular);
        }
      };
      expectDiff("(10^400+3)-(10^400+1)", 2, "2");
      expectDiff("(10^400+1)-(10^400+2)", -1, "−1");
      expectDiff("((10^400+3)+(10^400+1))-2*10^400", 4, "4");
      const wideDiff = "(10^400+10^300)-(10^400-10^300)";
      const wideNode = compileExpression(wideDiff, {});
      const wideHw = evaluateReport(wideNode, {}, budget);
      const wideEx = exactReport(wideNode, {}, budget);
      if (
        wideHw.singular !== null ||
        wideEx.singular !== null ||
        !close(wideHw.value, c(2e300, 0), 1e-12) ||
        formatExact(wideEx.value).replace(/\u200b/g, "") !== "2×10^300" ||
        !exactClose(wideEx.value, two300, 0, 110)
      ) {
        ctx.fail("FAIL 2*10^300 gap", wideHw.value, wideHw.singular, formatExact(wideEx.value), wideEx.singular);
      }
      const nineNode = compileExpression("(10^401+1)-(10^400+1)", {});
      const nineHw = evaluateReport(nineNode, {}, budget);
      const nineEx = exactReport(nineNode, {}, budget);
      if (
        nineHw.value.re !== Infinity ||
        nineHw.value.im !== 0 ||
        nineEx.singular !== null ||
        formatExact(nineEx.value).replace(/\u200b/g, "") !== "9×10^400" ||
        !exactClose(nineEx.value, nine400, 0, 110)
      ) {
        ctx.fail("FAIL 9*10^400", nineHw.value, nineHw.singular, formatExact(nineEx.value), nineEx.singular);
      }

      const carried = (source: string) => {
        const packed = packCircuit(compileExpression(source, {}));
        return packed.tokens.flatMap((tok) => ("int" in tok && tok.int ? [tok.int] : []));
      };
      const expectCarried = (source: string, digits: string) => {
        if (!carried(source).includes(digits)) {
          ctx.fail("FAIL integer missing on the wire", source);
        }
      };
      expectCarried("(10^401+1)-(10^400+1)", nine400);
      expectCarried("(10^400-10^300)/10^300", nines);
      expectCarried("10^400-10^300", gap400);
      expectCarried(wideDiff, two300);
      expectCarried("(10^400+1)/7", `${"1"}${"0".repeat(399)}1`);

      // A fresh process has an empty mark table. Same-process unpack reuses interned leaves.
      const wireRows: { source: string; re: string; im?: string; digits?: number; text?: string }[] = [
        { source: "(10^400-1)-10^400", re: "-1", text: "−1" },
        { source: "(10^400+1)-10^400", re: "1", text: "1" },
        { source: "10^400-(10^400-1)", re: "1", text: "1" },
        { source: "(10^400+i)-10^400", re: "0", im: "1" },
        { source: "(10^400+pi)-10^400", re: "3.1415926535897932384626433832795028841971693993751" },
        { source: "(10^400+sqrt(2))-10^400", re: "1.4142135623730950488016887242096980785696718753769" },
        { source: "(10^400+0.5)-10^400", re: "0.5", text: "0.5" },
        { source: "(10^400+(-i))-10^400", re: "0", im: "-1" },
        { source: "(10^400+3)-(10^400+1)", re: "2", text: "2" },
        { source: "(10^400+1)-(10^400+2)", re: "-1", text: "−1" },
        { source: "((10^400+3)+(10^400+1))-2*10^400", re: "4", text: "4" },
        { source: wideDiff, re: two300, digits: 110, text: "2×10^300" },
        { source: "(10^401+1)-(10^400+1)", re: nine400, digits: 110, text: "9×10^400" },
        { source: "(10^400-10^300)/10^300", re: nines, digits: 110, text: nines },
        { source: "10^400-10^300", re: gap400, digits: 110 },
        { source: "(10^400+1)/7", re: "1.428571428571428571428571e+399", digits: 20 },
      ];
      const wireJobs = wireRows.map((row) => {
        const packed = packCircuit(compileExpression(row.source, {}));
        return { source: row.source, tokens: packed.tokens, root: packed.root, re: row.re, im: row.im, digits: row.digits };
      });
      const wire = runTsx("scripts/fresh-exact.ts", JSON.stringify(wireJobs));
      if (wire.status !== 0) {
        ctx.fail("FAIL fresh huge integer", wire.status, wire.stderr);
      } else {
        const rows = JSON.parse(wire.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; close?: boolean }>;
        for (const row of rows) {
          const want = wireRows.find((item) => item.source === row.source);
          const text = row.text.replace(/\u200b/g, "");
          if (row.unverified || row.singular !== null || row.close !== true || (want?.text !== undefined && text !== want.text)) {
            ctx.fail("FAIL fresh huge", row.source, row.unverified ? "unverified" : text, row.singular, row.close);
          }
        }
      }

      // Identical nodes cancel to 0. mpmath at 1,200 digits is 0.
      // Two huge-carried terms whose small parts are not both exact integers are unverified, never a value.
      // (10^400+1)+(10^400+1) is the integer 2×10^400+2. A 1,200-digit compare sees the units digit.
      // The parser has no juxtaposition, so 2(10^400+pi) is written 2*(10^400+pi).
      const twoPlus = `2${"0".repeat(399)}2`;
      const cancelRows = [
        "(10^400+pi)+(-(10^400+pi))",
        "(10^400+i)+(-(10^400+i))",
        "(10^400+sqrt(2))+(-(10^400+sqrt(2)))",
        "(10^400+e)+(-(10^400+e))",
        "(10^400+0.5)+(-(10^400+0.5))",
        "(10^400+pi)-(10^400+pi)",
        "(10^400+i)-(10^400+i)",
        "(10^400+sqrt(2))-(10^400+sqrt(2))",
        "(10^400+e)-(10^400+e)",
      ];
      const flagRows = [
        "(10^400+pi)+(-(10^400+e))",
        "(10^400+pi)-(10^400+1)",
        "(10^400+1)-(10^400+i)",
        "(10^400+i)-(10^400+(-i))",
        "(10^400+sqrt(2))-(10^400+0.5)",
        "(10^400+pi)-(10^400+e)",
        "2*(10^400+pi)-2*10^400",
        "(10^400+i)-(10^400-i)",
        "-(10^400+pi)+10^400",
        "(10^400+1)+(-(10^400+i))",
        "(10^400+pi)+(-(10^400+1))",
        "(10^400+3)+(-(10^400+pi))",
        "(10^400+e)-(10^400+0.5)",
        "(10^400+i)+(10^400+i)",
        "(10^400+i)+(10^400+(-i))",
      ];
      const bareRows = ["10^400+pi", "10^400+i", "10^400-0.5"];
      const hugeJobs: { source: string; tokens: ReturnType<typeof packCircuit>["tokens"]; root: number; re?: string; digits?: number }[] = [];
      const timeCancel = (source: string) => {
        const started = performance.now();
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        const ms = performance.now() - started;
        const text = formatExact(ex.value).replace(/\u200b/g, "");
        const ok =
          ms < 200 &&
          hw.unverified !== true &&
          ex.unverified !== true &&
          hw.singular === null &&
          ex.singular === null &&
          close(hw.value, c(0, 0), 1e-12) &&
          text === "0" &&
          exactClose(ex.value, "0", "0", 1200);
        if (!ok) {
          ctx.fail("FAIL identical cancel", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : text);
        } else {
          console.log("cancel", source, "exact 0", `${ms.toFixed(1)}ms`);
        }
        const packed = packCircuit(node);
        hugeJobs.push({ source, tokens: packed.tokens, root: packed.root, re: "0", digits: 1200 });
      };
      for (const source of cancelRows) timeCancel(source);
      const timeFlag = (source: string) => {
        const started = performance.now();
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        const ms = performance.now() - started;
        if (ms >= 200 || hw.unverified !== true || ex.unverified !== true) {
          ctx.fail("FAIL unverified huge pair", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : formatExact(ex.value));
        } else {
          console.log("flag", source, "unverified", `${ms.toFixed(1)}ms`);
        }
        const packed = packCircuit(node);
        hugeJobs.push({ source, tokens: packed.tokens, root: packed.root });
      };
      for (const source of flagRows) timeFlag(source);
      const timeBare = (source: string) => {
        const started = performance.now();
        const node = compileExpression(source, {});
        const hw = evaluateReport(node, {}, budget);
        const ex = exactReport(node, {}, budget);
        const ms = performance.now() - started;
        const text = formatExact(ex.value).replace(/\u200b/g, "");
        const floatDropped = hw.unverified !== true && Number.isFinite(hw.value.re) && Number.isFinite(hw.value.im);
        if (ms >= 200 || ex.unverified !== true || floatDropped) {
          ctx.fail("FAIL bare huge sum", source, `${ms.toFixed(1)}ms`, hw.unverified ? "unverified" : hw.value, ex.unverified ? "unverified" : text);
        } else {
          console.log("bare", source, "unverified", `${ms.toFixed(1)}ms`);
        }
        const packed = packCircuit(node);
        hugeJobs.push({ source, tokens: packed.tokens, root: packed.root });
      };
      for (const source of bareRows) timeBare(source);
      const intSource = "(10^400+1)+(10^400+1)";
      const intStarted = performance.now();
      const intNode = compileExpression(intSource, {});
      const intHw = evaluateReport(intNode, {}, budget);
      const intEx = exactReport(intNode, {}, budget);
      const intMs = performance.now() - intStarted;
      const intText = formatExact(intEx.value).replace(/\u200b/g, "");
      if (
        intMs >= 200 ||
        intHw.unverified === true ||
        intEx.unverified === true ||
        intHw.value.re !== Infinity ||
        intHw.value.im !== 0 ||
        intEx.singular !== null ||
        intText !== twoPlus ||
        !exactClose(intEx.value, twoPlus, "0", 1200) ||
        exactClose(intEx.value, `2${"0".repeat(400)}`, "0", 1200)
      ) {
        ctx.fail("FAIL exact 2*10^400+2", `${intMs.toFixed(1)}ms`, intHw.value, intHw.unverified, intEx.unverified ? "unverified" : intText.slice(0, 12), intEx.singular);
      } else {
        console.log("int", intSource, "2×10^400+2", `${intMs.toFixed(1)}ms`);
      }
      const intPacked = packCircuit(intNode);
      hugeJobs.push({ source: intSource, tokens: intPacked.tokens, root: intPacked.root, re: twoPlus, digits: 1200 });
      const hugeWire = runTsx("scripts/fresh-exact.ts", JSON.stringify(hugeJobs));
      if (hugeWire.status !== 0) {
        ctx.fail("FAIL fresh huge pairs", hugeWire.status, hugeWire.stderr);
      } else {
        const rows = JSON.parse(hugeWire.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; close?: boolean; ms: number }>;
        for (const row of rows) {
          const text = row.text.replace(/\u200b/g, "");
          const wantFlag = flagRows.includes(row.source) || bareRows.includes(row.source);
          const freshOk = wantFlag
            ? row.unverified === true && row.ms < 200
            : row.unverified !== true && row.singular === null && row.close === true && row.ms < 200 && (row.source === intSource ? text === twoPlus : text === "0");
          if (!freshOk) {
            ctx.fail("FAIL fresh huge pair", row.source, `${row.ms}ms`, row.unverified ? "unverified" : text, row.singular, row.close);
          } else {
            console.log("fresh", row.source, wantFlag ? "unverified" : text === twoPlus ? "2×10^400+2" : "exact 0", `${row.ms}ms`);
          }
        }
      }
    },
  },
  {
    id: 53,
    weight: 13922,
    run(ctx) {
      // Outside review, section A. Each row fails while its claim holds.
      // A1: an angle within the snap tolerance of 0 is not the axis. sin(6.103e-120) is not 0,
      // so the doubled tiny imaginary sum keeps both halves (or says it could not verify).
      const tinyTwice = exactReport(compileExpression("6.103e-120*i + 6.103e-120*i", {}));
      const tinyTwiceText = formatExact(tinyTwice.value);
      if (!tinyTwice.unverified && tinyTwiceText !== "1.2206×10^−119i") {
        ctx.fail("FAIL review A1 tiny imaginary sum", tinyTwiceText);
      } else {
        console.log("review A1 tiny imaginary sum", tinyTwice.unverified ? "couldn't verify" : tinyTwiceText);
      }
      // exp of a tiny imaginary angle. Float gives 1 + 6.1e-120i, so an exact 1 with no note drops a component.
      const tinyTurn = exactReport(compileExpression("exp(6.103515625e-120*i)", {}));
      const tinyTurnText = formatExact(tinyTurn.value);
      if (!tinyTurn.unverified && !tinyTurn.singular && tinyTurn.value.im.isZero()) {
        ctx.fail("FAIL review A1 tiny turn", tinyTurnText);
      } else {
        console.log("review A1 tiny turn", tinyTurn.unverified ? "couldn't verify" : tinyTurnText, tinyTurn.singular ?? "");
      }
      // A tiny real part beside an imaginary one. The real part is a known 10^(−130) or
      // 10^(−136), so 0.5i or 1.5i alone drops it. Direct here, and packed in a fresh process
      // below in both orders, so cache hits and misses are both covered.
      const tinyBesideRows: Array<[string, string]> = [
        ["((1+10^(-130))-1)+i/2", "1×10^−130 + 0.5i"],
        ["(i*(1+10^-130)-i)*i+i/2", "−1×10^−130 + 0.5i"],
        ["((1+10^(-136))-1)+i*3/2", "1×10^−136 + 1.5i"],
      ];
      for (const [source, want] of tinyBesideRows) {
        const report = exactReport(compileExpression(source, {}));
        const text = report.unverified ? "unverified" : formatExact(report.value);
        if (text !== want && text !== "unverified") {
          ctx.fail("FAIL tiny real beside imaginary", source, text);
        } else {
          console.log("tiny real beside imaginary", source, text);
        }
      }
      const besideJobs = tinyBesideRows.map(([source]) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root, again: true as const };
      });
      for (const jobs of [besideJobs, [...besideJobs].reverse()]) {
        const run = runTsx("scripts/fresh-exact.ts", JSON.stringify(jobs));
        if (run.status !== 0) {
          ctx.fail("FAIL fresh tiny real beside imaginary", run.status, run.stderr?.slice(0, 400));
          continue;
        }
        for (const row of JSON.parse(run.stdout) as Array<{ source: string; text: string; unverified: boolean; again?: string }>) {
          const want = tinyBesideRows.find(([source]) => source === row.source)?.[1];
          const first = row.unverified ? "unverified" : row.text;
          const ok = (text: string | undefined) => text === want || text === "unverified";
          if (!ok(first) || !ok(row.again)) {
            ctx.fail("FAIL fresh tiny real beside imaginary", row.source, first, row.again);
          }
        }
      }
      // A2: a word built with no lowering notes, evaluated twice on the same node in a
      // fresh process. The second pass reads the var-free cache and must still find the
      // cancellation that the first pass recovered.
      const lossSource = "exp(10^(-115))-1";
      const lossWord = rpnTokens(compileExpression(lossSource, {}), 100_000);
      // A4: the worker receives a packed circuit. Its singular note must match the main thread.
      const noteRows: Array<[string, Record<string, { re: number; im: number }>]> = [
        ["asinh(x)", { x: c(1e-13) }],
        ["x+y", { x: c(1e-20), y: c(1e-20) }],
      ];
      const noteMain = noteRows.map(([source, env]) => exactReport(compileExpression(source, { x: V("x"), y: V("y") }), env).singular);
      const reviewJobs = [
        ...(lossWord ? [{ source: lossSource, word: lossWord, again: true }] : []),
        ...noteRows.map(([source, env]) => {
          const packed = packCircuit(compileExpression(source, { x: V("x"), y: V("y") }));
          return { source, tokens: packed.tokens, root: packed.root, env };
        }),
      ];
      const reviewFresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(reviewJobs));
      if (!lossWord || reviewFresh.status !== 0) {
        ctx.fail("FAIL review A fresh run", lossWord ? lossWord.length : "no word", reviewFresh.status, reviewFresh.stderr?.slice(0, 400));
      } else {
        const rows = JSON.parse(reviewFresh.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; again?: string }>;
        const [loss, ...notes] = rows;
        const shown = (text: string, unverified: boolean) => (unverified ? "unverified" : text);
        const first = loss ? shown(loss.text, loss.unverified) : "missing";
        const second = loss?.again ?? "missing";
        const honest = (text: string) => text === "1×10^−115" || text === "unverified";
        if (!honest(first) || !honest(second)) {
          ctx.fail("FAIL review A2 cached word", lossSource, "first", first, "second", second);
        } else {
          console.log("review A2 cached word", lossSource, first, second);
        }
        notes.forEach((row, index) => {
          const want = noteMain[index] ?? null;
          if (row.singular !== want) {
            ctx.fail("FAIL review A4 worker note", row.source, "worker", row.singular, "main", want);
          } else {
            console.log("review A4 worker note", row.source, row.singular);
          }
        });
      }
    },
  },
  {
    id: 54,
    weight: 13,
    run(ctx) {
      // Parser messages say what to type: implicit products, a function without
      // parentheses, an unknown function, and a doubled operator.
      const messages: [string, string][] = [
        ["2pi", "Put * between “2” and “pi”."],
        ["2(3)", "Put * between “2” and “(”."],
        ["sin 1", "Write sin with parentheses, as sin(1)."],
        ["abs(-2)", "Unknown function “abs”."],
        ["2^^3", "A value is missing before “^”."],
        ["foo", "Unknown name “foo”. Use x, y, pi, e, i, or inf."],
      ];
      for (const [source, want] of messages) {
        let got = "compiled";
        try {
          compileExpression(source, {});
        } catch (err) {
          got = err instanceof EmlError ? err.message : String(err);
        }
        if (got !== want) {
          ctx.fail("FAIL parser message", source, got, "want", want);
        } else console.log("parser message", source, got);
      }

      // A subtree shared through both inputs at every level: its cancellation records
      // are kept once, so 40 levels finish quickly instead of doubling per level.
      {
        let deep = E(ONE, ONE);
        for (let level = 0; level < 40; level += 1) deep = E(deep, deep);
        const started = Date.now();
        exactReport(deep, {}, { maxNodes: 80_000 });
        const took = Date.now() - started;
        if (took > 5000) {
          ctx.fail("FAIL deep shared circuit", took, "ms");
        } else console.log("deep shared circuit", took, "ms");
      }
    },
  },
];

export default checks;
