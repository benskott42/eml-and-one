import type { CheckModule } from "./_types";
import { makeCheckHelpers } from "./_helpers";
import { c, cdiv, close, eml } from "../complex";
import { circuitStats, describe, E, EmlError, evaluate, evaluateReport, input, isPure, type Node, ONE, rpnTokens, SINGULAR_INDET, SINGULAR_LN0, SINGULAR_RANGE, substitute, V } from "../node";
import { applyBinaryNode, applyUnaryNode, bindInput, constantNode, integerNode, literalNode, tAdd, tHalf, tI, tMul, tTwo, unaryNode } from "../library";
import { compileExpression, referenceExpression } from "../parse";
import { exactClose, exactEvaluate, exactParts, exactReport, exactToFloat, formatExact } from "../exact";
import { formatC, recognize } from "../format";
import { domainSub, naiveSub } from "../lowering";
import { applyProgram, nodeFromCompact, programK, programNode, SHORT_PROGRAMS } from "../programs";
import { acceptsConstantProgram } from "../golf";
import type { Decimal } from "decimal.js";

/**
 * Core EML constants, elementary functions, formatting, domain lowering, and short-program records.
 */
const checks: CheckModule[] = [
  {
    id: "core-basics",
    weight: 120,
    run(ctx) {
      const { check } = makeCheckHelpers(ctx);
      const e = eml(c(1), c(1));
      check("eml(1,1)=e", e, c(Math.E), 1e-15);
      check("0", evaluate(constantNode("0")), c(0), 1e-12);
      check("-1", evaluate(constantNode("-1")), c(-1), 1e-9);
      check("2", evaluate(constantNode("2")), c(2), 1e-9);
      check("1/2", evaluate(constantNode("1/2")), c(0.5), 1e-8);
      check("2/3", evaluate(constantNode("2/3")), c(2 / 3), 1e-8);
      check("sqrt2", evaluate(constantNode("sqrt(2)")), c(Math.SQRT2), 1e-6);
      check("i", evaluate(constantNode("i")), c(0, 1), 1e-6);
      check("pi", evaluate(constantNode("pi")), c(Math.PI), 1e-6);
      check("e const", evaluate(constantNode("e")), c(Math.E), 1e-12);
      function applyUnary(name: string, x: number, want: number, tol = 1e-6) {
        const node = applyUnaryNode(name, bindInput(c(x), "x"));
        const stats = circuitStats(node);
        const got = evaluate(node, { x: c(x) });
        check(`${name}(${x}) gates=${stats.dagGates} depth=${stats.depth}`, got, c(want), tol);
      }
      applyUnary("ln", 2, Math.log(2));
      applyUnary("ln", 0.5, Math.log(0.5));
      applyUnary("ln", Math.E, 1);
      applyUnary("exp", 0, 1);
      applyUnary("exp", 1, Math.E);
      applyUnary("exp", -1, 1 / Math.E);
      applyUnary("sqrt", 4, 2);
      applyUnary("sqrt", 2, Math.SQRT2);
      applyUnary("sqr", 7, 49);
      applyUnary("inv", 4, 0.25);
      applyUnary("minus", 3, -3);
      applyUnary("minus", -2.5, 2.5);
      applyUnary("sin", 0, 0);
      applyUnary("sin", Math.PI / 6, 0.5);
      applyUnary("sin", Math.PI / 2, 1);
      applyUnary("sin", Math.PI, 0, 1e-5);
      applyUnary("sin", 1, Math.sin(1));
      applyUnary("sin", 4, Math.sin(4), 1e-5);
      applyUnary("sin", -1, Math.sin(-1));
      applyUnary("cos", 0, 1);
      applyUnary("cos", Math.PI / 3, 0.5);
      applyUnary("cos", Math.PI, -1, 1e-5);
      applyUnary("cos", 10, Math.cos(10), 1e-4);
      applyUnary("tan", Math.PI / 4, 1, 1e-5);
      applyUnary("sinh", 0.7, Math.sinh(0.7), 1e-5);
      applyUnary("cosh", 0.7, Math.cosh(0.7), 1e-5);
      applyUnary("tanh", 0.7, Math.tanh(0.7), 1e-5);
      applyUnary("arcsin", 0.5, Math.asin(0.5), 1e-5);
      applyUnary("arccos", 0.5, Math.acos(0.5), 1e-5);
      applyUnary("arctan", 1, Math.PI / 4, 1e-5);
      applyUnary("arsinh", 0.8, Math.asinh(0.8), 1e-5);
      applyUnary("sigma", 0, 0.5, 1e-5);
      function applyBinary(name: string, x: number, y: number, want: number, tol = 1e-6) {
        const node = applyBinaryNode(name, bindInput(c(x), "x"), bindInput(c(y), "y"));
        check(`${name}(${x},${y})`, evaluate(node, { x: c(x), y: c(y) }), c(want), tol);
      }
      applyBinary("add", 3, 4, 7);
      applyBinary("sub", 3, 4, -1);
      applyBinary("mul", -2, -3, 6);
      applyBinary("mul", 2.5, 4, 10);
      applyBinary("div", 3, 4, 0.75);
      applyBinary("pow", 2, 10, 1024);
      applyBinary("pow", 9, 0.5, 3);
      applyBinary("log", 2, 8, 3);
      applyBinary("avg", 2, 8, 5);
      applyBinary("hypot", 3, 4, 5);
      const lnRpn = rpnTokens(substitute(unaryNode("ln"), { x: bindInput(c(2), "x") }));
      if (lnRpn?.join(" ") !== "1 1 x E 1 E E") {
        ctx.fail("FAIL ln rpn", lnRpn);
      }
      const exprs: [string, number][] = [
        ["e", Math.E],
        ["pi", Math.PI],
        ["i*i", -1],
        ["ln(2)", Math.log(2)],
        ["sin(pi/6)", 0.5],
        ["cos(pi/3)", 0.5],
        ["sqrt(2)", Math.SQRT2],
        ["2^10", 1024],
        ["(1+sqrt(5))/2", (1 + Math.sqrt(5)) / 2],
        ["log(2, 8)", 3],
        ["hypot(3, 4)", 5],
        ["2+2*2", 6],
        ["2^3^2", 512],
        ["-2^2", -4],
        ["2^-2^2", 1 / 16],
        ["2*-3^2", -18],
        ["(-2)^2", 4],
        ["tanh(1)", Math.tanh(1)],
        ["avg(2, 8)", 5],
        ["(-2)*(-3)", 6],
        ["exp(ln(7))", 7],
        ["0^1", 0],
        ["0^2", 0],
        ["sqrt(0)", 0],
        ["(1-1)^2", 0],
        ["400+400", 800],
        ["1000-1000", 0],
        ["2^10+2^10", 2048],
        ["1024-1024", 0],
        ["2^100-2^100", 0],
        ["(1e-6)^2", 1e-12],
        ["1000000-999999", 1],
        ["exp(-25)", Math.exp(-25)],
      ];
      for (const [source, want] of exprs) {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const ref = referenceExpression(source, {});
        check(`expr ${source}`, got, c(want), 1e-5);
        if (ref) check(`ref ${source}`, ref, c(want), 1e-9);
      }
      check("(1e-6)^2 tight", evaluate(compileExpression("(1e-6)^2", {})), c(1e-12), 1e-6);
      check("million minus exact", exactToFloat(exactEvaluate(compileExpression("1000000-999999", {}))), c(1), 1e-9);
      if (formatC(c(1e-9)) === "0" || formatC(c(Math.exp(-25))) === "0" || formatC(c(1e-20)) === "0") {
        ctx.fail("FAIL small values displayed as 0", formatC(c(1e-9)), formatC(c(Math.exp(-25))), formatC(c(1e-20)));
      }
      if (formatC(c(0, Infinity)) !== "∞i") {
        ctx.fail("FAIL imag infinity", formatC(c(0, Infinity)));
      }
      // A fraction twelve digits can show is not printed as the nearby integer.
      for (const [value, want] of [
        [c(2e9 / 3), "666666666.667"],
        [c(1e9 / 7), "142857142.857"],
        [c(500000000.5), "500000000.5"],
        [c(0, 1e10 / 3), "3.333333×10^9i"],
        [c(3 + 4e-13), "3"],
        [c(1e14 + 0.25), "100000000000000"],
        [c(0, 1 + 1e-10), "1.0000000001i"],
        [c(0, -(1 + 1e-13)), "−i"],
      ] as const) {
        if (formatC(value) !== want) {
          ctx.fail("FAIL float display digits", value, formatC(value), "want", want);
        }
      }
      // The imaginary coefficient keeps the digits the real part would show.
      for (const [source, want] of [
        ["i*(1+10^-12)", "1.000000000001i"],
        ["i*(1-10^-72)", `0.${"9".repeat(72)}i`],
        ["2-i*(1+3*10^-13)", "2 − 1.0000000000003i"],
        ["exp(i*pi/2)", "i"],
      ] as const) {
        const text = formatExact(exactEvaluate(compileExpression(source, {})));
        if (text !== want) {
          ctx.fail("FAIL exact imaginary digits", source, text, "want", want);
        }
      }
      const expTiny = evaluate(compileExpression("exp(-50)", {}));
      const expWant = Math.exp(-50);
      if (Math.abs(expTiny.re - expWant) > 1e-6 * expWant || expTiny.im !== 0) {
        ctx.fail("FAIL exp(-50)", expTiny, expWant);
      }
      const belowCut = evaluate(compileExpression("ln(-1-1e-9*i)", {}));
      if (!(belowCut.im < 0)) {
        ctx.fail("FAIL ln below the cut", belowCut);
      }
      check("sqrt(-4) via radical", evaluate(compileExpression("√-4", {})), c(0, 2), 1e-6);

      check("hypot huge", evaluate(compileExpression("hypot(1e200,1e200)", {})), c(Math.hypot(1e200, 1e200)), 1e-6);
      const hypotTiny = evaluate(compileExpression("hypot(1e-200,1e-200)", {}));
      const hypotTinyWant = Math.hypot(1e-200, 1e-200);
      if (Math.abs(hypotTiny.re - hypotTinyWant) > 1e-6 * hypotTinyWant || Math.abs(hypotTiny.im) > 1e-9 * hypotTinyWant) {
        ctx.fail("FAIL hypot tiny", hypotTiny, hypotTinyWant);
      }

      if (recognize(c(1e-9)) === "0" || recognize(c(0.999999996973)) === "1" || recognize(c(3.141592654)) !== null || recognize(c(Math.PI)) !== "π") {
        ctx.fail("FAIL recognize", recognize(c(1e-9)), recognize(c(0.999999996973)), recognize(c(3.141592654)), recognize(c(Math.PI)));
      }
      try {
        literalNode("0x10");
        ctx.fail("FAIL 0x10 was accepted");
      } catch {
        // hex is not a decimal literal
      }
      for (const blank of ["", " "]) {
        try {
          literalNode(blank);
          ctx.fail("FAIL blank literal was accepted", JSON.stringify(blank));
        } catch (err) {
          if (!(err instanceof EmlError)) {
            ctx.fail("FAIL blank literal", err);
          }
        }
      }
      try {
        evaluate({ type: "eml", a: ONE } as Node);
        ctx.fail("FAIL missing child did not throw");
      } catch (err) {
        if (!(err instanceof EmlError) || err.message !== "Could not evaluate this circuit.") {
          ctx.fail("FAIL missing child", err);
        }
      }
      for (const name of ["toString", "constructor", "x"]) {
        try {
          evaluate(V(name), {});
          ctx.fail("FAIL unbound name was accepted", name);
        } catch (err) {
          if (!(err instanceof EmlError)) {
            ctx.fail("FAIL unbound name", name, err);
          }
        }
      }
      check("own toString binding", evaluate(V("toString"), { toString: c(4) }), c(4), 1e-9);
      if (rpnTokens(ONE, 0) !== null || describe(V("abcdefghij"), 4) !== null) {
        ctx.fail("FAIL leaf budget", rpnTokens(ONE, 0), describe(V("abcdefghij"), 4));
      }
      if (rpnTokens(ONE, 1)?.join(" ") !== "1" || describe(ONE, 1) !== "1") {
        ctx.fail("FAIL leaf within budget", rpnTokens(ONE, 1), describe(ONE, 1));
      }
      check("integer 6", evaluate(integerNode(6)), c(6), 1e-8);

      const lnNeg = evaluate(compileExpression("ln(-1)", {}));
      const lnNegRef = referenceExpression("ln(-1)", {});
      check("ln(-1)", lnNeg, c(0, Math.PI), 1e-6);
      if (!lnNegRef) {
        ctx.fail("FAIL ln(-1) reference missing");
      } else {
        check("ln(-1) reference", lnNegRef, c(0, Math.PI), 1e-9);
      }
      const cube = evaluate(compileExpression("(-8)^(1/3)", {}));
      check("cube root of -8", cube, c(1, Math.sqrt(3)), 1e-5);
      const divNeg = evaluate(compileExpression("(-1)/0", {}));
      if (divNeg.re !== -Infinity || divNeg.im !== 0) {
        ctx.fail("FAIL (-1)/0", divNeg);
      }
      const divPos = evaluate(compileExpression("1/0", {}));
      if (divPos.re !== Infinity || divPos.im !== 0) {
        ctx.fail("FAIL 1/0", divPos);
      }

      check("arcsin(2)", evaluate(compileExpression("arcsin(2)", {})), c(Math.PI / 2, -1.3169578969248166), 1e-6);
      check("arccos(2)", evaluate(compileExpression("arccos(2)", {})), c(0, 1.3169578969248166), 1e-6);

      const hugeQuotient = evaluate(compileExpression("1e308/2", {}));
      if (Math.abs(hugeQuotient.re - 5e307) > 1e-6 * 5e307 || hugeQuotient.im !== 0) {
        ctx.fail("FAIL 1e308/2", hugeQuotient);
      }
      const tanImag = evaluate(applyUnaryNode("tan", bindInput(c(0, 2), "z")), { z: c(0, 2) });
      check("tan(2i)", tanImag, c(0, Math.tanh(2)), 1e-6);
      const divNegZero = cdiv(c(1), c(-0));
      if (divNegZero.re !== -Infinity || divNegZero.im !== 0) {
        ctx.fail("FAIL direct 1/(-0)", divNegZero);
      }
      const below = evaluate(compileExpression("ln(-1-1e-9*i)", {}));
      if (!(below.im < 0)) {
        ctx.fail("FAIL ln just below the cut", below);
      }
      if (constantNode("pi").type !== "eml" || constantNode("i").type !== "eml" || constantNode("e").type !== "eml") {
        ctx.fail("FAIL constants collapsed", constantNode("pi").type, constantNode("i").type, constantNode("e").type);
      }
      for (const source of ["0^2", "sqrt(0)", "(1-1)^2", "(-1)/0"]) {
        const tokens = rpnTokens(compileExpression(source, {}), 40);
        if (tokens?.includes("undefined")) {
          ctx.fail("FAIL program tape", source, tokens);
        }
      }
      const sinNode = applyUnaryNode("sin", bindInput(c(Math.PI / 6), "x"));
      if (sinNode.type !== "eml") {
        ctx.fail("FAIL sin(pi/6) was not kept as an EML circuit");
      }
      function sharedPow(depth: number): Node {
        let node: Node = ONE;
        for (let i = 0; i < depth; i++) node = E(node, node);
        return node;
      }
      let nested = "1";
      for (let i = 0; i < 3; i++) nested = `eml(${nested}, ${nested})`;
      if (describe(sharedPow(3)) !== nested) {
        ctx.fail("FAIL shared describe", describe(sharedPow(3)));
      }
      const deepDescribe = sharedPow(20);
      const describeStart = performance.now();
      const deepText = describe(deepDescribe);
      if (deepText !== null || performance.now() - describeStart > 50) {
        ctx.fail("FAIL deep describe", deepText, performance.now() - describeStart);
      }
      if (rpnTokens(deepDescribe) !== null) {
        ctx.fail("FAIL deep rpn", rpnTokens(deepDescribe));
      }
      const sharedGate = E(ONE, ONE);
      if (rpnTokens(E(sharedGate, sharedGate))?.join(" ") !== "1 1 E 1 1 E E") {
        ctx.fail("FAIL shared rpn", rpnTokens(E(sharedGate, sharedGate)));
      }
      if (describe(unaryNode("ln")) === null) {
        ctx.fail("FAIL ln describe");
      }
      const lnStats = circuitStats(substitute(unaryNode("ln"), { x: bindInput(c(2), "x") }));
      if (lnStats.dagGates !== 3 || lnStats.depth !== 3) {
        ctx.fail("FAIL ln stats", lnStats);
      }
      const powStats = circuitStats(sharedPow(8));
      if (powStats.dagGates !== 8 || powStats.depth !== 8) {
        ctx.fail("FAIL shared stats", powStats);
      }
      evaluate(sharedPow(8));
    },
  },
  {
    id: "core-domain-and-records",
    weight: 150,
    run(ctx) {
      const { absClose } = makeCheckHelpers(ctx);
      const ii = tI();
      const a = tAdd(tTwo(), tMul(tHalf(), ii));
      const b4 = tAdd(ONE, tMul(integerNode(4), ii));
      const b3 = tAdd(ONE, tMul(integerNode(3), ii));
      const b7 = tMul(integerNode(7), ii);
      const sub4 = domainSub(a, b4);
      absClose("a-(1+4i)", evaluate(sub4), 1, -3.5);
      absClose("a-(1+4i) exact", exactToFloat(exactEvaluate(sub4)), 1, -3.5);
      const naive4 = evaluate(naiveSub(a, b4));
      if (Math.abs(naive4.im + 3.5) < 0.2) {
        ctx.fail("FAIL naive a-(1+4i) should miss 1-3.5i", naive4);
      }
      absClose("naive a-(1+4i) folded", naive4, 1, -3.5 + 2 * Math.PI, 1e-8);
      absClose("a-(1+3i) control", evaluate(domainSub(a, b3)), 1, -2.5);
      absClose("a-7i", evaluate(domainSub(a, b7)), 2, -6.5);
      const naive7 = evaluate(naiveSub(a, b7));
      if (Math.abs(naive7.im + 6.5) < 0.2) {
        ctx.fail("FAIL naive a-7i", naive7);
      }
      const b35 = tAdd(tTwo(), tMul(tAdd(integerNode(3), tHalf()), ii));
      absClose("2-(2+3.5i)", evaluate(domainSub(tTwo(), b35)), 0, -3.5);
      absClose("2-(1-4i)", evaluate(domainSub(tTwo(), tAdd(ONE, tMul(integerNode(-4), ii)))), 1, 4);
      const product = evaluate(compileExpression("(1+2*i)*(1+3*i)", {}));
      absClose("(1+2i)(1+3i)", product, -5, 5);
      const lnOfNeg = evaluate(compileExpression("ln(-2)", {}));
      absClose("ln(-2)", lnOfNeg, Math.log(2), Math.PI);
      absClose("ln(-2) exact", exactToFloat(exactEvaluate(compileExpression("ln(-2)", {}))), Math.log(2), Math.PI);
      absClose("ln(-0.4+0.2i)", evaluate(compileExpression("ln(-0.4+0.2*i)", {})), Math.log(Math.hypot(-0.4, 0.2)), Math.atan2(0.2, -0.4));
      if (formatC(c(1, 1e-8)).includes("i") === false) {
        ctx.fail("FAIL small imag dropped", formatC(c(1, 1e-8)));
      }
      const above = E(input(c(0), "0"), input(c(-2, 1e-300), "z"));
      const belowTiny = E(input(c(0), "0"), input(c(-2, -1e-300), "z"));
      const aboveIm = exactEvaluate(above).im.neg();
      const belowIm = exactEvaluate(belowTiny).im.neg();
      if (!(aboveIm.gt(0) && belowIm.lt(0))) {
        ctx.fail("FAIL ±1e-300 sides", aboveIm.toString(), belowIm.toString());
      }
      for (const id of ["0", "-1", "2", "1/2", "i", "pi", "sqrt(2)", "e"]) {
        if (!isPure(constantNode(id))) {
          ctx.fail("FAIL impure", id);
        }
      }
      for (const id of ["-2", "-1/2", "3", "1/2-strict"]) {
        if (!isPure(programNode(id))) {
          ctx.fail("FAIL impure program", id);
        }
      }
      if (!isPure(literalNode("10")) || !isPure(literalNode("0.1"))) {
        ctx.fail("FAIL impure literal");
      }
      if (programK("-2") !== 25 || programK("-1/2") !== 29 || programK("1/2") !== 29 || programK("1/2-strict") !== 31) {
        ctx.fail("FAIL record lengths", programK("-2"), programK("-1/2"), programK("1/2-strict"));
      }
      if (!exactClose(exactEvaluate(programNode("-2")), -2, 0, 15)) {
        ctx.fail("FAIL -2 value");
      }
      const strictHalf = exactReport(programNode("1/2-strict"));
      if (strictHalf.singular !== null || !exactClose(strictHalf.value, 0.5, 0, 15)) {
        ctx.fail("FAIL strict 1/2", formatExact(strictHalf.value), strictHalf.singular);
      }
      for (const [id, re] of [
        ["-1/2-strict", -0.5],
        ["1/2-alt", 0.5],
      ] as const) {
        if (programK(id) !== 31) {
          ctx.fail("FAIL K31 word length", id, programK(id));
        }
        const wide = exactReport(programNode(id));
        const floated = evaluateReport(programNode(id));
        if (
          wide.touchedLn0 ||
          floated.touchedLn0 ||
          wide.singular !== null ||
          !acceptsConstantProgram(programNode(id), re, 0)
        ) {
          ctx.fail("FAIL K31 no-inf half", id, wide.touchedLn0, floated.touchedLn0, wide.singular);
        }
      }
      const halfReport = evaluateReport(programNode("1/2"));
      if (halfReport.singular !== null || !halfReport.touchedLn0) {
        ctx.fail("FAIL 1/2 ln 0 should cancel", halfReport.singular, halfReport.touchedLn0);
      }
      const third = exactParts(1, 0).re.div(3);
      const storedPi = exactEvaluate(programNode("pi")).re;
      const checkRecord = (id: string, k: number, re: Decimal.Value, im: Decimal.Value, usesLn0: boolean) => {
        if (programK(id) !== k) {
          ctx.fail("FAIL record length", id, programK(id), k);
        }
        const report = exactReport(programNode(id), {}, { maxNodes: 200_000 });
        if (report.singular !== null || report.touchedLn0 !== usesLn0 || !exactClose(report.value, re, im, 30)) {
          ctx.fail("FAIL record value", id, formatExact(report.value), report.singular, report.touchedLn0);
        }
      };
      checkRecord("-ipi", 45, 0, storedPi.neg(), true);
      checkRecord("-ipi-strict", 47, 0, storedPi.neg(), false);
      checkRecord("4", 39, 4, 0, false);
      checkRecord("2/3", 39, third.mul(2), 0, false);
      checkRecord("-1/3", 41, third.neg(), 0, false);
      checkRecord("-3", 35, -3, 0, false);
      checkRecord("1/3", 35, third, 0, true);
      checkRecord("1/3-strict", 37, third, 0, false);
      const thirdImpostor = "111E1111E11E11E1E11EEEEE11EEE1E1EEE1E";
      if (
        thirdImpostor.length !== 37 ||
        Object.values(SHORT_PROGRAMS).includes(thirdImpostor) ||
        exactClose(exactEvaluate(nodeFromCompact(thirdImpostor), {}, { maxNodes: 200_000 }), 1 / 3, 0, 12)
      ) {
        ctx.fail("FAIL 1/3 impostor was stored or accepted");
      }
      const lnZero = evaluateReport(compileExpression("ln(0)", {}));
      if (lnZero.value.re !== -Infinity || lnZero.singular !== SINGULAR_LN0) {
        ctx.fail("FAIL ln 0", lnZero);
      }
      const expNegInf = evaluate(compileExpression("exp(ln(0))", {}));
      if (expNegInf.re !== 0 || expNegInf.im !== 0) {
        ctx.fail("FAIL exp(-inf)", expNegInf);
      }
      const indeterminate = eml(c(Infinity), c(Infinity));
      if (!Number.isNaN(indeterminate.re)) {
        ctx.fail("FAIL inf-inf", indeterminate);
      }
      const zeroInf = evaluateReport(compileExpression("0*(1/0)", {}));
      if (zeroInf.singular !== SINGULAR_INDET || !Number.isNaN(zeroInf.value.re) || !Number.isNaN(zeroInf.value.im)) {
        ctx.fail("FAIL 0*inf", zeroInf);
      }
      const zeroInfExact = exactReport(compileExpression("0*(1/0)", {}), {}, { maxNodes: 20_000 });
      if (zeroInfExact.singular !== SINGULAR_INDET || !zeroInfExact.value.re.isNaN()) {
        ctx.fail("FAIL exact 0*inf", formatExact(zeroInfExact.value), zeroInfExact.singular);
      }
    },
  },
  {
    id: 0,
    weight: 615,
    run(ctx) {
      const { check } = makeCheckHelpers(ctx);
      const huge = compileExpression("asinh(1e200)", {});
      const wide = exactToFloat(exactEvaluate(huge));
      check("asinh huge exact", wide, c(Math.asinh(1e200)), 1e-8);
    },
  },
  {
    id: 1,
    weight: 26,
    run(ctx) {
      const at = exactReport(compileExpression("atan(1/0)", {}));
      if (at.value.im.isFinite() || at.singular === null) {
        ctx.fail("FAIL atan(inf) circuit", formatExact(at.value), at.singular);
      }
    },
  },
  {
    id: 2,
    weight: 99,
    run(ctx) {
      const { check } = makeCheckHelpers(ctx);
      const neg = integerNode(-1000);
      const wide = exactToFloat(exactEvaluate(neg));
      check("integer -1000 exact", wide, c(-1000), 1e-9);
      const narrow = evaluate(neg);
      if (Number.isFinite(narrow.re) && !close(narrow, c(-1000), 1e-6)) {
        ctx.fail("FAIL integer -1000 float", narrow);
      }
    },
  },
  {
    id: 3,
    weight: 3,
    run(ctx) {
      const pole = evaluate(compileExpression("tan(pi/2)", {}));
      if (Number.isFinite(pole.re) && Math.abs(pole.re) < 1e6) {
        ctx.fail("FAIL tan(pi/2) stayed small", pole);
      }
    },
  },
  {
    id: 4,
    weight: 1964,
    run(ctx) {
      const { check } = makeCheckHelpers(ctx);
      const sinhNode = compileExpression("sinh(710)", {});
      const coshNode = compileExpression("cosh(710)", {});
      check("sinh(710) exact", exactToFloat(exactEvaluate(sinhNode)), c(Math.sinh(710)), 1e-6);
      check("cosh(710) exact", exactToFloat(exactEvaluate(coshNode)), c(Math.cosh(710)), 1e-6);
    },
  },
  {
    id: 5,
    weight: 3,
    run(ctx) {
      const rawMul = applyProgram("mul", {
        x: E(input({ re: -Infinity, im: 0 }, "−∞"), ONE),
        y: applyProgram("div", { x: input({ re: 5, im: 0 }, "5"), y: input({ re: 0, im: 0 }, "0") }),
      });
      const rawReport = exactReport(rawMul);
      if (rawReport.singular !== SINGULAR_INDET || !rawReport.value.re.isNaN() || !rawReport.value.im.isNaN()) {
        ctx.fail("FAIL raw mul(exp(−∞), 5/0)", formatExact(rawReport.value), rawReport.singular);
      }
    },
  },
  {
    id: 6,
    weight: 48,
    run(ctx) {
      const logged = compileExpression("ln(-0)", {});
      const floated = evaluateReport(logged);
      const exact = exactReport(logged);
      const sameImag = floated.value.im > 0 && exact.value.im.isPos() && floated.value.re === -Infinity && exact.value.re.isNeg() && !exact.value.re.isFinite();
      if (!sameImag) {
        ctx.fail("FAIL ln(−0) banks", floated.value, formatExact(exact.value));
      }
      const below = evaluateReport(compileExpression("ln(-2-1e-20*i)", {}));
      const dust = evaluateReport(compileExpression("ln(-2-1e-35*i)", {}));
      const belowExact = exactReport(compileExpression("ln(-2-1e-20*i)", {}));
      if (!below.nearCut || !dust.nearCut || !belowExact.value.im.isNeg()) {
        ctx.fail("FAIL near-cut log", below.nearCut, below.value, dust.nearCut, dust.value, formatExact(belowExact.value));
      }
      const clear = evaluateReport(compileExpression("ln(-2-1e-12*i)", {}));
      if (clear.nearCut || clear.value.im >= 0) {
        ctx.fail("FAIL log clearly below the cut was flagged", clear.value, clear.nearCut);
      }
    },
  },
  {
    id: 7,
    weight: 1337,
    run(ctx) {
      const huge = evaluateReport(compileExpression("x-y", { x: V("x"), y: V("y") }), { x: c(1), y: c(1e200, 2e7) });
      if (huge.singular !== SINGULAR_RANGE || !Number.isNaN(huge.value.re)) {
        ctx.fail("FAIL huge subtrahend message", huge.singular, huge.value);
      }
    },
  },
];

export default checks;
