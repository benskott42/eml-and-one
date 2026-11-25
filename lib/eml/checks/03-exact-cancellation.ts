import type { CheckModule } from "./_types";
import { circuitStats, EmlError, evaluate, evaluateReport, isPure, type Node, SINGULAR_LN0, V } from "../node";
import { literalNode, tArsinh, tSub } from "../library";
import { compileExpression, referenceExpression } from "../parse";
import { beyondFloatBound, exactClose, exactEvaluate, exactReport, exactToFloat, formatExact } from "../exact";
import { c, cdiv, cexp, clog, close, cmul, csin, ctan } from "../complex";
import { makeCheckHelpers, relClose } from "./_helpers";
import { exactScreen, underflowDisclosure } from "../history";
import { provenInteger } from "../facts";

/**
 * Exact cancellation, high-precision subtractions, scaled arithmetic, and conformance checks.
 */
const checks: CheckModule[] = [
  {
    id: 9,
    weight: 375,
    run(ctx) {
      const rows: Array<{ source: string; re: string; im: string; vars?: Record<string, Node> }> = [
        { source: "e-1-1", re: "0.71828182845904523536028747135266249775724709369996", im: "0" },
        { source: "pi-1-1", re: "1.1415926535897932384626433832795028841971693993751", im: "0" },
        { source: "10-3-3", re: "4", im: "0" },
        { source: "2*e-e-e", re: "0", im: "0" },
        { source: "arcosh(e-1)", re: "1.1364211033963852565125274801058381954056538237393", im: "0" },
        { source: "arcosh(pi-1)", re: "1.3950997261071488078584719796130035077474855890456", im: "0" },
        { source: "sin(1.5-1-1)", re: "-0.4794255386042030002732879352155713880818033679406", im: "0" },
        { source: "pi-1-1-1", re: "0.14159265358979323846264338327950288419716939937511", im: "0" },
        { source: "(1.5-7)-7+7", re: "-5.5", im: "0" },
        { source: "x-y-y", re: "-3.5", im: "0", vars: { x: literalNode("0.5"), y: literalNode("2") } },
        { source: "(2+3i)-1-1", re: "0", im: "3" },
        // The two identities subComplement still folds.
        { source: "e-(e-1)", re: "1", im: "0" },
        { source: "(e-1)-e", re: "-1", im: "0" },
      ];
      for (const row of rows) {
        const node = compileExpression(row.source, row.vars ?? {});
        const hw = evaluateReport(node);
        const ex = exactReport(node);
        const want = c(Number(row.re), Number(row.im));
        const err = Math.hypot(hw.value.re - want.re, hw.value.im - want.im);
        const scale = Math.max(Math.hypot(want.re, want.im), 1);
        const hardwareOk = !hw.singular && err <= 1e-12 * scale;
        const exactOk = ex.singular === null && exactClose(ex.value, row.re, row.im, 40);
        if (!hardwareOk || !exactOk) {
          ctx.fail("FAIL repeated subtraction", row.source, hw.value, hw.singular, formatExact(ex.value), ex.singular, "want", row.re, row.im);
        }
      }
    },
  },
  {
    id: "core-conformance",
    weight: 120,
    run(ctx) {
      const { check } = makeCheckHelpers(ctx);
      const zeroSubtrahends = ["3-ln(2/2)", "1+ln(2/2)", "1-ln(1/1)", "1-log(2,1)", "1-sin(0*pi)"];
      for (const source of zeroSubtrahends) {
        const node = compileExpression(source, {});
        const got = evaluateReport(node);
        const want = source.startsWith("3") ? c(3) : c(1);
        const exact = exactToFloat(exactEvaluate(node));
        if (!close(got.value, want, 1e-9) || got.overflowed || !close(exact, want, 1e-9)) {
          ctx.fail("FAIL zero subtrahend", source, got.value, got.overflowed, exact);
        }
      }

      const asinhCases: Array<[string, number]> = [
        ["asinh(0.5-3)", Math.asinh(-2.5)],
        ["asinh(-sqrt(2))", Math.asinh(-Math.SQRT2)],
        ["asinh(cos(3))", Math.asinh(Math.cos(3))],
        ["asinh(-2)", Math.asinh(-2)],
        ["asinh(0)", 0],
      ];
      for (const [source, want] of asinhCases) {
        const got = evaluate(compileExpression(source, {}));
        if (!close(got, c(want), 1e-8) || Math.abs(got.im) > 1e-8) {
          ctx.fail("FAIL asinh", source, got);
        }
      }

      const bigSub = evaluate(compileExpression("2-1e8*i", {}));
      if (!close(bigSub, c(2, -1e8), 1e-6)) {
        ctx.fail("FAIL 2-1e8 i", bigSub);
      }
      if (!isPure(literalNode("1e-6")) || !isPure(literalNode("2.5E-3")) || !isPure(literalNode("1.5e20")) || isPure(literalNode("-0"))) {
        ctx.fail("FAIL impure typed literal");
      }
      if (!Number.isNaN(cmul(c(0), c(Infinity)).re) || !Number.isNaN(cdiv(c(NaN), c(0)).re)) {
        ctx.fail("FAIL 0·∞ or NaN/0");
      }
      const tangent = ctan(c(1, 800));
      if (!close(tangent, c(0, 1), 1e-6)) {
        ctx.fail("FAIL tan(1+800i)", tangent);
      }
      const deep = `${"(".repeat(10000)}1${")".repeat(10000)}`;
      if (evaluate(compileExpression(deep, {})).re !== 1) {
        ctx.fail("FAIL 10000 parentheses");
      }
      const many = Array.from({ length: 4000 }, () => "1").join("+");
      if (!close(evaluate(compileExpression(many, {})), c(4000), 1e-8)) {
        ctx.fail("FAIL long sum");
      }
      const sinFloat = csin(c(Math.PI / 6));
      if (!close(sinFloat, c(0.5), 1e-15) || Math.abs(sinFloat.im) > 1e-15) {
        ctx.fail("FAIL float sin(pi/6)", sinFloat);
      }
      function conformance(name: string, source: string, want: { re: number; im: number }, singular: string | null = null) {
        const node = compileExpression(source, {});
        const floated = evaluateReport(node);
        const exact = exactReport(node, {}, { maxNodes: 200_000 });
        const ref = referenceExpression(source, {});
        if (!close(floated.value, want, 1e-9) || floated.singular !== singular) {
          ctx.fail("FAIL float", name, floated.value, floated.singular);
        }
        if (!exactClose(exact.value, want.re, want.im, 12) || exact.singular !== singular) {
          ctx.fail("FAIL exact", name, formatExact(exact.value), exact.singular);
        }
        if (!ref || !close(ref, want, 1e-9)) {
          ctx.fail("FAIL reference", name, ref);
        }
      }
      conformance("ln just below the cut", "ln(-1-1e-15*i)", c(0, -Math.PI));
      conformance("0-ln(0)", "0-ln(0)", c(Infinity, 0), SINGULAR_LN0);

      check("implicit i", evaluate(compileExpression("2-1e16i", {})), evaluate(compileExpression("2-1e16*i", {})), 0);

      check("tan(1+800i) juxtaposition", evaluate(compileExpression("tan(1+800i)", {})), c(0, 1), 1e-6);

      check("big integer sub is not the zero program", evaluate(compileExpression("10000000000000001-10000000000000000", {})), c(1), 0);

      check("exp(800)/exp(799)", evaluate(compileExpression("exp(800)/exp(799)", {})), c(Math.E), 1e-12);
      check("tan(1+800i)", evaluate(compileExpression("tan(1+800*i)", {})), c(0, 1), 1e-6);
      check("tan(1-800i)", evaluate(compileExpression("tan(1-800*i)", {})), c(0, -1), 1e-6);
      check("tan(1-i)", evaluate(compileExpression("tan(1-i)", {})), ctan(c(1, -1)), 1e-6);
      check("tan(1+i)", evaluate(compileExpression("tan(1+i)", {})), ctan(c(1, 1)), 1e-6);
      if (!close(ctan(c(1, -1)), c(0.27175258531951174, -1.0839233273386948), 1e-9)) {
        ctx.fail("FAIL ctan negative imag", ctan(c(1, -1)));
      }

      if (!close(evaluate(literalNode("5.")), c(5), 0)) {
        ctx.fail("FAIL literal 5.", evaluate(literalNode("5.")));
      }

      if (close(c(8e-12), c(1e-12), 1e-6)) {
        ctx.fail("FAIL close accepts a 700% error near 1e-12");
      }
    },
  },
  {
    id: 10,
    weight: 19,
    run(ctx) {
      // A variable is not the integer 0, so y = 0 at runtime still runs the scaled
      // circuit. √(b²) is 0 there, k is 1, and both modes are that gate result.
      const bounds = [
        { x: c(5), y: c(0) },
        { x: c(0), y: c(0) },
      ];
      for (const source of ["x-y", "x+y"]) {
        const node = compileExpression(source, { x: V("x"), y: V("y") });
        const length = circuitStats(node).rpnLength;
        if (node === V("x") || length < BigInt(500)) {
          ctx.fail("FAIL variable zero left the scaled circuit", source, length.toString());
        }
        for (const env of bounds) {
          const got = evaluateReport(node, env);
          const exact = exactReport(node, env);
          const want = env.x;
          // The scaled gates agree through 70 digits. The last places are dust, not a dropped term.
          const exactOk = exact.singular === null && exactClose(exact.value, want.re, want.im, 70);
          if (got.singular || !close(got.value, want, 1e-8) || !exactOk) {
            ctx.fail("FAIL variable zero", source, env, got.value, got.singular, formatExact(exact.value), exact.singular);
          }
        }
      }
    },
  },
  {
    id: 11,
    weight: 3681,
    run(ctx) {
      const tiny = [
        ["1e-100-3e-100", c(-2e-100)],
        ["0-1e-90", c(-1e-90)],
      ] as const;
      for (const [source, want] of tiny) {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const exact = exactToFloat(exactEvaluate(node));
        if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9)) {
          ctx.fail("FAIL tiny difference", source, got, exact, want);
        }
      }
      for (const source of ["1-1e-72", "1-1e-80"]) {
        const text = formatExact(exactEvaluate(compileExpression(source, {})));
        if (text === "1" || !text.includes("999")) {
          ctx.fail("FAIL exact residual digits", source, text);
        }
      }
      const subnormal = compileExpression("5e-324", {});
      const sub = evaluateReport(subnormal);
      const subExact = exactToFloat(exactEvaluate(subnormal));
      if (!sub.underflowed || sub.value.re !== 0 || underflowDisclosure(sub.value, sub.underflowed) !== "underflowed to 0; not a mathematical zero") {
        ctx.fail("FAIL subnormal disclosure", sub.value, sub.underflowed);
      }
      if (!beyondFloatBound(sub.value, subExact)) {
        ctx.fail("FAIL subnormal exact disagrees and must replace the float 0", sub.value, subExact);
      }
      const computing = exactScreen("computing");
      const cancelled = exactScreen("cancelled", "2.718");
      const filled = exactScreen("ready", "2.718281828");
      if (computing.text !== "computing" || computing.text.includes("2.718") || cancelled.text !== "—" || cancelled.note !== "cancelled" || filled.text !== "2.718281828" || filled.note !== null) {
        ctx.fail("FAIL exact screen", computing, cancelled, filled);
      }
      const pi = Math.PI;
      const halfTurn = (got: { re: number; im: number }, want: { re: number; im: number }) => Object.is(got.re, want.re) && Object.is(got.im, want.im);
      for (const sign of [1, -1]) {
        const neg = cexp(c(Number.NEGATIVE_INFINITY, sign * pi));
        const pos = cexp(c(Number.POSITIVE_INFINITY, sign * pi));
        if (!halfTurn(neg, c(-0, -0)) || !halfTurn(pos, c(Number.NEGATIVE_INFINITY, 0))) {
          ctx.fail("FAIL half-turn exponential", sign, neg, pos);
        }
      }
      const lnNegInf = clog(c(Number.NEGATIVE_INFINITY));
      const lnNegZero = clog(c(-0));
      if (!Object.is(lnNegInf.im, -pi) || lnNegInf.re !== Number.POSITIVE_INFINITY || !Object.is(lnNegZero.im, -pi) || lnNegZero.re !== Number.NEGATIVE_INFINITY) {
        ctx.fail("FAIL lower-bank log", lnNegInf, lnNegZero);
      }
      for (const source of ["ln(-0)", "ln(-inf)"]) {
        const composed = evaluate(compileExpression(source, {}));
        const real = source === "ln(-0)" ? Number.NEGATIVE_INFINITY : Number.POSITIVE_INFINITY;
        if (!Object.is(composed.im, pi) || composed.re !== real) {
          ctx.fail("FAIL composed log keeps +π", source, composed);
        }
      }
      for (const source of ["sqrt(0)", "sqrt(-0)"]) {
        const node = compileExpression(source, {});
        const got = evaluate(node);
        const exact = exactEvaluate(node);
        const wantRe = source === "sqrt(-0)" ? -0 : 0;
        if (!Object.is(got.re, wantRe) || got.im !== 0 || !exact.re.eq(0) || !exact.im.eq(0)) {
          ctx.fail("FAIL sqrt zero", source, got, formatExact(exact));
        }
        if (source === "sqrt(-0)" && !exact.re.isNegative()) {
          ctx.fail("FAIL sqrt(-0) lost its sign", formatExact(exact));
        }
      }
      const tinyY = [c(0), c(-0), c(Number.MIN_VALUE), c(-Number.MIN_VALUE)];
      for (const source of ["x-y", "x+y"]) {
        const node = compileExpression(source, { x: V("x"), y: V("y") });
        for (const y of tinyY) {
          const env = { x: c(5), y };
          const got = evaluate(node, env);
          const exact = exactToFloat(exactEvaluate(node, env));
          const want = source === "x-y" ? c(5 - y.re, -y.im) : c(5 + y.re, y.im);
          if (!relClose(got, want, 1e-9) || !relClose(exact, want, 1e-9)) {
            ctx.fail("FAIL variable tiny y", source, y, got, exact, want);
          }
        }
        const seen = evaluate(node, { x: c(0), y: c(1e-300) });
        const opposite = evaluate(node, { x: c(0), y: c(-1e-300) });
        const flipped = source === "x-y" ? seen.re < 0 && opposite.re > 0 : seen.re > 0 && opposite.re < 0;
        if (!flipped) {
          ctx.fail("FAIL sign mutation", source, seen, opposite);
        }
        const subnormal = evaluateReport(node, { x: c(0), y: c(Number.MIN_VALUE) });
        const subExact = exactToFloat(exactEvaluate(node, { x: c(0), y: c(Number.MIN_VALUE) }));
        const subSigned = source === "x-y" ? subnormal.value.re < 0 : subnormal.value.re > 0;
        const bothZero = subnormal.value.re === 0 && subExact.re === 0;
        if (!subSigned && !subnormal.underflowed && !beyondFloatBound(subnormal.value, subExact) && !bothZero) {
          ctx.fail("FAIL subnormal sign", source, subnormal.value, subExact, subnormal.underflowed);
        }
      }
      const sqrtZero = evaluate(compileExpression("sqrt(0)", {}));
      const sqrtNegZero = evaluate(compileExpression("sqrt(-0)", {}));
      if (Object.is(sqrtZero.re, sqrtNegZero.re)) {
        ctx.fail("FAIL sqrt sign mutation", sqrtZero, sqrtNegZero);
      }
      if (beyondFloatBound(c(0), c(1e-90)) !== true || beyondFloatBound(c(1), c(1)) !== false || beyondFloatBound(c(1), c(1 + 1e-12)) !== false || beyondFloatBound(c(1), c(1 + 1e-6)) !== true) {
        ctx.fail("FAIL float bound");
      }
      // 13 to 15 digits print as an integer, so a wrong printed digit is flagged.
      const longInteger: [number, number, boolean][] = [
        [999999999999985, 1e15, true], // 10^30/10^15
        [999999999999978, 1e15 + 0.5, true], // 10^15 + 0.5
        [2 ** 40, 2 ** 40, false],
        [123456789012345, 123456789012345.4, false],
        [1e12, 1e12 + 0.3, false],
      ];
      for (const [floated, exact, want] of longInteger) {
        if (beyondFloatBound(c(floated), c(exact)) !== want) {
          ctx.fail("FAIL float bound long integer", floated, exact, "want", want);
        }
      }
    },
  },
  {
    id: 12,
    weight: 78,
    run(ctx) {
      const negative = evaluate(tArsinh(V("x")), { x: c(-2) });
      const zero = evaluate(tArsinh(V("x")), { x: c(0) });
      if (!close(negative, c(Math.asinh(-2)), 1e-8) || !close(zero, c(0), 0)) {
        ctx.fail("FAIL variable asinh", negative, zero);
      }
    },
  },
  {
    id: 13,
    weight: 1,
    run(ctx) {
      // Float64 cannot recover a real 2 beside an imaginary 10^16 through exp and ln:
      // one ulp of the angle is already larger than 2. Exact mode still has both.
      const scaledImag = evaluate(compileExpression("2-1e16*i", {}));
      if (!Number.isFinite(scaledImag.im) || Math.abs(scaledImag.im + 1e16) / 1e16 > 1e-6) {
        ctx.fail("FAIL 2-1e16i float imaginary part", scaledImag);
      }
    },
  },
  {
    id: 14,
    weight: 1,
    run(ctx) {
      const inf = evaluate(compileExpression("inf", {}));
      if (inf.re !== Infinity || inf.im !== 0) {
        ctx.fail("FAIL inf", inf);
      }
    },
  },
  {
    id: 15,
    weight: 80,
    run(ctx) {
      const exact = exactReport(compileExpression("2-1e16*i", {}), {}, { maxNodes: 200_000 });
      if (!exactClose(exact.value, 2, "-1e16", 12)) {
        ctx.fail("FAIL exact 2-1e16i", formatExact(exact.value));
      }
    },
  },
  {
    id: 16,
    weight: 4,
    run(ctx) {
      const exact = exactReport(compileExpression("10000000000000001-10000000000000000", {}), {}, { maxNodes: 200_000 });
      if (!exactClose(exact.value, 1, 0, 20)) {
        ctx.fail("FAIL exact big integer sub", formatExact(exact.value));
      }
    },
  },
  {
    id: 17,
    weight: 1,
    run(ctx) {
      const exact = exactReport(compileExpression("(2^53+1)-2^53", {}), {}, { maxNodes: 200_000 });
      if (!exactClose(exact.value, 1, 0, 12)) {
        ctx.fail("FAIL exact 2^53", formatExact(exact.value));
      }
    },
  },
  {
    id: 18,
    weight: 1,
    run(ctx) {
      const exact = exactReport(compileExpression("(1e16+1)-1e16", {}), {}, { maxNodes: 200_000 });
      if (!exactClose(exact.value, 1, 0, 12)) {
        ctx.fail("FAIL exact 1e16+1-1e16", formatExact(exact.value));
      }
    },
  },
  {
    id: 19,
    weight: 16,
    run(ctx) {
      const exact = exactReport(compileExpression("(1+1e-20)-1", {}), {}, { maxNodes: 200_000 });
      if (!exactClose(exact.value, "1e-20", 0, 12)) {
        ctx.fail("FAIL exact (1+1e-20)-1", formatExact(exact.value));
      }
    },
  },
  {
    id: 20,
    weight: 48,
    run(ctx) {
      const node = compileExpression("1-((1e9+pi+1e-10)-1e9)*i", {});
      const exact = exactReport(node, {}, { maxNodes: 400_000 });
      if (exact.value.im.gt(0) || !exactClose(exact.value, 1, exact.value.im, 8)) {
        ctx.fail("FAIL exact near-pi sign", formatExact(exact.value));
      }
      if (!close(evaluate(node), c(1, -Math.PI), 1e-4)) {
        ctx.fail("FAIL float near-pi", evaluate(node));
      }
    },
  },
  {
    id: 21,
    weight: 2,
    run(ctx) {
      const exact = exactReport(compileExpression("(1e17+pi)-1e17", {}), {}, { maxNodes: 400_000 });
      if (!exactClose(exact.value, Math.PI, 0, 10)) {
        ctx.fail("FAIL exact (1e17+pi)-1e17", formatExact(exact.value));
      }
    },
  },
  {
    id: 22,
    weight: 28,
    run(ctx) {
      const variable = tSub(literalNode("1"), V("x"));
      const exact = exactReport(variable, { x: c(1e20) }, { maxNodes: 400_000 });
      if (exact.value.re.plus("99999999999999999999").abs().gt("1e-6")) {
        ctx.fail("FAIL variable 1-1e20", exact.value.re.toString());
      }
    },
  },
  {
    id: 23,
    weight: 2941,
    run(ctx) {
      const exact = exactReport(compileExpression("1e308+1e308", {}), {}, { maxNodes: 400_000 });
      if (!exactClose(exact.value, "2e308", 0, 12)) {
        ctx.fail("FAIL exact 1e308+1e308", formatExact(exact.value));
      }
      const avg = exactReport(compileExpression("avg(1e308,1e308)", {}), {}, { maxNodes: 400_000 });
      if (!exactClose(avg.value, "1e308", 0, 12)) {
        ctx.fail("FAIL exact avg 1e308", formatExact(avg.value));
      }
    },
  },
  {
    id: 24,
    weight: 1,
    run(ctx) {
      const asinh = evaluate(tArsinh(V("x")), { x: c(1000) });
      if (!close(asinh, c(Math.asinh(1000)), 1e-9)) {
        ctx.fail("FAIL variable asinh(1000)", asinh);
      }
    },
  },
  {
    id: 25,
    weight: 2,
    run(ctx) {
      let threw = false;
      try {
        literalNode("1e400000000");
      } catch (err) {
        threw = err instanceof EmlError && /exponent is too large/i.test(err.message);
      }
      if (!threw) {
        ctx.fail("FAIL 1e400 message");
      }
    },
  },
  {
    id: 26,
    weight: 228,
    run(ctx) {
      const twentyK = Array.from({ length: 20_000 }, () => "1").join("+");
      const summed = compileExpression(twentyK, {});
      const sum = evaluateReport(summed, {}, { maxNodes: 2_000_000 });
      if (!close(sum.value, c(20000), 1e-12) || sum.value.im !== 0) {
        ctx.fail("FAIL 20000 ones", sum.value, sum.singular, provenInteger(summed)?.toString(), summed.type);
      }
    },
  },
];

export default checks;
