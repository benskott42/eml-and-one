import { agreementNote, compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import { beyondFloatBound, exactEvaluate, exactParts, exactReport, exactToFloat, exactUnderflowsFloat, formatExact } from "../exact";
import type { CheckContext, CheckModule } from "./_types";
import { evaluate, evaluateReport, SINGULAR_LN0, SINGULAR_POLE } from "../node";
import type { Decimal } from "decimal.js";
import { c } from "../complex";
import { seriesShortcutNote, unaryNode } from "../library";
import { captionName, formatC } from "../format";
import { finiteLossMessage } from "../history";
import table from "../best-known.json";
import { runTsx, workerReport } from "./_helpers";

/**
 * Float accuracy bounds, 12-digit flagging, small-argument series accuracy, and fresh-realm wire unpack.
 */
// Equivalent spellings, series corrections, dust, and the 480-digit cap.
function closeTo(ctx: CheckContext, source: string, re: string, im = "0"): void {
  const report = workerReport(source);
  const wantRe = exactParts(re).re;
  const wantIm = exactParts(im).re;
  const badRe = wantRe.isZero() ? !report.value.re.isZero() : report.value.re.sub(wantRe).abs().div(wantRe.abs()).gt("1e-9");
  const badIm = wantIm.isZero() ? !report.value.im.isZero() : report.value.im.sub(wantIm).abs().div(wantIm.abs()).gt("1e-9");
  if (report.unverified || badRe || badIm) {
    ctx.fail("FAIL worker value", source, report.unverified ? "unverified" : formatExact(report.value));
  }
}
function unresolved(ctx: CheckContext, source: string): void {
  const report = workerReport(source);
  if (!report.unverified) {
    ctx.fail("FAIL certified", source, formatExact(report.value));
  }
}
// From p = 112 the negative imaginary part falls off 120 digits and the composed
// log would certify +π. The value is ln 2 − iπ, or the result stays unverified.
function lnBelow(ctx: CheckContext, source: string): void {
  const report = workerReport(source);
  if (report.unverified) return;
  const wantRe = exactParts("0.6931471805599453").re;
  const wantIm = exactParts(Math.PI).re.neg();
  const badRe = report.value.re.sub(wantRe).abs().div(wantRe.abs()).gt("1e-9");
  const badIm = report.value.im.isPos() || report.value.im.sub(wantIm).abs().div(wantIm.abs()).gt("1e-9");
  if (badRe || badIm) {
    ctx.fail("FAIL ln below the cut", source, formatExact(report.value));
  }
}
// Scaled tiny adds stay on the raw add word only while the lifted imaginary parts
// and their sum sit in (−π, π]. These are the cases that leave that strip.
function bothModes(ctx: CheckContext, source: string, re: string, im: string): void {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  const rebuilt = unpackCircuit(packed.tokens, packed.root);
  const exact = exactReport(rebuilt, {}, { maxNodes: 200_000 });
  const floated = evaluate(rebuilt, {}, { maxNodes: 200_000 });
  const wantRe = exactParts(re).re;
  const wantIm = exactParts(im).re;
  const off = (got: Decimal, want: Decimal, tol: string) => {
    if (want.isZero()) return got.abs().gt("1e-12");
    return got.sub(want).abs().div(want.abs()).gt(tol);
  };
  const floatRe = exactParts(floated.re).re;
  const floatIm = exactParts(floated.im).re;
  if (
    exact.unverified ||
    off(exact.value.re, wantRe, "1e-9") ||
    off(exact.value.im, wantIm, "1e-9") ||
    off(floatRe, wantRe, "1e-8") ||
    off(floatIm, wantIm, "1e-8")
  ) {
    ctx.fail("FAIL both modes", source, exact.unverified ? "unverified" : formatExact(exact.value), floated);
  }
}

const checks: CheckModule[] = [
  {
    id: 46,
    weight: 9618,
    run(ctx) {
      const bfRel = (got: { re: number; im: number }, want: { re: number; im: number }, tol: number) =>
        Number.isFinite(got.re) && Number.isFinite(got.im) && Math.hypot(got.re - want.re, got.im - want.im) <= tol * Math.max(Math.hypot(want.re, want.im), 1e-300);
      const asinCases: Array<[number, number, number, number]> = [
        [3, 4, 0.63398386563917672, 2.3055090312434769],
        [-3, 4, -0.63398386563917672, 2.3055090312434769],
        [3, -4, 0.63398386563917672, -2.3055090312434769],
        [-3, -4, -0.63398386563917672, -2.3055090312434769],
        [1, 800, 0.0012499983724006398, 7.3777600801002023],
        [0, 10, 0.0, 2.9982229502979697],
        [0, -10, 0.0, -2.9982229502979697],
        [0.5, 5, 0.097763379364927734, 2.3171322930349235],
        [2, 1e-18, 1.5707963267948966, 1.3169578969248167],
        [2, -1e-18, 1.5707963267948966, -1.3169578969248167],
        [-2, 1e-18, -1.5707963267948966, 1.3169578969248167],
        [-2, -1e-18, -1.5707963267948966, -1.3169578969248167],
        [2, 0, 1.5707963267948966, -1.3169578969248167],
        [-2, 0, -1.5707963267948966, 1.3169578969248167],
        [1.5, 0, 1.5707963267948966, -0.96242365011920689],
        [0.5, 0, 0.52359877559829887, 0.0],
        [1000000, 0, 1.5707963267948966, -14.508657738523969],
        [-1000000, 0, -1.5707963267948966, 14.508657738523969],
        [0, 1000000, 0.0, 14.508657738524469],
        [1000000000000, 0.5, 1.5707963267943966, 28.324168296488494],
        [1e-9, 0, 1.0000000000000001e-9, 0.0],
      ];
      for (const [re, im, wantRe, wantIm] of asinCases) {
        const want = c(wantRe, wantIm);
        const source = `arcsin((${re})+(${im})*i)`;
        const node = compileExpression(source, {});
        const got = evaluate(node, {}, { maxNodes: 2_000_000 });
        const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
        if (!bfRel(got, want, 1e-9) || !bfRel(exact, want, 1e-14)) {
          ctx.fail("FAIL arcsin literal", source, got, exact, want);
        }
      }
      // A variable has no proven range. Its value must still be right on both
      // sides of |Im x| = π; exact mode also keeps the side of a 10^(−18) offset.
      const variable = unaryNode("arcsin");
      const varCases: Array<[number, number, number, number, boolean]> = [
        [3, 4, 0.63398386563917672, 2.3055090312434769, true],
        [3, -4, 0.63398386563917672, -2.3055090312434769, true],
        [-3, 4, -0.63398386563917672, 2.3055090312434769, true],
        [1, 800, 0.0012499983724006398, 7.3777600801002023, true],
        [0, 10, 0.0, 2.9982229502979697, true],
        [0, -10, 0.0, -2.9982229502979697, true],
        [0.5, 5, 0.097763379364927734, 2.3171322930349235, true],
        [2, 0, 1.5707963267948966, -1.3169578969248167, true],
        [-2, 0, -1.5707963267948966, 1.3169578969248167, true],
        [1, 0, 1.5707963267948966, 0, true],
        [-1, 0, -1.5707963267948966, 0, true],
        [0.5, 0, 0.52359877559829887, 0.0, true],
        [0, 1000000, 0.0, 14.508657738524469, true],
        [-1000000, 0, -1.5707963267948966, 14.508657738523969, true],
        [0, -1000000, 0.0, -14.508657738524469, true],
        [2, 1e-18, 1.5707963267948966, 1.3169578969248167, false],
        [-2, -1e-18, -1.5707963267948966, -1.3169578969248167, false],
      ];
      for (const [re, im, wantRe, wantIm, floatToo] of varCases) {
        const want = c(wantRe, wantIm);
        const env = { x: c(re, im) };
        const got = evaluate(variable, env, { maxNodes: 2_000_000 });
        const exact = exactToFloat(exactEvaluate(variable, env, { maxNodes: 2_000_000 }));
        if ((floatToo && !bfRel(got, want, 1e-7)) || !bfRel(exact, want, 1e-14)) {
          ctx.fail("FAIL arcsin variable", re, im, got, exact, want);
        }
      }

      // arsinh and arccos follow arcsin's conventions (mpmath).
      const viaArcsin: Array<[string, number, number, number, number]> = [
        ["arsinh", 0, -1000000, -14.508657738523969, -1.5707963267948966],
        ["arsinh", 0, 1, 0.0, 1.5707963267948966],
        ["arsinh", 0, -1, 0.0, -1.5707963267948966],
        ["arsinh", 0, 2, 1.3169578969248167, 1.5707963267948966],
        ["arsinh", 0, -2, -1.3169578969248167, -1.5707963267948966],
        ["arsinh", 3, 4, 2.2999140408792696, 0.91761685335147866],
        ["arsinh", -3, -4, -2.2999140408792696, -0.91761685335147866],
        ["arsinh", -1000000, 0, -14.508657738524469, 0.0],
        ["arsinh", 1e-9, 0, 1.0000000000000001e-9, 0.0],
        ["arsinh", 1e-18, -2, 1.3169578969248167, -1.5707963267948966],
        ["arsinh", -1e-18, 2, -1.3169578969248167, 1.5707963267948966],
        ["arccos", -1, 0, 3.1415926535897932, 0.0],
        ["arccos", 1, 0, 0.0, 0.0],
        ["arccos", 2, 0, 0.0, 1.3169578969248167],
        ["arccos", -2, 0, 3.1415926535897932, -1.3169578969248167],
        ["arccos", 3, 4, 0.9368124611557199, -2.3055090312434769],
        ["arccos", 0, 10, 1.5707963267948966, -2.9982229502979697],
        ["arccos", 0.5, 0, 1.0471975511965977, 0.0],
        ["arccos", -2, -1e-18, 3.1415926535897932, 1.3169578969248167],
      ];
      for (const [fn, re, im, wantRe, wantIm] of viaArcsin) {
        const want = c(wantRe, wantIm);
        // ±i as typed. 0 + (−1)·i is another circuit; its float value is about 4·10^(−8) off.
        const source = re === 0 && (im === 1 || im === -1) ? `${fn}(${im < 0 ? "-" : ""}i)` : `${fn}((${re})+(${im})*i)`;
        const node = compileExpression(source, {});
        const got = evaluate(node, {}, { maxNodes: 2_000_000 });
        const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 2_000_000 }));
        const tolF = want.re === 0 && want.im === 0 ? 0 : 1e-9;
        const okF = tolF === 0 ? Math.hypot(got.re, got.im) <= 1e-15 : bfRel(got, want, tolF);
        const okX = tolF === 0 ? Math.hypot(exact.re, exact.im) <= 1e-30 : bfRel(exact, want, 1e-14);
        if (!okF || !okX) {
          ctx.fail("FAIL branch literal", source, got, exact, want);
        }
      }
      const asinhVar = unaryNode("arsinh");
      for (const [re, im, wantRe, wantIm] of [
        [0, 1, 0, 1.5707963267948966],
        [0, -1, 0, -1.5707963267948966],
        [0, 2, 1.3169578969248167, 1.5707963267948966],
        [0, -1000000, -14.508657738523969, -1.5707963267948966],
        [0, 1000000, 14.508657738523969, 1.5707963267948966],
        [1000000, 0, 14.508657738524469, 0],
      ] as Array<[number, number, number, number]>) {
        const env = { x: c(re, im) };
        const want = c(wantRe, wantIm);
        const got = evaluate(asinhVar, env, { maxNodes: 2_000_000 });
        const report = exactReport(asinhVar, env, { maxNodes: 2_000_000 });
        if (!bfRel(got, want, 1e-7) || report.singular || !bfRel(exactToFloat(report.value), want, 1e-14)) {
          ctx.fail("FAIL arsinh variable", re, im, got, report.singular, exactToFloat(report.value), want);
        }
      }

      // Exact mode printed every |value| ≤ 10^(−30) as 0 (exactInteger's absolute 1e-30 test).
      const exactText: Array<[string, string]> = [
        ["1e-30", "1×10^−30"],
        ["-1e-40", "−1×10^−40"],
        ["2e-80+1e-80", "3×10^−80"],
        ["1e-90*3", "3×10^−90"],
        ["1e-29", "1×10^−29"],
        ["2", "2"],
        ["6*7", "42"],
      ];
      for (const [source, want] of exactText) {
        const text = formatExact(exactEvaluate(compileExpression(source, {}), {}));
        if (text !== want) {
          ctx.fail("FAIL exact display", source, text, want);
        }
      }

      // Subtraction of two tiny operands lost the subtrahend (no lift before eml(ln a, exp b)).
      const tinySub: Array<[string, number, number]> = [
        ["1e-100-3e-100", -2e-100, 0],
        ["0-1e-90", -1e-90, 0],
        ["(1e-90*i)-(2e-90)", -2e-90, 1e-90],
        ["3e-20-1e-20", 2e-20, 0],
      ];
      for (const [source, wantRe, wantIm] of tinySub) {
        const node = compileExpression(source, {});
        const want = c(wantRe, wantIm);
        const got = evaluate(node, {});
        const exact = exactToFloat(exactEvaluate(node, {}));
        if (!bfRel(got, want, 1e-9) || !bfRel(exact, want, 1e-14)) {
          ctx.fail("FAIL tiny sub", source, got, exact, want);
        }
      }
    },
  },
  {
    id: 47,
    weight: 26113,
    run(ctx) {
      // The float flag compares each component at the 12 displayed digits.
      // The exact reference raises its precision when a subtraction cancels, so a
      // float 0 is not certified by an exact 0. The −6.7×10^(−106) real part is a
      // real component, not dust, and stays.
      const kept = exactEvaluate(compileExpression("(2e-40*i)-(-6.7e-106)", {}));
      const keptNeg = exactEvaluate(compileExpression("(2e-40*i)-(6.7e-106)", {}));
      if (
        kept.re.isZero() ||
        kept.re.sub("6.7e-106").abs().div("6.7e-106").gt("1e-9") ||
        keptNeg.re.isZero() ||
        keptNeg.re.plus("6.7e-106").abs().div("6.7e-106").gt("1e-9")
      ) {
        ctx.fail("FAIL tiny real part snapped", kept.re.toString(), keptNeg.re.toString());
      }
      const half = formatExact(exactEvaluate(compileExpression("0.5-1e-72", {})));
      if (half === "0.5" || !half.includes("999")) {
        ctx.fail("FAIL exact 0.5-1e-72 display", half);
      }
      const hugeDiv = evaluateReport(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 });
      if (hugeDiv.singular === SINGULAR_LN0) {
        ctx.fail("FAIL float overflow labelled ln 0", hugeDiv.singular, hugeDiv.value);
      }
      const hugeExact = formatExact(exactEvaluate(compileExpression("(10^400+1)/7", {}), {}, { maxNodes: 400_000 }));
      if (!hugeExact.includes("10^399") || hugeExact.includes("∞")) {
        ctx.fail("FAIL exact (10^400+1)/7", hugeExact);
      }
      for (const source of ["tan(pi/2)", "tan(3*pi/2)"]) {
        const floatPole = evaluateReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
        const exactPole = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
        if (floatPole.singular !== SINGULAR_POLE || exactPole.singular !== SINGULAR_POLE) {
          ctx.fail("FAIL pole", source, floatPole.singular, exactPole.singular, floatPole.value, formatExact(exactPole.value));
        }
      }
      const nearPole = exactEvaluate(compileExpression("tan(pi/2+1e-8)", {}), {}, { maxNodes: 400_000 });
      if (!nearPole.im.isZero() && nearPole.im.abs().gt("1e-40")) {
        ctx.fail("FAIL exact tan near pole imag", nearPole.re.toString(), nearPole.im.toString());
      }
      const atanh = exactToFloat(exactEvaluate(compileExpression("artanh(2)", {})));
      if (Math.abs(atanh.re - Math.log(3) / 2) > 1e-9 || Math.abs(atanh.im + Math.PI / 2) > 1e-9) {
        ctx.fail("FAIL artanh lower cut", atanh);
      }
      const flagged = (source: string) => {
        const node = compileExpression(source, {});
        const got = evaluateReport(node, {}, { maxNodes: 400_000 });
        const report = exactReport(node, {}, { maxNodes: 400_000 });
        return beyondFloatBound(got.value, exactToFloat(report.value)) || exactUnderflowsFloat(report.value);
      };
      for (const source of ["exp(1e-9*i)-1", "1e300+i", "tan(50000)", "exp(1e-6)-1", "cos(1e-200)-1"]) {
        if (!flagged(source)) {
              const node = compileExpression(source, {});
          const got = evaluate(node, {}, { maxNodes: 400_000 });
          const exact = exactToFloat(exactEvaluate(node, {}, { maxNodes: 400_000 }));
          ctx.fail("FAIL unflagged", source, got, exact, formatExact(exactEvaluate(node, {}, { maxNodes: 400_000 })));
        }
      }
      if (beyondFloatBound(c(1), c(1 + 1e-12)) !== false || beyondFloatBound(c(1), c(1 + 1e-11)) !== true) {
        ctx.fail("FAIL displayed-digit tolerance");
      }
      // The same path the screen uses: parse the typed expression, pack it for the
      // worker, and read the text the worker would post.
      const shown = (source: string) => {
        const node = compileExpression(source, {});
        const packed = packCircuit(node);
        const rebuilt = unpackCircuit(packed.tokens, packed.root);
        return formatExact(exactReport(rebuilt, {}, { maxNodes: 80_000 }).value);
      };
      for (const [source, want] of [
        ["sin(10^-200)", "1×10^−200"],
        ["sin(1e-200)", "1×10^−200"],
        ["tan(1e-200)", "1×10^−200"],
        ["tanh(1e-200)", "1×10^−200"],
        ["arctan(1e-200)", "1×10^−200"],
        ["tan(1e-400)", "1×10^−400"],
        ["ln(1+1e-130)", "1×10^−130"],
        ["exp(1e-150)-1", "1×10^−150"],
        ["sqrt(1+1e-200)-1", "5×10^−201"],
        ["tan(10^(-20))", "1×10^−20"],
        ["tan(10^(-100))", "1×10^−100"],
      ] as Array<[string, string]>) {
        const text = shown(source);
        const direct = formatExact(exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 }).value);
        if (text !== want || direct !== want) {
          ctx.fail("FAIL tiny trig text", source, text, direct, want);
        }
      }
      const tinyTan = compileExpression("tan(1e-200)", {});
      const tinyFloat = evaluateReport(tinyTan, {}, { maxNodes: 80_000 });
      const tinyExact = exactToFloat(exactReport(tinyTan, {}, { maxNodes: 80_000 }).value);
      if (beyondFloatBound(tinyFloat.value, tinyExact) || Math.abs(tinyExact.re - 1e-200) / 1e-200 > 1e-9) {
        ctx.fail("FAIL tan(1e-200) should agree on the leading term", tinyFloat.value, tinyExact);
      }
      const cosGap = (source: string, want: string) => {
        const text = shown(source);
        const rel = exactEvaluate(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        const off = rel.re.sub(want).abs().div(want.replace("-", ""));
        if (text.includes("i") || rel.re.isZero() || off.gt("1e-9")) {
          ctx.fail("FAIL cos minus one", source, text, rel.re.toString());
        }
      };
      cosGap("cos(1e-100)-1", "-5e-201");
      cosGap("cos(1e-200)-1", "-5e-401");
      for (const source of ["arsinh(1e-18)", "arsinh(-1e-18)", "arcsin(1e-18*i)", "arcsin(-1e-18*i)", "arcsin(1e-12*i)"]) {
        const node = compileExpression(source, {});
        const packed = packCircuit(node);
        const rebuilt = unpackCircuit(packed.tokens, packed.root);
        const exact = exactReport(rebuilt, {}, { maxNodes: 200_000 });
        const got = evaluateReport(node, {}, { maxNodes: 200_000 });
        if (beyondFloatBound(got.value, exactToFloat(exact.value))) {
          ctx.fail("FAIL spurious tiny component", source, got.value, formatExact(exact.value));
        }
      }
      const hugeSum = formatExact(exactEvaluate(compileExpression("1e308+2e308", {}), {}, { maxNodes: 80_000 }));
      if (!hugeSum.includes("3") || !hugeSum.includes("10^308")) {
        ctx.fail("FAIL exact 1e308+2e308", hugeSum);
      }
      const atanNeg = compileExpression("arctan(-2*i)", {});
      const atanFloat = evaluate(atanNeg, {}, { maxNodes: 200_000 });
      const atanExact = exactToFloat(exactEvaluate(atanNeg, {}, { maxNodes: 200_000 }));
      if (Math.abs(atanFloat.re - atanExact.re) > 1e-9 || Math.abs(atanFloat.im - atanExact.im) > 1e-9 || atanFloat.re > 0) {
        ctx.fail("FAIL arctan(-2i) cut", atanFloat, atanExact);
      }
      const farText = shown("tan(1e-5000)");
      if (farText !== "1×10^−5000") {
        ctx.fail("FAIL tan(1e-5000)", farText);
      }
      const beyond = exactReport(unpackCircuit(...(() => {
        const packed = packCircuit(compileExpression("cos(1e-300)-1", {}));
        return [packed.tokens, packed.root] as const;
      })()), {}, { maxNodes: 80_000 });
      if (!beyond.unverified && formatExact(beyond.value) === "0") {
        ctx.fail("FAIL cos(1e-300)-1 certified a zero", formatExact(beyond.value), beyond.unverified);
      }
      const poleNode = compileExpression("tan(pi/2)", {});
      const polePacked = packCircuit(poleNode);
      const poleRebuilt = unpackCircuit(polePacked.tokens, polePacked.root);
      const poleExact = exactReport(poleRebuilt, {}, { maxNodes: 80_000 });
      const poleFloat = evaluateReport(poleNode, {}, { maxNodes: 80_000 });
      if (poleExact.singular !== SINGULAR_POLE || poleFloat.singular !== SINGULAR_POLE) {
        ctx.fail("FAIL packed tan pole", poleExact.singular, poleFloat.singular, formatExact(poleExact.value));
      }
    },
  },
  {
    id: 48,
    weight: 13355,
    run(ctx) {
      for (const source of [
        "sin(2*10^(-200))",
        "sin(2*1e-200)",
        "sin(10^(-200)+10^(-200))",
        "sin(1e-200+1e-200)",
      ]) closeTo(ctx, source, "2e-200");
      for (const source of ["-1+exp(10^(-150))", "exp(10^(-150))-1", "-1+exp(1e-150)", "exp(1e-150)-1"]) closeTo(ctx, source, "1e-150");
      closeTo(ctx, "sin(1e-40)-1e-40", "-1.666666666667e-121");
      closeTo(ctx, "tan(1e-40)-1e-40", "3.333333333333e-121");
      closeTo(ctx, "tan(10^(-40))-10^(-40)", "3.333333333333e-121");
      closeTo(ctx, "tan(3*10^(-40))-3*10^(-40)", "9e-120");
      closeTo(ctx, "tan(1e-50)-1e-50", "3.333333333333e-151");
    },
  },
  {
    id: 67,
    weight: 27962,
    run(ctx) {
      closeTo(ctx, "tanh(1e-45)-1e-45", "-3.333333333333e-136");
      closeTo(ctx, "tanh(10^(-45))-10^(-45)", "-3.333333333333e-136");
      closeTo(ctx, "tanh(3*10^(-45))-3*10^(-45)", "-9e-135");
      closeTo(ctx, "arctan(1e-45)-1e-45", "-3.333333333333e-136");
      closeTo(ctx, "arctan(10^(-45))-10^(-45)", "-3.333333333333e-136");
      closeTo(ctx, "arctan(3*10^(-45))-3*10^(-45)", "-9e-135");
    },
  },
  {
    id: 68,
    weight: 7197,
    run(ctx) {
      closeTo(ctx, "cos(1e-50)-1", "-5e-101");
      closeTo(ctx, "cos(10^(-50))-1", "-5e-101");
      closeTo(ctx, "cos(3*10^(-50))-1", "-4.5e-100");
      closeTo(ctx, "cos(1e-50)-1+5e-101", "4.166666666667e-202");
      closeTo(ctx, "sin(1e-18+1e-120*i)", "1e-18", "1e-120");
      closeTo(ctx, "ln(1+10^(-130))", "1e-130");
      closeTo(ctx, "ln(1+1e-130)", "1e-130");
      closeTo(ctx, "ln(1+3*10^(-130))", "3e-130");
      closeTo(ctx, "log(1+10^(-130))", "1e-130");
      closeTo(ctx, "log(1+1e-130)", "1e-130");
      closeTo(ctx, "log(1+3*10^(-130))", "3e-130");
      closeTo(ctx, "log(1+10^(-200))", "1e-200");
      closeTo(ctx, "ln(1+10^(-300))", "1e-300");
      closeTo(ctx, "ln(1+3*10^(-300))", "3e-300");
      closeTo(ctx, "log(1+3*1e-300)", "3e-300");
    },
  },
  {
    id: 64,
    weight: 3205,
    run(ctx) {
      lnBelow(ctx, "ln(-2-10^(-110)*i)");
      lnBelow(ctx, "ln(-2-10^(-112)*i)");
      lnBelow(ctx, "ln(-2-10^(-115)*i)");
      lnBelow(ctx, "ln(-2-10^(-130)*i)");
      bothModes(ctx, "0.00005*i+0.00005*i", "0", "0.0001");
      bothModes(ctx, "0.00006103*i+0.00006103*i", "0", "0.00012206");
      bothModes(ctx, "sinh(0.00005*i)", "0", "0.00005");
      bothModes(ctx, "tanh(1e-10*i)", "0", "1e-10");
      bothModes(ctx, "tanh(1e-16*i)", "0", "1e-16");
      bothModes(ctx, "cosh(0.00005*i)", "0.99999999875", "0");
      bothModes(ctx, "3.1*i+0.04", "0.04", "3.1");
      bothModes(ctx, "4*i+0.5*i", "0", "4.5");
      bothModes(ctx, "-4*i+1", "1", "-4");
      bothModes(ctx, "0.00005*i+4*i", "0", "4.00005");
      bothModes(ctx, "6*i+(-6*i)", "0", "0");
      bothModes(ctx, "(2+3*i)+(-1+0.2*i)", "1", "3.2");
      bothModes(ctx, "(3.141592653589793*i)+(-0.0001*i)", "0", "3.141492653589793");
    },
  },
  {
    id: 65,
    weight: 4812,
    run(ctx) {
      closeTo(ctx, "(exp(1e-50)-1)-1e-50", "5e-101");
      closeTo(ctx, "ln(1+1e-50)-1e-50", "-5e-101");
      closeTo(ctx, "(sqrt(1+1e-50)-1)-5e-51", "-1.25e-101");
      closeTo(ctx, "1e-120*(2+i)", "2e-120", "1e-120");
      closeTo(ctx, "3*((1e-120*i)-(2e-120))", "-6e-120", "3e-120");
      closeTo(ctx, "2*(1e-18+1e-125*i)", "2e-18", "2e-125");
      closeTo(ctx, "exp(1e-432)-1", "1e-432");
      closeTo(ctx, "tan(1e-5000)", "1e-5000");
      closeTo(ctx, "exp(1e-1000)-1", "1e-1000");
      for (const source of ["exp(1e-433)-1", "tan(10^(-5000))", "exp(10^(-1000))-1", "sin(1e-300)-1e-300"]) unresolved(ctx, source);
      const shortcut = seriesShortcutNote(compileExpression("sin(1e-200)", {}));
      if (!shortcut || !shortcut.includes("series shortcut")) {
        ctx.fail("FAIL series note", shortcut);
      }
      if (seriesShortcutNote(compileExpression("sin(1)", {})) !== null) {
        ctx.fail("FAIL series note on sin(1)");
      }
      const under = agreementNote("ln(1+1e-130)", { re: 1e-130, im: 0 }, {}, "1×10^−130");
      if (under !== "float underflows") {
        ctx.fail("FAIL float underflows note", under);
      }
      const atanValue = evaluate(compileExpression("arctan(-2*i)", {}), {}, { maxNodes: 200_000 });
      const atanNote = agreementNote("arctan(-2*i)", atanValue, {}, formatC(atanValue));
      if (atanNote !== "matches the usual value" || !(atanValue.re < 0)) {
        ctx.fail("FAIL arctan usual value", atanNote, atanValue);
      }
      if (captionName("1×10^−5000", { re: 0, im: 0 }, "tan(1e-5000)") !== null) {
        ctx.fail("FAIL caption zero beside a tiny exact text");
      }
      if (captionName("0", { re: 0, im: 0 }, "1-1") !== "0") {
        ctx.fail("FAIL caption of a real zero");
      }
      const blocked = finiteLossMessage({ usable: false, notice: "couldn't verify", singular: null, mode: "float", text: "—" });
      const finite = finiteLossMessage({ usable: false, notice: null, singular: null, mode: "float", text: "—" });
      if (blocked !== null || finite !== "That left the finite numbers.") {
        ctx.fail("FAIL double limit message", blocked, finite);
      }
      const byKey = new Map(table.minimality.map((row) => [`${row.value}@${row.k}`, row]));
      const zero = byKey.get("0@7");
      const neg15 = byKey.get("−1@15");
      const neg17 = byKey.get("−1@17");
      const two = byKey.get("2@19");
      // Proved by tools/minimality/decide.py --open (all 6918 programs with K <= 19 excluded).
      const ipi = byKey.get("+iπ on this cut (−iπ on the principal log)@21");
      if (
        ipi?.label !== "proven minimal" ||
        !ipi.note.includes("6918") ||
        zero?.label !== "proven minimal" ||
        !zero.note.includes("K ≤ 5") ||
        neg15?.label !== "proven minimal (uses ln 0)" ||
        neg17?.label !== "proven minimal without ln 0" ||
        two?.label !== "proven minimal" ||
        !two.note.includes("2056") ||
        byKey.get("+iπ on this cut (−iπ on the principal log)@23")?.label !== "proven minimal without ln 0" ||
        byKey.get("−2@25")?.label !== "proven minimal (uses ln 0)" ||
        !byKey.get("−2@25")?.note.includes("82500") ||
        byKey.get("−2@27")?.label !== "shortest known"
      ) {
        ctx.fail("FAIL minimality labels", zero, neg15, neg17, two);
      }
    },
  },
  {
    id: 49,
    weight: 2424,
    run(ctx) {
      // A same-process unpack reuses the nodes that still hold the float range.
      // The screen's worker is a fresh realm, so the tiny known value has to cross the wire.
      const sources = [
        "ln(1+10^(-130))",
        "log(1+10^(-130))",
        "log(1+10^(-200))",
        "ln(1+10^(-300))",
        "ln(1+3*10^(-300))",
      ];
      const jobs = sources.map((source) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root };
      });
      const fresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(jobs));
      if (fresh.status !== 0) {
        ctx.fail("FAIL fresh exact process", fresh.status, fresh.stderr);
      } else {
        const rows = JSON.parse(fresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>;
        const want: Record<string, string> = {
          "ln(1+10^(-130))": "1×10^−130",
          "log(1+10^(-130))": "1×10^−130",
          "log(1+10^(-200))": "1×10^−200",
          "ln(1+10^(-300))": "1×10^−300",
          "ln(1+3*10^(-300))": "3×10^−300",
        };
        for (const row of rows) {
          if (row.unverified || row.text !== want[row.source]) {
            ctx.fail("FAIL fresh ln", row.source, row.unverified ? "unverified" : row.text);
          }
        }
      }
    },
  },
];

export default checks;
