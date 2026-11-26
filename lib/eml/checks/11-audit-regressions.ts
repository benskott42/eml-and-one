import type { CheckModule } from "./_types";
import { formatC } from "../format";
import { EmlError, evaluate, isolateCircuit } from "../node";
import { agreementNote, compileExpression, referenceExpression } from "../parse";
import { beyondFloatBound, exactReport, formatExact } from "../exact";
import { packCircuit, unpackCircuit } from "../wire";
import { runTsx, workerReport } from "./_helpers";
import { decadeOf } from "../lowering";
import { literalNode, seriesShortcutNote } from "../library";
import { c, cdiv, cpow } from "../complex";

/**
 * Audit regressions: pi lexing, build-time float underflow, odd functions at +/-0, enclosures, pole directions, exact display, and v1.0.3/1.0.4 bugs.
 */
const checks: CheckModule[] = [
  {
    id: 81,
    weight: 60,
    run(ctx) {
      // π is its own token. πi read as the name "pii", so exp(πi) and iπ could not be
      // typed. .5e3 and 1.e5 were "Cannot read the number", though .5 and 5. read.
      const same: [string, string][] = [
        ["πi", "pi*i"], ["exp(πi)", "exp(pi*i)"], ["π i", "pi*i"], ["2*πi", "2*pi*i"],
        [".5e3", "500"], [".5e-3", "0.0005"], ["1.e5", "100000"], ["-.25E+2", "-25"],
      ];
      for (const [source, spelled] of same) {
        let got = "error";
        try {
          got = formatC(evaluate(compileExpression(source, {})));
        } catch (err) {
          got = err instanceof Error ? err.message : String(err);
        }
        const want = formatC(evaluate(compileExpression(spelled, {})));
        if (got !== want) {
          ctx.fail("FAIL parser spelling", source, got, "want", want);
        }
      }
      const messages: [string, string][] = [
        ["2πi", "Put * between “2” and “pi”."],
        ["iπ", "Put * between “i” and “pi”."],
        ["ππ", "Put * between “pi” and “pi”."],
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
        }
      }
      // Nesting past the JavaScript stack is an expression error, not the engine's RangeError.
      for (const source of ["exp(".repeat(20000) + "0" + ")".repeat(20000), "-".repeat(50000) + "1"]) {
        let got = "compiled";
        try {
          compileExpression(source, {});
        } catch (err) {
          got = err instanceof EmlError ? err.message : `${(err as Error).name}: ${(err as Error).message}`;
        }
        if (got !== "The expression is nested too deeply." && got !== "This circuit is too large to evaluate.") {
          ctx.fail("FAIL deep nesting", source.slice(0, 8), got);
        }
      }
      // The pole note reads tan(π/2) as it reads tan(pi/2).
      const pole = evaluate(compileExpression("tan(π/2)", {}));
      const poleNote = agreementNote("tan(π/2)", pole, {}, formatC(pole));
      if (!poleNote?.startsWith("near a pole")) {
        ctx.fail("FAIL tan(π/2) agreement note", poleNote);
      }
    },
  },
  {
    id: 82,
    weight: 8000,
    run(ctx) {
      // A build-time known value is a float. A product or quotient that underflowed, two
      // tags that cancel in float (π against 3.141592653589793e0), and a decimal or power
      // that rounds to an integer were the exact 0 or that integer, and the folds for x·0,
      // 0/x and x^0 used them: (10^(−170))²·10^300 was a certified 0 (it is 10^(−40)),
      // (3.141592653589793e0 − π)·10^20 was 0, and 1.0000000000000001e0 − 1 was 0.
      // 0^(−0) is 1, as 0^0 is.
      const rows: [string, string][] = [
        ["(3.141592653589793e0-pi)*1e20", "−23846.26433832795"],
        ["5*(3.141592653589793e0-pi)", "−1.192313216916×10^−15"],
        ["(ln(2)-0.6931471805599453e0)*1e20", "941.723212145818"],
        ["(sqrt(2)-1.4142135623730951e0)*1e20", "−5119.83112757903"],
        ["1.0000000000000001e0-1", "1×10^−16"],
        ["3.0000000000000001e0*2-6", "2×10^−16"],
        ["8^(3.3333333333333333e-1)-2", "−1.38629436112×10^−17"],
        ["sqrt(4.0000000000000001e0)-2", "2.5×10^−17"],
        ["0^(1.0000000000000001e0-1)", "0"],
        ["2e3-2000", "0"],
        ["sqrt(4)-2", "0"],
        ["(1e-300/1e100)*1e300", "1×10^−100"],
        ["sqr(1e-200)*5", "5×10^−400"],
        ["sqr(1e-200)*(-3)", "−3×10^−400"],
        ["sqr(1e-200)/5", "2×10^−401"],
        ["(1e-300/1e100)/5", "2×10^−401"],
        ["0^(1e-200*1e-200)", "0"],
        ["0^(1e-300/1e100)", "0"],
        ["2^(1e-200*1e-200)-1", "6.931471805599×10^−401"],
        ["0^-0", "1"],
        ["0^(0*-1)", "1"],
      ];
      for (const [source, want] of rows) {
        const report = workerReport(source);
        const got = report.unverified ? "unverified" : formatExact(report.value);
        if (got !== want) {
          ctx.fail("FAIL build-time known value", source, got, "want", want);
        }
      }
      // Refused is honest; a certified 0 is not.
      for (const source of ["sqr(1e-170)*1e300", "sqr(1e-200)*1e300", "sqr(1e-170)*1e200*1e200"]) {
        const report = workerReport(source);
        if (!report.unverified && report.value.re.isZero()) {
          ctx.fail("FAIL underflowed product certified 0", source, formatExact(report.value));
        }
      }
    },
  },
  {
    id: 83,
    weight: 500,
    run(ctx) {
      // a − (a + 0) is +0. A 16-digit literal ending in 0 is (its prefix)·10 + 0, so
      // 1234567890123456*10 − 12345678901234560 folded to −(0) = −0, and ln of it was
      // a certified −∞ + iπ where ln(2*10 − 20) is −∞.
      const rows: [string, string][] = [
        ["1234567890123456*10-12345678901234560", "0"],
        ["ln(1234567890123456*10-12345678901234560)", "−∞"],
        ["1/(1234567890123456*10-12345678901234560)", "∞"],
        ["12345678901234567890*10-123456789012345678900", "0"],
        ["123456789012345678900-12345678901234567890*10", "0"],
        ["12345678901234567891-12345678901234567890", "1"],
      ];
      for (const [source, want] of rows) {
        const report = workerReport(source);
        const got = report.unverified ? "unverified" : formatExact(report.value);
        const floated = formatC(evaluate(compileExpression(source, {})));
        if (got !== want || floated !== want) {
          ctx.fail("FAIL sum complement zero", source, got, floated, "want", want);
        }
      }
    },
  },
  {
    id: 84,
    weight: 1500,
    run(ctx) {
      // An odd function at an exact 0 is 0, and at −0 it is −0. tan(0), sinh(0), arctan(0)
      // and artanh(0) were "couldn't verify", and arcsin(−0) was undefined in float.
      // sinh(−0) marked the shared −0 leaf as a series shortcut, so a later "-0" in the
      // same process (the exact worker is reused) was refused too.
      const rows: [string, string][] = [];
      for (const name of ["sin", "tan", "sinh", "tanh", "arcsin", "arctan", "arsinh", "artanh"]) {
        rows.push([`${name}(0)`, "0"], [`${name}(-0)`, "−0"], [`${name}(2-2)`, "0"]);
      }
      rows.push(["-0", "−0"], ["sqrt(-0)", "−0"]);
      for (const [source, want] of rows) {
        const report = workerReport(source);
        const got = report.unverified ? "unverified" : formatExact(report.value);
        const floated = formatC(evaluate(compileExpression(source, {})));
        if (got !== want || floated !== want) {
          ctx.fail("FAIL odd function at zero", source, got, floated, "want", want);
        }
      }
    },
  },
  {
    id: 85,
    weight: 30000,
    run(ctx) {
      // Well-conditioned results the size rules refused. ln(10^400) passes through 10^400
      // and loses nothing; an enclosure (exact-ball.ts) now confirms such a result where
      // the rule "far below a value past float range" refused it. (−10^200)^3 is a
      // compiler-proven integer. Decimal literals are exact, so a sum of them that comes
      // to 0 is the integer 0. Each row is read directly, through the wire in this
      // process, and in a fresh process that receives only the packed circuit.
      const certified: [string, string][] = [
        ["ln(1e400)", "921.034037197618"],
        ["ln(1e-400)", "−921.034037197618"],
        ["sqrt(4e-400)", "2×10^−200"],
        ["hypot(-1e-200,3e-200)", "3.162277660168×10^−200"],
        ["(-1e200)^3", "−1×10^600"],
        ["0.1+0.2-0.3", "0"],
        ["(0.1+0.2)-0.3", "0"],
        ["0.3-(0.1+0.2)", "0"],
        ["-0.3+0.1+0.2", "0"],
        ["0.5+0.25-0.75", "0"],
        ["0.7-0.5-0.2", "0"],
        ["1e-5+2e-5-3e-5", "0"],
        ["0.1+0.2-0.3+1e-50", "1×10^−50"],
        ["(0.1+0.2-0.3)*7", "0"],
        ["0-10^(-500)", "−1×10^−500"],
        ["10^400/7", "1.428571428571×10^399"],
        ["(exp(exp(-300))-1)+i/2", "5.148200222412×10^−131 + 0.5i"],
        ["hypot(2e-160,1)", "1"],
        ["(1+1e-200)^1e200", "2.718281828459"],
        ["(atan(1e-7)-1e-7)+1e-100", "−3.333333333333×10^−22"],
        ["hypot(1e160,-1)", "1×10^160"],
      ];
      // Still refused: a term absorbed into a huge value and cancelled with it, a part
      // past the cap, a collapsed logarithm, and a series zero.
      const refused = [
        "((1+10^(-500))-1)+i/2",
        "(exp(1200)+1)-exp(1200)",
        "exp(800)*0",
        "ln(1-10^(-500))",
        "ln(1+exp(-1000))",
        "ln(1-exp(-1000))",
        "pi+sqrt(exp(800))-sqrt(exp(800))-pi",
        "(1+1e-450)^1e450",
        "sinh(1e-7)-1e-7",
      ];
      const read = (report: ReturnType<typeof exactReport>) => (report.unverified ? "unverified" : formatExact(report.value).replace(/\u200b/g, ""));
      for (const [source, want] of certified) {
        const got = [read(exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 })), read(workerReport(source))];
        if (got.some((text) => text !== want)) {
          ctx.fail("FAIL newly certified", source, got, "want", want);
        }
      }
      for (const source of refused) {
        const got = [read(exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 })), read(workerReport(source))];
        if (got.some((text) => text !== "unverified")) {
          ctx.fail("FAIL still refused", source, got);
        }
      }
      const jobs = [...certified.map(([source]) => source), ...refused].map((source) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root };
      });
      const fresh = runTsx("scripts/fresh-exact.ts", JSON.stringify(jobs), 300_000);
      if (fresh.status !== 0) {
        ctx.fail("FAIL fresh newly certified", fresh.status, fresh.stderr?.slice(0, 400));
      } else {
        const want = new Map<string, string>([...certified, ...refused.map((source): [string, string] => [source, "unverified"])]);
        for (const row of JSON.parse(fresh.stdout) as Array<{ source: string; text: string; unverified: boolean }>) {
          const text = row.unverified ? "unverified" : row.text.replace(/\u200b/g, "");
          if (text !== want.get(row.source)) {
            ctx.fail("FAIL fresh newly certified", row.source, text, "want", want.get(row.source));
          }
        }
      }
    },
  },
  {
    id: 95,
    weight: 400,
    run(ctx) {
      // A pole's infinity keeps its direction. arctan(±i) is ±∞i and artanh(±1) is ±∞, so
      // exp of their turns has no limit. 1 + exp(−arctan(i)) was a certified 1. An infinity
      // off the axes (ln(ln(0)) = ∞ + iπ) turned by i is refused, and so is any result read
      // off it. A float overflow such as exp(800) is finite in exact mode and stays certified.
      const show = (source: string): string => {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        return report.unverified ? "unverified" : formatExact(report.value);
      };
      const rows: [string, string][] = [
        ["arctan(i)", "∞i"],
        ["arctan(-i)", "−∞i"],
        ["artanh(1)*i", "∞i"],
        ["1+exp(-arctan(i))", "undefined"],
        ["1+exp(-exp(arctan(i)))", "undefined"],
        ["sigma(arctan(i))", "undefined"],
        ["sigma(arctan(-i))", "undefined"],
        ["sigma(artanh(1)*i)", "undefined"],
        ["sigma(ln(ln(0))*i)", "unverified"],
        ["1+exp(-(ln(ln(0))*i))", "unverified"],
        ["acos(2/2)", "0"],
        ["acos(-(2/2))", "3.14159265359"],
        ["exp(800)*i", "2.726374572113×10^347i"],
        ["i*ln(0)", "−∞i"],
      ];
      for (const [source, want] of rows) {
        const got = show(source);
        if (got !== want) {
          ctx.fail("FAIL pole direction", source, got, "want", want);
        }
      }
    },
  },
  {
    id: 90,
    weight: 100,
    run(ctx) {
      // Exact display. Below 10^(−6) fixed notation has twelve places, so 1e−7·e printed as
      // 0.000000271828 with six digits where float shows seven. Scientific keeps twelve.
      // A value whose 12th to 14th places are 0 by chance (sigma(1) = 0.73105857863|000488)
      // is not a hidden tail: it prints as twelve places. A value that sits within 10^(−14) of
      // a round one, and is not it, still shows the digits that twelve places hide.
      const show = (source: string): string => {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        return report.unverified ? "unverified" : formatExact(report.value);
      };
      const rows: [string, string][] = [
        ["sigma(1)", "0.73105857863"],
        ["cosh(0.00005i)", "0.99999999875000000026"],
        ["1e-7*e", "2.718281828459×10^−7"],
        ["5e-7+1e-9", "5.01×10^−7"],
        ["0.000012345678901", "0.000012345679"],
        ["0.019930868458", "0.019930868458"],
        ["0.5-1e-16", "0.4999999999999999"],
        ["1+1e-13", "1.0000000000001"],
        ["acos(1+10^-16)", "1.414213562373×10^−8i"],
      ];
      for (const [source, want] of rows) {
        const got = show(source);
        if (got !== want) {
          ctx.fail("FAIL exact display", source, got, "want", want);
        }
      }
      const tail = show("0.5-1e-72");
      if (!tail.startsWith("0.49999999999999999999999999")) {
        ctx.fail("FAIL exact display hidden tail", tail);
      }
    },
  },
  {
    id: 91,
    weight: 300,
    run(ctx) {
      // sin, cos and tan at a recorded multiple of π where the value is 0, ±1/2 or ±1, exp of
      // i·kπ/2, and i^n. Their gates leave a residue near 10^(−16) that exact mode refuses, so
      // sin(π), cos(π/2), exp(iπ) + 1 and i^2 + 1 said "couldn't verify". The angle must be the
      // recorded multiple: a float near π, or π plus a tiny term, keeps its circuit.
      const rows: [string, string][] = [
        ["sin(pi)", "0"],
        ["sin(2*pi)", "0"],
        ["sin(100*pi)", "0"],
        ["cos(pi/2)", "0"],
        ["cos(pi)+1", "0"],
        ["cos(-5*pi)", "−1"],
        ["sin(pi/6)-1/2", "0"],
        ["cos(pi/3)", "0.5"],
        ["cos(7*pi/3)", "0.5"],
        ["sin(-pi/2)", "−1"],
        ["tan(pi)", "0"],
        ["tan(pi/4)", "1"],
        ["tan(3*pi/4)", "−1"],
        ["tan(pi/2)", "undefined"],
        ["exp(i*pi)+1", "0"],
        ["exp(2*pi*i)", "1"],
        ["exp(i*pi/2)", "i"],
        ["exp(i*pi*3/2)", "−i"],
        ["exp(-(i*pi))", "−1"],
        ["i^2+1", "0"],
        ["i^3", "−i"],
        ["i^-1", "−i"],
        ["sin(pi/3)", "0.866025403784"],
        ["exp(i*pi/3)", "0.5 + 0.866025403784i"],
        ["exp(pi*i*i)", "0.043213918264"],
        ["sin(pi+1e-30)", "−1×10^−30"],
        ["sin(3.141592653589793)", "2.384626433833×10^−16"],
        ["sin(pi)/sin(pi)", "undefined"],
      ];
      for (const [source, want] of rows) {
        const node = compileExpression(source, {});
        const report = exactReport(node, {}, { maxNodes: 80_000 });
        const got = report.unverified ? "unverified" : formatExact(report.value);
        if (got !== want) {
          ctx.fail("FAIL pi multiple", source, got, "want", want);
        }
      }
      for (const source of ["sin(pi)", "cos(pi/2)", "exp(i*pi)+1", "i^2+1"]) {
        const floated = formatC(evaluate(compileExpression(source, {})));
        if (floated !== "0") {
          ctx.fail("FAIL pi multiple float", source, floated);
        }
      }
    },
  },
  {
    id: 96,
    weight: 15000,
    run(ctx) {
      // Audit regressions: absorbed real terms & serial cancellations (the 6 v1.0.3 fuzz bugs),
      // unbounded series/asymptotic shortcuts, exactUnsure propagation, wire series-shortcut notes,
      // parser/complex/float-bound edge cases, and directed-rounding ball soundness.
      const show = (source: string): string => {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        return report.unverified ? "unverified" : formatExact(report.value).replace(/\u200b/g, "");
      };
      const auditRows: [string, string][] = [
        ["1e-400 + exp(-800)", "3.667874584178×10^−348"],
        ["(1e200 + 0.5) - (1e200 - 0.5)", "1"],
        ["((exp(-300) + 0.1/10^-130) - 0.1/10^-130) - exp(-300)", "unverified"],
        ["sqrt(sqrt(1e-40 + exp(-800)) - 1e-20)", "1.354229408959×10^−164"],
        ["hypot((1e-5)^2, -1e-200) - (1e-5)^2", "unverified"],
        ["ln((1e-20 + 0.5^i) - 0.5^i - 1e-20)", "unverified"],
        ["(sinh(5e-7) - 5e-7) + 1e-19", "unverified"],
        ["(artanh(5e-7) - 5e-7) + 1e-19", "unverified"],
        ["(arcsin(1e-5) - 1e-5 - (1e-15)/6) * 1e25", "0.075000000004"],
        ["tanh(1000) - tanh(1000)", "unverified"],
        ["(1 + tanh(1000)) - (1 + tanh(1000))", "unverified"],
      ];
      for (const [source, want] of auditRows) {
        const got = show(source);
        if (got !== want) {
          ctx.fail("FAIL audit row", source, got, "want", want);
        }
      }
      const asym = show("(arcsin(1e11) + i*ln(2e11)) * 1e23");
      if (!asym.startsWith("1.570796326795×10^23 + 2.5")) {
        ctx.fail("FAIL arcsin asymptotic", asym);
      }
      if (decadeOf(literalNode("1.0000001e-240")) !== -240) {
        ctx.fail("FAIL literalNode decade", decadeOf(literalNode("1.0000001e-240")));
      }
      // Parser: 2exp(1) asks for *, and referenceExpression reads inf.
      try {
        compileExpression("2exp(1)", {});
        ctx.fail("FAIL 2exp(1) compiled");
      } catch (err) {
        const msg = err instanceof EmlError ? err.message : String(err);
        if (msg !== "Put * between “2” and “exp”.") {
          ctx.fail("FAIL 2exp(1) message", msg);
        }
      }
      const refInf = referenceExpression("inf", {});
      if (!refInf || refInf.re !== Infinity || refInf.im !== 0) {
        ctx.fail("FAIL referenceExpression inf", refInf);
      }
      // Complex: infinite base to 0 is NaN (not 1), and i / (-0) is -Infinity*i.
      const infPow0 = cpow(c(-Infinity), c(0));
      if (!Number.isNaN(infPow0.re) || !Number.isNaN(infPow0.im)) {
        ctx.fail("FAIL cpow(-Inf, 0)", infPow0);
      }
      if (agreementNote("ln(0)^0", c(NaN, NaN), {}, "undefined") !== null) {
        ctx.fail("FAIL agreementNote ln(0)^0", agreementNote("ln(0)^0", c(NaN, NaN), {}, "undefined"));
      }
      const divNeg0 = cdiv(c(0, 1), c(-0, 0));
      if (divNeg0.re !== 0 || divNeg0.im !== -Infinity) {
        ctx.fail("FAIL cdiv(i, -0)", divNeg0);
      }
      // Long-integer boundary right below 1e12 that formatReal rounds up to 1000000000000.
      if (!beyondFloatBound(c(999999999999.9), c(999999999999))) {
        ctx.fail("FAIL beyondFloatBound 999999999999.9 vs 999999999999");
      }
      // Wire serialization preserves seriesShortcutNote across fresh unpack (isolateCircuit clears cons).
      const seriesSrc = compileExpression("tan(1e-5000)", {});
      const packedSeries = packCircuit(seriesSrc);
      const unpackedSeries = isolateCircuit(() => unpackCircuit(packedSeries.tokens, packedSeries.root));
      if (seriesShortcutNote(unpackedSeries) !== seriesShortcutNote(seriesSrc)) {
        ctx.fail("FAIL wire seriesShortcutNote", seriesShortcutNote(unpackedSeries), "want", seriesShortcutNote(seriesSrc));
      }
    },
  },
  {
    id: 98,
    weight: 2000,
    run(ctx) {
      // A refused operand whose float-known value is 0 is not the additive identity: adding to it
      // must not certify the other addend as the whole sum.
      const show98 = (source: string): string => {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        return report.unverified ? "unverified" : formatExact(report.value).replace(/​/g, "");
      };
      const rows98: [string, string][] = [
        ["(((0.2 + exp(300)) + exp(800)) + 1e310) + exp(300)", "unverified"],
        ["(((0.2 + exp(300)) + exp(800)) + 1e310) + exp(301)", "unverified"],
        ["exp(300) + (((0.2 + exp(300)) + exp(800)) + 1e310)", "unverified"],
        ["((((1e500 - 0.2) + 0.2) + exp(300)) + 0.2)", "unverified"],
        ["(1e200 - (((((-1e400) - 1e-310) + 2) + 1e400) + 1e310))", "unverified"],
        ["(exp(800) + 1e310) + 2", "2.726374572113×10^347"],
        ["0.1 + 0.2 - 0.3", "0"],
      ];
      for (const [source, want] of rows98) {
        const got = show98(source);
        if (got !== want) {
          ctx.fail("FAIL refused addend identity", source, got, "want", want);
        }
      }
    },
  },
  {
    id: 97,
    weight: 6000,
    run(ctx) {
      // Second-order terms of exp and cos rounded into 1: a cancellation that exposes x^2/2 below the
      // working precision must raise precision, or refuse past the cap, not certify 0 or dust.
      const show97 = (source: string): string => {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 80_000 });
        return report.unverified ? "unverified" : formatExact(report.value).replace(/​/g, "");
      };
      const rows97: [string, string][] = [
        ["exp(-1e-200) - 1 + 1e-200", "5×10^−401"],
        ["exp(1e-100) - 1 - 1e-100", "5×10^−201"],
        ["cos(1e-100*i) - 1", "5×10^−201"],
        ["ln(cos(1e-100*i))", "5×10^−201"],
        ["exp(-1e-240) - 1 + 1e-240", "unverified"],
        ["exp(5e-243) - 1 - 5e-243", "unverified"],
        ["ln(cos(1e-242*i))", "unverified"],
        ["cos(1e-240*i) - 1", "unverified"],
        ["sqrt(1 + 1e-130) - 1 - 0.5e-130", "−1.25×10^−261"],
      ];
      for (const [source, want] of rows97) {
        const got = show97(source);
        if (got !== want) {
          ctx.fail("FAIL second-order absorption", source, got, "want", want);
        }
      }
    },
  },
];

export default checks;
