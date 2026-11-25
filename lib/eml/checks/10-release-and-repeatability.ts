import type { CheckContext, CheckModule } from "./_types";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import { exactReport, formatExact } from "../exact";
import { runTsx } from "./_helpers";
import { circuitStats, E, EmlError, evaluateReport, isolateCircuit, type Node, nodeFromRpn, ONE, rpnTokens, SINGULAR_PRECISION, V } from "../node";
import { c, close } from "../complex";
import { pressPreviewForNode } from "../presses";
import { keyCostEntries, keyCosts } from "../../../components/keyTables";
import { programNumberText } from "../programIndex";
import { formatC } from "../format";
import { compileSubmission } from "../../../components/submitTurn";

/**
 * Release refusal/kept tables, cold-vs-warm repeatability, scaled-add notes, key captions, and submit turns.
 */
// Release refusals: a large trig argument below the root, a part cancelled to 0
// beside a nonzero part after a value below the precision, a finite overflow
// operand, inf·0, and the tiny sinh/artanh shortcut are refused, not certified.
const releaseRefused = ["-cos(1e119)", "cos(1e119)+1", "cos(1e125)*cos(1e130)", "tan(1e140)+1", "((1+exp(-299.3))-1)+i/2", "((1+exp(-300))-1)*i+1/2", "((1+10^-500)-1)+i/2", "i*((1+10^-500)-1)+1/2", "(10^400+i)*2", "2*(10^400+pi)", "(10^400+i)/7", "exp(((1+10^-500)-1)*i)", "(exp(800)+1)-exp(800)", "exp(800)*0", "sinh(1e-7)-1e-7", "artanh(1e-7)-1e-7", "cos(10^119)+1", "cos(2^400)+1", "sin(1e22)+1", "arcsin(1e-300)-1e-300", "tanh(130)", "tanh(200)", "tanh(354)", "sinh(5e-7)-5e-7", "sinh(1e-7*i)-1e-7*i", "(10^400-(2-2*i))^-1", "(1+(10^400+pi))-2", "(1+(10^400+pi))*2", "((cos(10^-50))+((10^400)+(pi)))-(((e)^0.5)+(((1+10^-200))+((-1+1*i))))", "tanh(10^300)", "tanh(10^20)", "tanh(-10^300)", "tanh(exp(800))", "asin((-1)/(10^-200))", "asinh(1/10^-200)", "acosh(asinh(10^400))", "exp(-10^20)", "(cosh(10^50))^(-2)", "1/cosh(10^50)"];
function releaseRefusal(ctx: CheckContext, source: string): void {
  const node = compileExpression(source, {});
  const packed = packCircuit(node);
  const seen = [exactReport(node), exactReport(node), exactReport(unpackCircuit(packed.tokens, packed.root))];
  if (seen.some((report) => !report.unverified)) {
    ctx.fail("FAIL release refusal", source, seen.map((report) => formatExact(report.value)).join(" | "));
  } else console.log("release refusal", source);
}
// A large real product passes through its reciprocal; that tiny real cannot reach the
// zero imaginary part, so these stay certified (v1.0.1 refused every one of them).
// atanh of a real above 1 is −iπ/2, and arctan of iy with y < −1 is −π/2 + …i,
// however the argument was built (mpmath's atanh and atan).
// A point just below the negative real axis keeps its side through a composition
// (mpmath at 600 digits); past 480 digits that side cannot be read, so it is refused.
const releaseKept: [string, string][] = [["1e-320*e/e-1e-320*(1+1e-100)", "−1×10^−420"], ["1e-320*(1+1e-100)-1e-320", "1×10^−420"], ["exp(-1000)+1", "1"], ["1e-400*pi+1e-400", "4.14159265359×10^−400"], ["((1+10^(-136))-1)+i*3/2", "1×10^−136 + 1.5i"], ["exp(800)-exp(800)", "0"], ["0^0", "1"], ["(1-1)^0", "1"], ["0^(1-1)", "1"], ["2^0", "1"], ["ln(0)^0", "unverified"], ["10^400/7", "1.428571428571×10^399"], ["10^400*2", "2×10^400"], ["10^400*i", "1×10^400i"], ["-(10^400)/3", "−3.333333333333×10^399"], ["10^300*10^100", "1×10^400"], ["atanh(1.694^3)", "0.208689790346 − 1.570796326795i"], ["atanh(-(1.5^3))", "−0.305454541161 + 1.570796326795i"], ["atanh(1.694^3)*atanh(32)", "−2.460877420177 − 0.376912529663i"], ["atan((-i-i)*asinh(9))", "−1.570796326795 − 0.174556001875i"], ["atan(-i*(1.5^3))", "−1.570796326795 − 0.305454541161i"], ["atan(i*(1.5^3))", "1.570796326795 + 0.305454541161i"], ["(10^108-i)*sin(atanh(-i))", "−0.868670961486 − 8.68670961486×10^107i"], ["(10^106-i)*sin(atanh(-i))", "−0.868670961486 − 8.68670961486×10^105i"], ["(10^300-(2-2*i))^-1", "1×10^−300 − 2×10^−600i"], ["1/(10^300-(2-2*i))", "1×10^−300 − 2×10^−600i"], ["(10^300+2)^-1", "1×10^−300"], ["((1+1/10^130)-1)+i/2", "1×10^−130 + 0.5i"], ["((1+1/10^130)-1)*i+1/2", "0.5 + 1×10^−130i"], ["((1+1/10^300)-1)+i/2", "unverified"], ["acos(1+10^-16)", "1.414213562373×10^−8i"], ["((i)*(6))-(acos((1+10^-16)))", "5.999999985858i"], ["acos(1-10^-200)", "1.414213562373×10^−100"], ["acos(-1-10^-200)", "3.14159265359 − 1.414213562373×10^−100i"], ["acos(2/2)", "0"], ["acos(cos(0))", "0"], ["acos(-(2/2))", "3.14159265359"], ["atanh(2/exp(300))", "1.029640044482×10^−130"], ["atanh(((-3)-(-5))/(sqrt(exp(600))))", "1.029640044482×10^−130"], ["sin(2/exp(300))", "1.029640044482×10^−130"], ["sin(2/exp(200))", "2.767793053473×10^−87"], ["sinh(10^300*i)", "−0.98575042516i"], ["cosh(10^20*i)", "0.763970404442"], ["ln(0)-ln(0)", "undefined"], ["0/0", "undefined"], ["1+exp(-10^20)", "1"], ["ln(ln(-5-i*10^-300))", "1.261257534955 − 1.097357207506i"], ["sqrt(acosh(-2-i*10^-120))", "1.536785569226 − 1.022131101599i"], ["acos(atanh(-5-i*10^-120))", "1.679425334464 + 1.238394314276i"], ["(-1/2-i*10^-120)^(1+i)", "−8.90036048882 + 7.393003249711i"], ["ln(-2-i*10^-300)-(2+3*i)^(-5)", "0.692818599089 − 3.143200548164i"], ["ln(ln(-5-i*10^-450))", "unverified"], ["sqrt(-4-i*10^-200)", "2.5×10^−201 − 2i"], ["(-8-i*10^-300)^(1/3)", "1 − 1.732050807569i"]];
function releaseKeptValue(ctx: CheckContext, source: string, want: string): void {
  const report = exactReport(compileExpression(source, {}));
  const got = report.unverified ? "unverified" : formatExact(report.value);
  if (got !== want) {
    ctx.fail("FAIL release kept", source, got, "want", want);
  } else console.log("release kept", source, got);
}

// A repeat evaluation in one process (the exact worker is reused across jobs) must
// match an evaluation with the pure cache off: same text, same note, same verdict.
// Large trig arguments: each certified a wrong value on a repeat before (cos(1e119) → −0.98499,
// true −0.37226; cos(1e125/1e130/1e200) → 1; sin(1e150/1e300) → −0; tan(1e140) → −2.306, true −3.307).
const repeatBigTrig = [
  "cos(1e119)", "cos(1e125)", "cos(1e130)", "cos(1e200)", "sin(1e150)", "sin(1e300)", "tan(1e140)",
  "sin(10^22)", "tan(10^22)", "cos(10^7)", "cos(2^60)",
  "sin(1e23)", "cos(1e23)", "tan(1e23)", "sin(1e60)", "cos(1e60)", "tan(1e60)", "sin(1e250)", "cos(1e250)", "tan(1e300)",
];
const repeatRows = ["1-cos(sqrt(1/10^130))", "6*i+(-6*i)", "cos(1e100)", "sin(1e22)", "tan(1e100)", "tan(1e22)", "cos(1e7)", "tan(pi/2)", ...repeatBigTrig];
const warmRows = ["1e100", "1e22", "1e7", "1e119", "1e300", "sqrt(1/10^130)", "6*i", "pi/2"];
const repeatVerdict = (report: ReturnType<typeof exactReport>) =>
  `${report.unverified ? "unverified" : formatExact(report.value)} [${report.singular ?? ""}]`;
/** Each repeat row evaluated with the pure cache off: the reference for the repeat blocks. */
function repeatColdVerdicts(): string[] {
  const saved = process.env.EML_NOCACHE;
  process.env.EML_NOCACHE = "1";
  const cold = repeatRows.map((source) => repeatVerdict(exactReport(compileExpression(source, {}))));
  if (saved === undefined) delete process.env.EML_NOCACHE;
  else process.env.EML_NOCACHE = saved;
  return cold;
}

const checks: CheckModule[] = [
  {
    id: 57,
    weight: 4163,
    run(ctx) {
      for (const source of releaseRefused.slice(0, 20)) releaseRefusal(ctx, source);
    },
  },
  {
    id: 58,
    weight: 3383,
    run(ctx) {
      for (const source of releaseRefused.slice(20)) releaseRefusal(ctx, source);
    },
  },
  {
    id: 59,
    weight: 20198,
    run(ctx) {
      for (const [source, want] of releaseKept.slice(0, 27)) releaseKeptValue(ctx, source, want);
    },
  },
  {
    id: 60,
    weight: 25748,
    run(ctx) {
      for (const [source, want] of releaseKept.slice(27)) releaseKeptValue(ctx, source, want);
    },
  },
  {
    id: 55,
    weight: 34363,
    run(ctx) {
      const cold = repeatColdVerdicts();
      repeatBigTrig.forEach((source) => {
        const want = cold[repeatRows.indexOf(source)];
        if (!want?.includes("argument too large to reduce")) {
          ctx.fail("FAIL large trig argument not flagged", source, want);
        }
      });
      for (const source of warmRows) exactReport(compileExpression(source, {}));
      repeatRows.forEach((source, index) => {
        const node = compileExpression(source, {});
        const first = repeatVerdict(exactReport(node));
        const second = repeatVerdict(exactReport(node));
        const packed = packCircuit(node);
        const trip = repeatVerdict(exactReport(unpackCircuit(packed.tokens, packed.root)));
        if (first !== cold[index] || second !== cold[index] || trip !== cold[index]) {
          ctx.fail("FAIL repeat evaluation", source, "cold", cold[index], "first", first, "second", second, "round trip", trip);
        } else {
          console.log("repeat evaluation", source, cold[index]);
        }
      });
    },
  },
  {
    id: 63,
    weight: 38590,
    run(ctx) {
      const cold = repeatColdVerdicts();
      // The same rows in one shared fresh child after earlier jobs, each evaluated twice.
      const shared = [...warmRows, ...repeatRows].map((source) => {
        const packed = packCircuit(compileExpression(source, {}));
        return { source, tokens: packed.tokens, root: packed.root, again: true as const };
      });
      const run = runTsx("scripts/fresh-exact.ts", JSON.stringify(shared));
      if (run.status !== 0) {
        ctx.fail("FAIL shared child repeat", run.status, run.stderr?.slice(0, 400));
      } else {
        const rows = JSON.parse(run.stdout) as Array<{ source: string; text: string; unverified: boolean; singular: string | null; again?: string; againSingular?: string | null }>;
        for (const row of rows.slice(warmRows.length)) {
          const want = cold[repeatRows.indexOf(row.source)];
          const first = `${row.unverified ? "unverified" : row.text} [${row.singular ?? ""}]`;
          const second = `${row.again} [${row.againSingular ?? ""}]`;
          if (first !== want || second !== want) {
            ctx.fail("FAIL shared child repeat", row.source, "cold", want, "first", first, "second", second);
          }
        }
      }
    },
  },
  {
    id: 56,
    weight: 4,
    run(ctx) {
      // A scaled add rebuilds its operands, so the add note's term is not a gate.
      // 2x + 1 near x = −1/2 kept no low-precision flag; x + 1 near −1 had one.
      // 10^(−300)·x + 1 printed 6.35×10^(−13) for 10^(−12) with no note.
      const vars = { x: V("x") };
      const lowRows: Array<[string, number]> = [["x+1", -1 + 1e-12], ["2*x+1", -0.5 + 1e-13], ["1e-300*x+1", -1e300 * (1 - 1e-12)]];
      for (const [source, x] of lowRows) {
        const report = evaluateReport(compileExpression(source, vars), { x: c(x) });
        if (report.singular !== SINGULAR_PRECISION) {
          ctx.fail("FAIL add precision note", source, report.value, report.singular);
        } else console.log("add precision note", source);
      }
      const plain = evaluateReport(compileExpression("2*x+1", vars), { x: c(3) });
      if (plain.singular !== null || Math.abs(plain.value.re - 7) > 1e-12) {
        ctx.fail("FAIL add precision note away from 0", plain);
      }
      // A preview past 20000 presses shows a prefix. The x in sin(sin(x)) is past it.
      const nested = pressPreviewForNode(compileExpression("sin(sin(x))", vars));
      if (!nested || nested.copyable || !nested.usesVariables || nested.preview.includes("x")) {
        ctx.fail("FAIL long press preview names its variables", nested && { ...nested, full: nested.full.slice(0, 40), presses: nested.presses.toString() });
      }
      let tower: Node = ONE;
      for (let i = 0; i < 16; i += 1) tower = E(tower, tower);
      const constant = pressPreviewForNode(tower);
      if (!constant || constant.usesVariables) {
        ctx.fail("FAIL long constant press preview", constant?.presses.toString());
      }
    },
  },
  {
    id: 73,
    run(ctx) {
      // A part made of a square or product of tiny inputs is not certified as 0. cosh(10^(−100))
      // is 1 + 5×10^(−201), which rounds to 1 at 120 digits, so cosh(10^(−100))^i certified 1.
      // A part that a raised reading shows and keeps is certified; past 480 digits it is refused.
      // A part that does not depend on the tiny inputs (a real function of a real) stays 0.
      const squareRows: Array<[string, string]> = [
        ["cosh(10^(-100))^i", "1 + 5×10^−201i"],
        ["cos(10^(-100))^i", "1 − 5×10^−201i"],
        ["cosh(10^(-100)*(1+i))", "1 + 1×10^−200i"],
        ["(1+2*10^(-120)*i)^(i/3)", "1 + 6.666666666667×10^−241i"],
        ["((1+10^(-110))-1)+i/2", "1×10^−110 + 0.5i"],
        ["cos(10^(-300))", "1"],
        ["cos(10^(-300))^2", "1"],
        ["tanh((1/3)*10^(-100)*i)", "3.333333333333×10^−101i"],
        ["cos(1+10^(-200)*i)", "0.540302305868 − 8.414709848079×10^−201i"],
      ];
      for (const [source, want] of squareRows) {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
        const got = formatExact(report.value);
        if (report.unverified || got !== want) {
          ctx.fail("FAIL squared tiny part", source, got, report.unverified ? "unverified" : "certified", "want", want);
        } else console.log("squared tiny part", source, got);
      }
      // True parts 2×10^(−500) i and 5×10^(−601) i: past the cap, so not certified.
      // A refused huge sum inside atanh or atan is refused, not undefined (it was √0/√0).
      for (const source of ["cos(2*10^(-250))^(-i)", "cosh(10^(-300))^i", "atanh(exp(-50)-10^400)", "atan(10^400-6+i)", "atan(10^400+i)"]) {
        const report = exactReport(compileExpression(source, {}), {}, { maxNodes: 400_000 });
        if (!report.unverified || report.singular !== null) {
          ctx.fail("FAIL refused tiny or huge part", source, formatExact(report.value), report.singular);
        } else console.log("refused", source);
      }
    },
  },
  {
    id: 74,
    run(ctx) {
      // The 671-press word for ln(1+10^(−130)) was listed as able to show an exact 0
      // depending on the cache. Built from its presses, alone, after the named
      // expression, and through the worker's wire, it is 10^(−130) every time.
      const named = compileExpression("ln(1+10^-130)", {});
      const words = rpnTokens(named, Number(circuitStats(named).rpnLength));
      const texts: string[] = [];
      if (words) {
        const read = (node: Node) => {
          const report = exactReport(node, {}, { maxNodes: 80_000 });
          return report.unverified ? "unverified" : formatExact(report.value);
        };
        texts.push(read(isolateCircuit(() => nodeFromRpn(words))));
        texts.push(read(named));
        texts.push(read(nodeFromRpn(words)));
        const packed = packCircuit(nodeFromRpn(words));
        texts.push(read(isolateCircuit(() => unpackCircuit(packed.tokens, packed.root))));
      }
      if (!words || words.length !== 671 || texts.some((text) => text !== "1×10^−130")) {
        ctx.fail("FAIL press word of ln(1+10^-130)", words?.length, texts);
      }
    },
  },
  {
    id: 75,
    run(ctx) {
      // The calculator builds the key captions in slices from keyCostEntries, with
      // other circuits built in between. The table must not depend on that.
      const four = { node: compileExpression("2*2", {}) };
      const tables = [
        { stack: [four], want: "add=K 89 sub=K 81 mul=K 87 div=K 87 pow=K 95 log=K 99 avg=K 133 hypot=K 233" },
        { stack: [four, four], want: "add=K 123 sub=K 7 mul=K 121 div=K 121 pow=K 129 log=K 133 avg=K 167 hypot=K 301" },
      ];
      for (const { stack, want } of tables) {
        const whole = keyCosts(stack, "0.5", "2");
        const sliced: Record<string, string> = {};
        for (const [id, caption] of keyCostEntries(stack, "0.5", "2")) {
          sliced[id] = caption;
          compileExpression("3+5", {});
        }
        const binary = ["add", "sub", "mul", "div", "pow", "log", "avg", "hypot"].map((id) => `${id}=${sliced[id]}`).join(" ");
        if (JSON.stringify(whole) !== JSON.stringify(sliced) || binary !== want) {
          ctx.fail("FAIL key captions", stack.length, binary);
        }
      }
    },
  },
  {
    id: 76,
    weight: 120,
    run(ctx) {
      // A submit compiles in the turn after the event (components/submitTurn.ts),
      // so key captions and other circuits can be built in between. Compiling
      // starts its own isolateCircuit, and what the screen reads from the node
      // must not depend on what was built before or after it.
      const summary = (node: Node) => {
        const stats = circuitStats(node);
        const packed = packCircuit(node);
        const report = evaluateReport(node, {}, { maxNodes: 80_000 });
        return JSON.stringify([
          stats.rpnLength.toString(), stats.dagGates, stats.depth, programNumberText(node),
          packed.tokens.length, packed.root, formatC(report.value), report.singular, report.unverified ?? false,
        ]);
      };
      const four = { node: compileExpression("2*2", {}) };
      for (const source of ["tan(10^(-5000))", "x+y", "ln(-1)"]) {
        const alone = summary(compileSubmission(source, "0.5", "2").node);
        for (const [id] of keyCostEntries([four], "0.5", "2")) if (id === "add") break;
        const late = compileSubmission(source, "0.5", "2");
        for (const entry of keyCostEntries([four, { node: late.node }], "0.5", "2")) void entry;
        const after = summary(late.node);
        if (alone !== after) {
          ctx.fail("FAIL submit compiled between other circuits", source, alone, after);
        }
      }
      const bound = compileSubmission("x*y", "0.5", "2").numbers;
      if (!close(bound.x, c(0.5, 0), 1e-12) || !close(bound.y, c(2, 0), 1e-12) || "y" in compileSubmission("x+1", "0.5", "").numbers) {
        ctx.fail("FAIL submit x and y", JSON.stringify(bound));
      }
      let missing = "";
      try {
        compileSubmission("x+y", "0.5", " ");
      } catch (err) {
        missing = err instanceof EmlError ? err.message : String(err);
      }
      if (missing !== "Give y a value.") {
        ctx.fail("FAIL submit empty y", missing);
      }
    },
  },
];

export default checks;
