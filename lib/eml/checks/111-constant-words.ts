import { exactReport, formatExact } from "../exact";
import { circuitStats, evaluateReport } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * Constant substitution: a closed constant with a shortest known word
 * (best-known.json) compiles to it when the word is shorter and does not add
 * a dependence on ln 0 = −∞. The value is unchanged in both engines.
 * Each row: source, K, exact text, whether the circuit logs 0.
 * Before: 1/2 K 35, −1/2 K 49, 1/3 K 45, −1/3 K 59, 2/3 K 63, 3/2 K 63,
 * −3/2 K 77, −5/2 K 119, −2 K 33, −3 K 43, 4 K 53, 2^2 K 61, e^2 K 45, 6/4 K 131,
 * pi*i K 165, −pi*i K 179, 2*pi*i K 199, −ln 2 K 39, −2/3 K 69, −5/3 K 115.
 */
const rows: [string, number, string, boolean][] = [
  ["1/2", 31, "0.5", false],
  ["-1/2", 29, "−0.5", true],
  ["1/3", 37, "0.333333333333", false],
  ["-1/3", 41, "−0.333333333333", false],
  ["2/3", 39, "0.666666666667", false],
  ["3/2", 41, "1.5", false],
  ["6/4", 41, "1.5", false],
  ["-3/2", 33, "−1.5", false],
  ["-5/2", 41, "−2.5", true],
  ["-2", 25, "−2", true],
  ["-3", 35, "−3", false],
  ["4", 39, "4", false],
  ["2^2", 39, "4", false],
  ["e^2", 21, "7.389056098931", false],
  ["1/e", 19, "0.367879441171", false],
  ["-e", 17, "−2.718281828459", true],
  // From the recorded exact facts, however the constant is spelled.
  ["-ln(2)", 27, "−0.69314718056", true],
  ["-2/3", 37, "−0.666666666667", true],
  ["-(2/3)", 37, "−0.666666666667", true],
  ["1/3-1", 39, "−0.666666666667", false],
  ["-5/3", 41, "−1.666666666667", true],
  ["-1-2/3", 41, "−1.666666666667", true],
  ["0.5", 31, "0.5", false],
];

/** Imaginary constants from the recorded πi multiple: source, K, exact text, ln 0, Im value. */
const imagRows: [string, number, string, boolean, number][] = [
  ["pi*i", 21, "3.14159265359i", true, Math.PI],
  ["i*pi/2*2", 21, "3.14159265359i", true, Math.PI],
  ["-pi*i", 45, "−3.14159265359i", true, -Math.PI],
  ["2*pi*i", 31, "6.28318530718i", false, 2 * Math.PI],
  ["4*pi*i/2", 31, "6.28318530718i", false, 2 * Math.PI],
  ["-2*pi*i", 31, "−6.28318530718i", false, -2 * Math.PI],
];

const checkModule: CheckModule = {
  id: 111,
  weight: 3000,
  run(ctx) {
    for (const [source, k, want, ln0] of rows) {
      const node = compileExpression(source, {});
      const got = Number(circuitStats(node).rpnLength);
      const exact = exactReport(node);
      const text = exact.unverified ? "unverified" : formatExact(exact.value);
      const float = evaluateReport(node);
      if (got !== k) ctx.fail(`FAIL constant word ${source} K ${got}, want K ${k}`);
      if (text !== want) ctx.fail(`FAIL constant word ${source} exact ${text}, want ${want}`);
      if (float.touchedLn0 !== ln0) ctx.fail(`FAIL constant word ${source} ln0 ${float.touchedLn0}, want ${ln0}`);
      const value = Number(want.replace("−", "-"));
      if (Math.abs(float.value.re - value) > 1e-11 * Math.max(1, Math.abs(value)) || float.value.im !== 0) {
        ctx.fail(`FAIL constant word ${source} float ${float.value.re} + ${float.value.im}i`);
      }
    }
    for (const [source, k, want, ln0, im] of imagRows) {
      const node = compileExpression(source, {});
      const got = Number(circuitStats(node).rpnLength);
      const exact = exactReport(node);
      const text = exact.unverified ? "unverified" : formatExact(exact.value);
      const float = evaluateReport(node);
      if (got !== k) ctx.fail(`FAIL constant word ${source} K ${got}, want K ${k}`);
      if (text !== want) ctx.fail(`FAIL constant word ${source} exact ${text}, want ${want}`);
      if (float.touchedLn0 !== ln0) ctx.fail(`FAIL constant word ${source} ln0 ${float.touchedLn0}, want ${ln0}`);
      if (Math.abs(float.value.im - im) > 1e-11 * Math.abs(im) || Math.abs(float.value.re) > 1e-11) {
        ctx.fail(`FAIL constant word ${source} float ${float.value.re} + ${float.value.im}i`);
      }
    }
  },
};

export default checkModule;
