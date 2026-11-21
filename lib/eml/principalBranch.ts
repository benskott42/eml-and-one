import { cexp, clogPrincipal, csub, eml, type C } from "./complex";
import { evaluateReport, nodeFromRpn } from "./node";

function principalValue(word: string): C {
  const stack: C[] = [];
  for (const ch of word) {
    if (ch === "1") {
      stack.push({ re: 1, im: 0 });
      continue;
    }
    const y = stack.pop();
    const x = stack.pop();
    if (!x || !y) return { re: Number.NaN, im: Number.NaN };
    stack.push(csub(cexp(x), clogPrincipal(y)));
  }
  return stack[0] ?? { re: Number.NaN, im: Number.NaN };
}

/** Lower-cut float value agrees with exp(x) − principal Log(y) to 1e−9. */
export function samePrincipal(word: string): boolean {
  const lower = evaluateReport(nodeFromRpn(word.split(""))).value;
  const upper = principalValue(word);
  // eml is the lower-cut gate. Keep the reference so a drift in evaluateReport is visible beside it.
  const viaEml = (() => {
    const stack: C[] = [];
    for (const ch of word) {
      if (ch === "1") stack.push({ re: 1, im: 0 });
      else {
        const y = stack.pop();
        const x = stack.pop();
        if (!x || !y) return { re: Number.NaN, im: Number.NaN };
        stack.push(eml(x, y));
      }
    }
    return stack[0] ?? { re: Number.NaN, im: Number.NaN };
  })();
  const tol = 1e-9 * Math.max(1, Math.abs(lower.re), Math.abs(viaEml.re));
  const close = (a: C, b: C) => Math.abs(a.re - b.re) <= tol && Math.abs(a.im - b.im) <= tol;
  return [lower.re, lower.im, upper.re, upper.im, viaEml.re, viaEml.im].every(Number.isFinite) && close(lower, upper) && close(lower, viaEml);
}
