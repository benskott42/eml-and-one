/**
 * Golden harness corpus.
 * Each expression is evaluated in both exact and float modes,
 * and the results are checked for consistency.
 */

export const basicExpressions = [
  "1+1",
  "pi",
  "e",
  "i",
  "0",
  "-1",
  "2",
  "1/2",
  "2/3",
  "sqrt(2)",
  "ln(-1)",
  "exp(1)",
  "tan(pi/2)",
];

/**
 * Cancellation cases: ((1+10^(-k))-1)+i*c and (i*(1+10^(-k))-i)*i+i*c
 * for k in {110,124,126,128,130,132,136} and c in {1/2,1/3,3/2,-1/2,10^10/3}
 */
export function getCancellationCases(): string[] {
  const kValues = [110, 124, 126, 128, 130, 132, 136];
  const cValues = ["1/2", "1/3", "3/2", "-1/2", "10^10/3"];
  const cases: string[] = [];
  
  for (const k of kValues) {
    for (const c of cValues) {
      // ((1+10^(-k))-1)+i*c
      cases.push(`((1+10^(-${k}))-1)+i*${c}`);
      // (i*(1+10^(-k))-i)*i+i*c
      cases.push(`(i*(1+10^(-${k}))-i)*i+i*${c}`);
    }
  }
  
  return cases;
}

/**
 * Edge cases for transcendental functions
 */
export const transcendentalEdgeCases = [
  // ln edge cases
  "ln(1+10^-130)",
  "ln(1+3*10^(-130))",
  "ln(-1)",
  "ln(-2-10^(-20)*i)",
  "ln(-2-10^(-110)*i)",
  "ln(-2-10^(-112)*i)",
  "ln(-2-10^(-115)*i)",
  "ln(-2-10^(-130)*i)",
  
  // tan edge cases
  "tan(1e100)",
  "tan(1e22)",
  "tan(10^(-20))",
  "tan(10^(-40))",
  "tan(1e-5000)",
  
  // cos edge cases
  "cos(1e100)",
  "cos(1e7)",
  "cos(10^(-50))",
  "cos(10^(-200))",
  
  // sin edge cases
  "sin(1e22)",
  "sin(1e-18+1e-120*i)",
  "sin(1e-200)",
  
  // Special cancellations
  "1-cos(sqrt(1/10^130))",
  "cos(10^(-50))-1",
  "cos(3*10^(-50))-1",
  
  // sinh, artanh, arcsin
  "sinh(1e-7)-1e-7",
  "sinh(0.00005*i)",
  "artanh(1e-7)-1e-7",
  "arcsin(1e-5)-1e-5",
  "arcsin(2)",
  "arcsin(-2*i)",
  "asinh(1e200)",
  
  // tanh
  "tanh(1e-10*i)",
  "tanh(1e-16*i)",
  "tanh(10^(-45))-10^(-45)",
  "tanh(3*10^(-45))-3*10^(-45)",
  
  // arctan
  "arctan(10^(-45))-10^(-45)",
  "arctan(3*10^(-45))-3*10^(-45)",
];

/**
 * Complex arithmetic edge cases
 */
export const complexEdgeCases = [
  // Known bug: drops to half with no flag (v1.1)
  "6.103e-120*i+6.103e-120*i",
  "0.00005*i+0.00005*i",
  "0.00006103*i+0.00006103*i",
  
  // Other complex cases
  "3.1*i+0.04",
  "4*i+0.5*i",
  "-4*i+1",
  "0.00005*i+4*i",
  "6*i+(-6*i)",
  "(2+3*i)+(-1+0.2*i)",
  "1e-120*(2+i)",
  "3*((1e-120*i)-(2e-120))",
  "2*(1e-18+1e-125*i)",
];

/**
 * Integer powers of directed infinities
 */
export const infinityPowers = [
  "ln(0)^2",
  "ln(0)^3",
  "ln(0)^(-1)",
  "ln(0)^(-2)",
  "(ln(0)*i)^2",
  "(ln(0)*i)^3",
  "(ln(0)*i)^(-1)",
];

/**
 * Pole cases
 */
export const poleCases = [
  "tan(pi/2)",
  "tan(3*pi/2)",
  "1/0",
  "ln(0)",
];

/**
 * Precision and series shortcut cases
 */
export const precisionCases = [
  "exp(1e-432)-1",
  "tan(10^(-5000))",
  "exp(10^(-1000))-1",
  "sin(1e-300)-1e-300",
  "exp(1e-50)-1",
  "ln(1+1e-50)-1e-50",
  "(sqrt(1+1e-50)-1)-5e-51",
];

/**
 * Pack/unpack round-trip test cases
 */
export const packUnpackCases = [
  "1+1",
  "tan(1e100)",
  "ln(1+10^-130)",
  "6.103e-120*i+6.103e-120*i",
  "exp(1e-432)-1",
];

/**
 * Get all corpus expressions
 */
/**
 * Rows from the open exact-zero (#38) and infinity (#39) releases, plus the
 * severity-1 repros. `(1+1e-20*i)-1` is the exact-zero sibling at exact.ts
 * residueParts: its real part is 0, its imaginary part is ~1e-20, and that
 * sibling sits under 10^(work-12). `sqrt(-0)` is the signed-zero wire row.
 */
export const releaseRows = [
  "-5e-801",
  "1e-100*1.5/1.5-1e-100",
  "1e-50*1.5/1.5-1e-50",
  "1e-500*e/e-1e-500",
  "1e-500",
  "exp(-1200)",
  "1e-400*(1+1e-100)-1e-400",
  "1e-400*pi+1e-400",
  "exp(-1000)-exp(-1001)",
  "1e-400-1e-400*(1+1e-50)",
  "(1e-400)*3/3-(1e-400)*(1+1e-50)",
  "inf+1",
  "ln(0)+0",
  "ln(0)-1",
  "ln(0)+i",
  "(inf*i)/2",
  "ln(ln(0)*i)",
  "1e-320*(1+1e-100)-1e-320",
  "exp(ln(ln(0))*i)",
  "exp(800)-exp(800)",
  "sqrt(-0)",
  "(1+1e-20*i)-1",
];

export function getAllCorpus(): string[] {
  const seen = new Set<string>();
  const out: string[] = [];
  for (const source of [
    ...basicExpressions,
    ...getCancellationCases(),
    ...transcendentalEdgeCases,
    ...complexEdgeCases,
    ...infinityPowers,
    ...poleCases,
    ...precisionCases,
    ...wireBugCases,
    ...releaseRows,
  ]) {
    if (seen.has(source)) continue;
    seen.add(source);
    out.push(source);
  }
  return out;
}

/**
 * Wire-mode test cases: bugs that only manifest through packCircuit→unpackCircuit→evaluate
 * These must be evaluated in a fresh process over the packed wire to reproduce.
 * Note: ((1+10^(-136))-1)+i*3/2 is already covered by cancellation cases
 */
export const wireBugCases = [
  // Severity-1 bug: tiny real part ~1e-130 dropped over wire (owned by bigfixer)
  "((1+10^(-130))-1)+i/2",
  "((1+10^(-130))-1)+i*(1+10^(-130))/2",
];

/**
 * Heavy corpus (slow cases, not run in CI by default)
 */
export const heavyCorpus = [
  "ln(1+3*10^(-300))",
  "log(1+3*1e-300)",
  "(exp(1e-50)-1)-1e-50",
  "cos(1e-50)-1+5e-101",
];
