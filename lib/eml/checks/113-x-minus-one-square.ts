import { exactReport, formatExact } from "../exact";
import { compileExpression } from "../parse";
import { packCircuit, unpackCircuit } from "../wire";
import type { CheckModule } from "./_types";

/**
 * (x − 1) must not certify the square term as a real 0.
 * (10^n+i)/(10^n−i) − 1 is −2×10^(−2n) + 2×10^(−n) i. At n = 200 that real
 * was certified as 0, on this branch and on v1.0.13. At n = 300 and n = 400
 * the square is past 480 digits; the remembered-sum path certified a pure
 * imaginary (v1.0.13 refused the n = 400 forms). A certified value has to be
 * the leading terms below. A refusal is also right when the square does not
 * fit. A vanished component certified as 0 is not. Multiplying by ±i or by 2i
 * swaps that square onto the other component: the 35 forms at n = 400 (these
 * seven bases times i*, *i, *(-i), /i, and *(2*i)) must refuse or certify the
 * rotated leading terms.
 * The worker wire evaluates the same circuit the app does.
 */
function sources(n: number): Array<[string, string]> {
  const n2 = 2 * n;
  return [
    [`(10^${n}+i)/(10^${n}-i)-1`, `−2×10^−${n2} + 2×10^−${n}i`],
    [`(10^${n}-i)/(10^${n}+i)-1`, `−2×10^−${n2} − 2×10^−${n}i`],
    [`(10^${n}+i)/(10^${n}+2*i)-1`, `−2×10^−${n2} − 1×10^−${n}i`],
    [`(10^${n}+2*i)/(10^${n}+i)-1`, `1×10^−${n2} + 1×10^−${n}i`],
    [`10^${n}/(10^${n}+i)-1`, `−1×10^−${n2} − 1×10^−${n}i`],
    [`1/(10^${n}+i)*10^${n}-1`, `−1×10^−${n2} − 1×10^−${n}i`],
    [`sqrt(10^${n}+i)/10^${n / 2}-1`, `1.25×10^−${n2 + 1} + 5×10^−${n + 1}i`],
  ];
}

const checkModule: CheckModule = {
  id: 113,
  weight: 67244,
  run(ctx) {
    const judge = (source: string, want: string, allowRefusal: boolean) => {
      const node = compileExpression(source, {});
      const packed = packCircuit(node);
      const reports = [
        ["app", exactReport(node)],
        ["wire", exactReport(unpackCircuit(packed.tokens, packed.root))],
      ] as const;
      for (const [path, report] of reports) {
        if (report.unverified) {
          if (!allowRefusal) ctx.fail(`FAIL x-1 ${path} ${source} refused`);
          continue;
        }
        const got = formatExact(report.value);
        if (got !== want) ctx.fail(`FAIL x-1 ${path} ${source} got="${got}" want="${want}"`);
      }
    };
    // These fit in 480 digits, so the square is part of the certified value.
    judge("(10^20+i)/(10^20-i)-1", "−2×10^−40 + 2×10^−20i", false);
    for (const [source, want] of sources(200)) judge(source, want, false);
    // The square is past the 480-digit cap. A certified leading term is right; so is a refusal.
    for (const n of [300, 400]) {
      for (const [source, want] of sources(n)) judge(source, want, true);
    }
    // ±i and 2i move the lost square onto the real component. v1.0.13 refused all 35.
    for (const [source, want] of rotations(400)) judge(source, want, true);
  },
};

/** Leading term `coeff × 10^(−exp)`, normalized the way formatExact prints it. */
function sci(coeff: number, exp: number): string {
  let c = coeff;
  let e = exp;
  while (Math.abs(c) >= 10) {
    c /= 10;
    e -= 1;
  }
  while (c !== 0 && Math.abs(c) < 1) {
    c *= 10;
    e += 1;
  }
  const sign = c < 0 ? "−" : "";
  const abs = Math.abs(c);
  const digits = Number.isInteger(abs) ? String(abs) : String(abs);
  return `${sign}${digits}×10^−${e}`;
}

function show(re: number, reExp: number, im: number, imExp: number): string {
  const imag = `${sci(Math.abs(im), imExp)}i`;
  return im < 0 ? `${sci(re, reExp)} − ${imag}` : `${sci(re, reExp)} + ${imag}`;
}

/**
 * (re, im) times i, i, −i, 1/i, and 2i. 1/i = −i, so those two rows share a value.
 */
function rotations(n: number): Array<[string, string]> {
  const n2 = 2 * n;
  const bases: Array<[string, number, number, number, number]> = [
    [`(10^${n}+i)/(10^${n}-i)-1`, -2, n2, 2, n],
    [`(10^${n}-i)/(10^${n}+i)-1`, -2, n2, -2, n],
    [`(10^${n}+i)/(10^${n}+2*i)-1`, -2, n2, -1, n],
    [`(10^${n}+2*i)/(10^${n}+i)-1`, 1, n2, 1, n],
    [`10^${n}/(10^${n}+i)-1`, -1, n2, -1, n],
    [`1/(10^${n}+i)*10^${n}-1`, -1, n2, -1, n],
    [`sqrt(10^${n}+i)/10^${n / 2}-1`, 1.25, n2 + 1, 5, n + 1],
  ];
  const out: Array<[string, string]> = [];
  for (const [expr, re, reExp, im, imExp] of bases) {
    const turned: Array<[string, number, number, number, number]> = [
      [`i*(${expr})`, -im, imExp, re, reExp],
      [`(${expr})*i`, -im, imExp, re, reExp],
      [`(${expr})*(-i)`, im, imExp, -re, reExp],
      [`(${expr})/i`, im, imExp, -re, reExp],
      [`(${expr})*(2*i)`, -2 * im, imExp, 2 * re, reExp],
    ];
    for (const [source, a, ae, b, be] of turned) out.push([source, show(a, ae, b, be)]);
  }
  return out;
}

export default checkModule;
