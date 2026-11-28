import { APP_SUB_WORD, APP_WORDS, variableRpnFromNode } from "../export";
import { V, evaluateReport } from "../node";
import { compileExpression } from "../parse";
import type { CheckModule } from "./_types";

/**
 * The compiler's circuits for variable operands are exactly the words Lean proves:
 * x − y is APP_SUB_WORD (formal/lean/Eml/AppSub.lean, `appSub_correct`), and each
 * APP_WORDS entry is proved in formal/lean/Eml/AppOps.lean. If lowering changes one of
 * them, this fails until the word and its Lean proof are updated together. The float
 * engine agrees on sample points, zero operands among them.
 */
type Cx = { re: number; im: number };

const expected: Record<string, (x: Cx, y: Cx) => Cx | null> = {
  sub: (x, y) => ({ re: x.re - y.re, im: x.im - y.im }),
  add: (x, y) => ({ re: x.re + y.re, im: x.im + y.im }),
  mul: (x, y) => ({ re: x.re * y.re - x.im * y.im, im: x.re * y.im + x.im * y.re }),
  div: (x, y) => {
    const d = y.re * y.re + y.im * y.im;
    if (d === 0) return null;
    return { re: (x.re * y.re + x.im * y.im) / d, im: (x.im * y.re - x.re * y.im) / d };
  },
  neg: (x) => ({ re: -x.re, im: -x.im }),
  sq: (x) => ({ re: x.re * x.re - x.im * x.im, im: 2 * x.re * x.im }),
  twoMul: (x) => ({ re: 2 * x.re, im: 2 * x.im }),
  inv: (x) => {
    const d = x.re * x.re + x.im * x.im;
    return d === 0 ? null : { re: x.re / d, im: -x.im / d };
  },
  sqrt: (x) => {
    const r = Math.hypot(x.re, x.im);
    const re = Math.sqrt((r + x.re) / 2);
    const im = Math.sqrt((r - x.re) / 2);
    return { re, im: x.im < 0 || (x.im === 0 && Object.is(x.im, -0) && x.re < 0) ? -im : im };
  },
  exp: (x) => ({ re: Math.exp(x.re) * Math.cos(x.im), im: Math.exp(x.re) * Math.sin(x.im) }),
  ln: (x) => (x.re === 0 && x.im === 0 ? null : { re: Math.log(Math.hypot(x.re, x.im)), im: Math.atan2(x.im, x.re) }),
  subOne: (x) => ({ re: x.re - 1, im: x.im }),
  addOne: (x) => ({ re: x.re + 1, im: x.im }),
  subTwo: (x) => ({ re: x.re - 2, im: x.im }),
  pow: (x, y) => {
    // principal x^y = exp(y · log x), for x ≠ 0
    if (x.re === 0 && x.im === 0) return null;
    const lr = Math.log(Math.hypot(x.re, x.im));
    const li = Math.atan2(x.im, x.re);
    const re = y.re * lr - y.im * li;
    const im = y.re * li + y.im * lr;
    return { re: Math.exp(re) * Math.cos(im), im: Math.exp(re) * Math.sin(im) };
  },
  expE: (x) => ({ re: Math.exp(x.re) * Math.cos(x.im), im: Math.exp(x.re) * Math.sin(x.im) }),
  mulTwo: (x) => ({ re: 2 * x.re, im: 2 * x.im }),
  divTwo: (x) => ({ re: x.re / 2, im: x.im / 2 }),
  cube: (x) => {
    const re2 = x.re * x.re - x.im * x.im;
    const im2 = 2 * x.re * x.im;
    return { re: re2 * x.re - im2 * x.im, im: re2 * x.im + im2 * x.re };
  },
  sigma: (x) => cdiv(one, cadd(one, cexp(cneg(x)))),
  sinh: (x) => cmul(cmul(cexp(x), csub(one, cexp(cneg(cadd(x, x))))), half),
  cosh: (x) => cmul(cmul(cexp(x), csub(one, cneg(cexp(cneg(cadd(x, x)))))), half),
  artanh: (x) => {
    const den = csqrt(csub(one, x));
    const num = csqrt(cadd(one, x));
    const q = cdiv(num, den);
    return q ? cln(q) : null;
  },
  arcosh: (x) => cln(cadd(x, cmul(csqrt(csub(x, one)), csqrt(cadd(x, one))))),
};

const one: Cx = { re: 1, im: 0 };
const half: Cx = { re: 0.5, im: 0 };

function cneg(z: Cx): Cx {
  return { re: -z.re, im: -z.im };
}
function cadd(a: Cx, b: Cx): Cx {
  return { re: a.re + b.re, im: a.im + b.im };
}
function csub(a: Cx, b: Cx): Cx {
  return { re: a.re - b.re, im: a.im - b.im };
}
function cmul(a: Cx, b: Cx): Cx {
  return { re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re };
}
function cdiv(a: Cx, b: Cx): Cx | null {
  const d = b.re * b.re + b.im * b.im;
  if (d === 0) return null;
  return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d };
}
function cexp(z: Cx): Cx {
  return { re: Math.exp(z.re) * Math.cos(z.im), im: Math.exp(z.re) * Math.sin(z.im) };
}
function csqrt(z: Cx): Cx {
  const r = Math.hypot(z.re, z.im);
  const re = Math.sqrt((r + z.re) / 2);
  const im = Math.sqrt((r - z.re) / 2);
  return { re, im: z.im < 0 || (z.im === 0 && Object.is(z.im, -0) && z.re < 0) ? -im : im };
}
function cln(z: Cx): Cx | null {
  if (z.re === 0 && z.im === 0) return null;
  return { re: Math.log(Math.hypot(z.re, z.im)), im: Math.atan2(z.im, z.re) };
}

const points: [Cx, Cx][] = [
  [{ re: 3, im: 0 }, { re: 5, im: 0 }],
  [{ re: 0, im: 0 }, { re: 0, im: 0 }],
  [{ re: 2, im: -1 }, { re: 0, im: 0 }],
  [{ re: 0, im: 0 }, { re: -1.5, im: 2 }],
  [{ re: -1.5, im: 2 }, { re: 0.25, im: -3 }],
  [{ re: -4, im: 0 }, { re: 0.5, im: 0.5 }],
  [{ re: 0, im: 3 }, { re: 0, im: -3 }],
];

const checkModule: CheckModule = {
  id: 115,
  weight: 900,
  run(ctx) {
    const x = V("x");
    const y = V("y");
    const words: [string, string, string][] = [
      ["sub", "x-y", APP_SUB_WORD],
      ...Object.entries(APP_WORDS).map(([name, w]) => [name, w.source, w.word] as [string, string, string]),
    ];
    for (const [name, source, want] of words) {
      const node = compileExpression(source, { x, y });
      const word = variableRpnFromNode(node, 40000);
      if (word !== want) {
        ctx.fail(`FAIL ${source} circuit changed (K ${word?.length ?? "?"}, Lean proves K ${want.length}): update export.ts and formal/lean/Eml/App*.lean`);
        continue;
      }
      const f = expected[name];
      if (!f) {
        ctx.fail(`FAIL ${source}: no float reference`);
        continue;
      }
      for (const [a, b] of points) {
        const want = f(a, b);
        if (!want) continue;
        const r = evaluateReport(node, { x: a, y: b });
        const scale = Math.max(1, Math.hypot(a.re, a.im), Math.hypot(b.re, b.im), Math.hypot(want.re, want.im));
        if (Math.abs(r.value.re - want.re) > 1e-9 * scale || Math.abs(r.value.im - want.im) > 1e-9 * scale) {
          ctx.fail(`FAIL ${source} at x = ${a.re}+${a.im}i, y = ${b.re}+${b.im}i: ${r.value.re} + ${r.value.im}i, want ${want.re} + ${want.im}i`);
        }
      }
    }
  },
};

export default checkModule;
