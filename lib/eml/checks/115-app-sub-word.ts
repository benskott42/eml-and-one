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
};

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
      const word = variableRpnFromNode(node);
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
