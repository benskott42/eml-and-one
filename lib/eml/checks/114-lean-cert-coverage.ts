import { exactReport, exactToFloat } from "../exact";
import {
  LEAN_BOX_SCALE,
  certifyRpnForLean,
  certifyRpnForLeanExt,
  formatLeanXSymTerm,
  leanSymBox,
  type LeanSym,
} from "../leanCert";
import { SHORT_PROGRAMS, nodeFromCompact } from "../programs";
import type { CheckModule } from "./_types";

/**
 * The Lean certificate checker (`Eml.Cert.certify`, mirrored by leanCert.ts)
 * proves these closed stored words by kernel computation alone, with no ln 0.
 * Since the 2026-11-27 rectangle bounds (formal/lean/Eml/CertBox.lean) it also
 * sees values such as e − exp e ≠ 0 and exp(e − ln 2) − exp e ≠ 0.
 *
 * For every certificate: its symbolic value agrees with the exact engine, and the
 * TypeScript box of every subterm contains the subterm's numeric value (the Lean
 * boxes are proved sound; this catches a transcription slip in the port).
 * The EmlExt checker (`Eml.Cert.certifyExt`, `ln 0 = −∞`) certifies EXT_ONLY as
 * well, and agrees with `certify` wherever that succeeds. Complex `exp` and `ln`
 * decide `pi` and `-ipi` in EmlExt, and `-ipi-strict` in ℂ.
 */
const CERTIFIED = [
  "0", "2", "3", "4", "e", "ln2", "sqrt2", "1/2-strict", "-1/2-strict", "1/2-alt", "2/3", "-1/3",
  "-3", "1/3-strict", "e^2", "3/2-strict", "-3/2-strict", "1/e-strict", "-e-strict", "2ipi", "-2ipi",
  "ipi-strict", "-2/3-strict", "-ipi-strict",
];

const EXT_ONLY = [
  "-inf", "-1", "-2", "1/2", "-1/2", "ipi", "i", "1/3", "3/2", "-3/2", "5/2", "-5/2", "1/e", "-e",
  "-ln2", "-2/3", "-5/3", "pi", "-ipi",
];

type Cx = { re: number; im: number };

/** Numeric value of a certificate term; `ln` is the lower cut (Im in [−π, π)). */
function value(s: LeanSym): Cx {
  switch (s.kind) {
    case "int":
      return { re: Number(s.n), im: 0 };
    case "e":
      return { re: Math.E, im: 0 };
    case "ipi":
      return { re: 0, im: Number(s.k) * Math.PI };
    case "exp": {
      const a = value(s.a);
      return { re: Math.exp(a.re) * Math.cos(a.im), im: Math.exp(a.re) * Math.sin(a.im) };
    }
    case "ln": {
      const a = value(s.a);
      const arg = Math.atan2(a.im, a.re);
      return { re: Math.log(Math.hypot(a.re, a.im)), im: a.im === 0 && a.re < 0 ? -Math.PI : arg };
    }
    case "neg": {
      const a = value(s.a);
      return { re: -a.re, im: -a.im };
    }
    case "add":
    case "sub": {
      const a = value(s.a);
      const b = value(s.b);
      const sign = s.kind === "add" ? 1 : -1;
      return { re: a.re + sign * b.re, im: a.im + sign * b.im };
    }
  }
}

function subterms(s: LeanSym, out: LeanSym[] = []): LeanSym[] {
  out.push(s);
  if ("a" in s) subterms(s.a, out);
  if ("b" in s) subterms(s.b, out);
  return out;
}

const scale = Number(LEAN_BOX_SCALE);
const inside = (lo: bigint, hi: bigint, x: number) => {
  const slack = 1e-9 * Math.max(1, Math.abs(x));
  return Number(lo) / scale <= x + slack && x - slack <= Number(hi) / scale;
};

const checkModule: CheckModule = {
  id: 114,
  weight: 2000,
  run(ctx) {
    const got: string[] = [];
    const gotExt: string[] = [];
    let boxes = 0;
    for (const [name, word] of Object.entries(SHORT_PROGRAMS)) {
      if (/[xy]/.test(word)) continue;
      const cert = certifyRpnForLean(word, 100000);
      const ext = certifyRpnForLeanExt(word, 100000);
      if (cert && (!ext || ext.xsym.kind !== "fin" || ext.leanXSym !== formatLeanXSymTerm({ kind: "fin", s: cert.sym }))) {
        ctx.fail(`FAIL lean certifyExt ${name}: ${ext?.leanXSym ?? "none"}, certify gives ${cert.leanSym}`);
      }
      if (!cert && ext) {
        gotExt.push(name);
        const exact = exactReport(nodeFromCompact(word));
        const w = exact.unverified ? null : exactToFloat(exact.value);
        if (ext.xsym.kind !== "fin") {
          const want = ext.xsym.kind === "negInf" ? -Infinity : Infinity;
          if (!w || w.re !== want) ctx.fail(`FAIL lean certifyExt ${name}: ${ext.display}, exact ${w?.re}`);
        } else {
          const v = value(ext.xsym.s);
          const tol = w ? 1e-9 * Math.max(1, Math.hypot(w.re, w.im)) : 0;
          if (!w || Math.abs(v.re - w.re) > tol || Math.abs(v.im - w.im) > tol) {
            ctx.fail(`FAIL lean certifyExt ${name}: ${ext.display} = ${v.re}+${v.im}i, exact ${w?.re}+${w?.im}i`);
          }
        }
      }
      if (!cert) continue;
      got.push(name);
      const v = value(cert.sym);
      const exact = exactReport(nodeFromCompact(word));
      if (exact.unverified) {
        ctx.fail(`FAIL lean cert ${name}: exact engine refused`);
        continue;
      }
      const w = exactToFloat(exact.value);
      const tol = 1e-9 * Math.max(1, Math.hypot(w.re, w.im));
      if (Math.abs(v.re - w.re) > tol || Math.abs(v.im - w.im) > tol) {
        ctx.fail(`FAIL lean cert ${name}: ${cert.display} = ${v.re}+${v.im}i, exact ${w.re}+${w.im}i`);
      }
      for (const t of subterms(cert.sym)) {
        const b = leanSymBox(t);
        if (!b) continue;
        boxes += 1;
        const x = value(t);
        if (!inside(b.rl, b.rh, x.re) || !inside(b.il, b.ih, x.im)) {
          ctx.fail(`FAIL lean box ${name}: subterm value ${x.re}+${x.im}i outside its box`);
        }
      }
    }
    const missing = CERTIFIED.filter((n) => !got.includes(n));
    const extra = got.filter((n) => !CERTIFIED.includes(n));
    if (missing.length) ctx.fail(`FAIL lean cert coverage lost: ${missing.join(", ")}`);
    if (extra.length) ctx.fail(`FAIL lean cert coverage gained (update CERTIFIED): ${extra.join(", ")}`);
    const missingExt = EXT_ONLY.filter((n) => !gotExt.includes(n));
    const extraExt = gotExt.filter((n) => !EXT_ONLY.includes(n));
    if (missingExt.length) ctx.fail(`FAIL lean EmlExt cert coverage lost: ${missingExt.join(", ")}`);
    if (extraExt.length) ctx.fail(`FAIL lean EmlExt cert coverage gained (update EXT_ONLY): ${extraExt.join(", ")}`);
    console.log(
      "lean cert coverage",
      `${got.length} words in ℂ, ${gotExt.length} more in EmlExt, ${boxes} subterm boxes checked`,
    );
  },
};

export default checkModule;
