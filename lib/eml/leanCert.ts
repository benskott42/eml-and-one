import { binaryToRpn } from "./binary";
import { isProgram } from "./programIndex";

/**
 * Exact TypeScript mirror of `formal/lean/Eml/Cert.lean`.
 *
 * When `certifyRpnForLean(rpn)` returns a `LeanCert`, Lean's kernel-verified
 * `Eml.Cert.certify` returns the exact same `Sym` value, and
 * `Eml.Cert.certify_sound (by decide)` proves both the `ℂ` and `EmlExt`
 * evaluations in one line.
 */

const Z0 = BigInt(0);
const Z1 = BigInt(1);
const Z2 = BigInt(2);
const ZM1 = BigInt(-1);

export type LeanSym =
  | { kind: "int"; n: bigint }
  | { kind: "e" }
  | { kind: "ipi"; k: bigint }
  | { kind: "exp"; a: LeanSym }
  | { kind: "ln"; a: LeanSym }
  | { kind: "neg"; a: LeanSym }
  | { kind: "add"; a: LeanSym; b: LeanSym }
  | { kind: "sub"; a: LeanSym; b: LeanSym };

export type LeanCert = {
  rpn: string;
  sym: LeanSym;
  /** Lean term of type `Eml.Cert.Sym`, e.g. `Sym.int 0` or `Sym.e`. */
  leanSym: string;
  /** Human-readable value text. */
  display: string;
};

function symEq(a: LeanSym, b: LeanSym): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "int":
      return a.n === (b as typeof a).n;
    case "e":
      return true;
    case "ipi":
      return a.k === (b as typeof a).k;
    case "exp":
    case "ln":
    case "neg":
      return symEq(a.a, (b as typeof a).a);
    case "add":
    case "sub":
      return symEq(a.a, (b as typeof a).a) && symEq(a.b, (b as typeof a).b);
  }
}

function eSubSmall(a: LeanSym, b: LeanSym): boolean {
  return a.kind === "e" && b.kind === "int" && b.n <= Z2;
}

function cls(s: LeanSym): 0 | 1 | 2 {
  switch (s.kind) {
    case "int":
      return s.n > Z0 ? 2 : 1;
    case "e":
      return 2;
    case "ipi":
      return 0;
    case "exp":
      return cls(s.a) >= 1 ? 2 : 0;
    case "ln":
      return cls(s.a) === 2 ? 1 : 0;
    case "neg":
      return cls(s.a) >= 1 ? 1 : 0;
    case "add":
      return cls(s.a) >= 1 && cls(s.b) >= 1 ? 1 : 0;
    case "sub":
      if (eSubSmall(s.a, s.b)) return 2;
      return cls(s.a) >= 1 && cls(s.b) >= 1 ? 1 : 0;
  }
}

// ---- Fixed-point boxes (formal/lean/Eml/CertBox.lean and CertBoxC.lean) ----

/** Lean's `Int` division (`Int.ediv`): Euclidean, the remainder is never negative. */
function ediv(n: bigint, d: bigint): bigint {
  const q = n / d;
  if (n % d < Z0) return d > Z0 ? q - Z1 : q + Z1;
  return q;
}

const D = BigInt("281474976710656"); // 2^48
const N = BigInt(65536); // 2^16
const cdiv = (n: bigint, d: bigint) => -ediv(-n, d);
const E_LO = ediv(BigInt(2718281828) * D, BigInt(1000000000));
const E_HI = cdiv(BigInt("27182818286") * D, BigInt("10000000000"));
const PI_LO = ediv(BigInt(3141592) * D, BigInt(1000000));
const PI_HI = cdiv(BigInt(3141593) * D, BigInt(1000000));
const EXP_CAP = BigInt(64) * D;

export type Box = { rl: bigint; rh: bigint; il: bigint; ih: bigint };

function sqDn(k: number, r: bigint): bigint {
  for (let i = 0; i < k; i += 1) r = ediv(r * r, D);
  return r;
}

function sqUp(k: number, r: bigint): bigint {
  for (let i = 0; i < k; i += 1) r = cdiv(r * r, D);
  return r;
}

function expLo(x: bigint): bigint {
  const m = x < EXP_CAP ? x : EXP_CAP;
  return N * D + m < Z0 ? Z0 : sqDn(16, ediv(N * D + m, N));
}

function expHi(x: bigint): bigint | null {
  return EXP_CAP < x ? null : sqUp(16, cdiv(N * D * D, N * D - x));
}

const lnLo = (x: bigint) => D - cdiv(D * D, x);
const lnHi = (x: bigint) => x - D;

const minI = (a: bigint, b: bigint) => (a <= b ? a : b);
const maxI = (a: bigint, b: bigint) => (a >= b ? a : b);
const absI = (a: bigint) => (a < Z0 ? -a : a);

const KH = 4;
const PS = Z1 << 64n;
const BOX_FUEL = 16;
const halfPiLo = ediv(PI_LO, Z2);
const halfPiHi = cdiv(PI_HI, Z2);

function imul(a1: bigint, a2: bigint, b1: bigint, b2: bigint, S: bigint): [bigint, bigint] {
  const p11 = a1 * b1, p12 = a1 * b2, p21 = a2 * b1, p22 = a2 * b2;
  const lo = minI(minI(p11, p12), minI(p21, p22));
  const hi = maxI(maxI(p11, p12), maxI(p21, p22));
  return [ediv(lo, S), cdiv(hi, S)];
}

function idiv(a1: bigint, a2: bigint, b1: bigint, b2: bigint): [bigint, bigint] {
  const flo = (n: bigint, d: bigint) => ediv(n * D, d);
  const cei = (n: bigint, d: bigint) => cdiv(n * D, d);
  return [
    minI(minI(flo(a1, b1), flo(a1, b2)), minI(flo(a2, b1), flo(a2, b2))),
    maxI(maxI(cei(a1, b1), cei(a1, b2)), maxI(cei(a2, b1), cei(a2, b2))),
  ];
}

function clampU(x: bigint): bigint {
  return maxI(-D, minI(D, x));
}

function isqrtSearch(fuel: number, lo: bigint, hi: bigint, n: bigint): bigint {
  let f = fuel, a = lo, b = hi;
  while (f > 0) {
    if (b <= a + Z1) return a;
    const mid = ediv(a + b, Z2);
    if (mid * mid <= n) a = mid;
    else b = mid;
    f -= 1;
  }
  return a;
}

function sqrtLo(n: bigint): bigint {
  const r = n <= Z0 ? Z0 : isqrtSearch(512, Z0, n + Z1, n);
  return Z0 <= r && r * r <= n ? r : Z0;
}

function sqrtHi(n: bigint): bigint {
  const r = (n <= Z0 ? Z0 : isqrtSearch(512, Z0, n + Z1, n)) + Z1;
  return Z0 <= r && n <= r * r ? r : n + D;
}

function lnSearchLo(fuel: number, x: bigint, lo: bigint, hi: bigint): bigint {
  let f = fuel, a = lo, b = hi;
  while (f > 0) {
    if (b <= a) return a;
    const mid = ediv(a + b + Z1, Z2);
    const h = expHi(mid);
    if (h !== null && h <= x) a = mid;
    else b = mid - Z1;
    f -= 1;
  }
  return a;
}

function lnSearchHi(fuel: number, x: bigint, lo: bigint, hi: bigint): bigint {
  let f = fuel, a = lo, b = hi;
  while (f > 0) {
    if (b <= a) return b;
    const mid = ediv(a + b, Z2);
    if (mid <= EXP_CAP && x <= expLo(mid)) b = mid;
    else a = mid + Z1;
    f -= 1;
  }
  return b;
}

function lnSLo(x: bigint): bigint {
  const c = lnSearchLo(BOX_FUEL, x, lnLo(x), minI(lnHi(x), EXP_CAP));
  const h = expHi(c);
  return h !== null && h <= x ? c : lnLo(x);
}

function lnSHi(x: bigint): bigint {
  const c = lnSearchHi(BOX_FUEL, x, lnLo(x), lnHi(x));
  return c <= EXP_CAP && x <= expLo(c) ? c : lnHi(x);
}

type CS = { cl: bigint; ch: bigint; sl: bigint; sh: bigint };

function sqI(a: bigint, b: bigint, S: bigint): [bigint, bigint] {
  if (Z0 <= a) return [ediv(a * a, S), cdiv(b * b, S)];
  if (b <= Z0) return [ediv(b * b, S), cdiv(a * a, S)];
  return [Z0, cdiv(maxI(a * a, b * b), S)];
}

function taylorCS(u: bigint): CS {
  const u2 = imul(u, u, u, u, PS);
  const u3 = imul(u2[0], u2[1], u, u, PS);
  const u4 = imul(u2[0], u2[1], u2[0], u2[1], PS);
  const r = cdiv(u4[1] * 5n, 96n) + Z2;
  return {
    cl: PS - cdiv(u2[1], Z2) - r,
    ch: PS - ediv(u2[0], Z2) + r,
    sl: u - cdiv(u3[1], 6n) - r,
    sh: u - ediv(u3[0], 6n) + r,
  };
}

function dblCS(q: CS): CS {
  const sq = sqI(q.cl, q.ch, PS);
  const pr = imul(q.sl, q.sh, q.cl, q.ch, PS);
  return {
    cl: maxI(-PS, Z2 * sq[0] - PS),
    ch: minI(PS, Z2 * sq[1] - PS),
    sl: maxI(-PS, Z2 * pr[0]),
    sh: minI(PS, Z2 * pr[1]),
  };
}

function trigStep(k: number, q: CS): CS {
  let r = q;
  for (let i = 0; i < k; i += 1) r = dblCS(r);
  return r;
}

function uOf(t: bigint): bigint {
  return t * ediv(PS, D * (Z2 ** BigInt(KH)));
}

function trigPt(t: bigint): CS {
  const q = trigStep(KH, taylorCS(uOf(t)));
  const s = ediv(PS, D);
  return { cl: ediv(q.cl, s), ch: cdiv(q.ch, s), sl: ediv(q.sl, s), sh: cdiv(q.sh, s) };
}

function trigK(a: bigint): bigint {
  return ediv(a + PI_LO, Z2 * PI_LO);
}

function trigT1(a: bigint): bigint {
  const k = trigK(a);
  return Z0 <= k ? a - Z2 * k * PI_HI : a - Z2 * k * PI_LO;
}

function trigT2(a: bigint): bigint {
  const k = trigK(a);
  return Z0 <= k ? a - Z2 * k * PI_LO : a - Z2 * k * PI_HI;
}

function trigW(a: bigint, b: bigint): bigint {
  return b - a + (trigT2(a) - trigT1(a));
}

function trigI(a: bigint, b: bigint): CS {
  const t1 = trigT1(a);
  const w = trigW(a, b);
  const q = trigPt(t1);
  if (absI(t1) <= 4n * D) {
    return {
      cl: clampU(q.cl - w),
      ch: clampU(q.ch + w),
      sl: clampU(q.sl - w),
      sh: clampU(q.sh + w),
    };
  }
  return { cl: -D, ch: D, sl: -D, sh: D };
}

function asinSearchLo(fuel: number, s: bigint, lo: bigint, hi: bigint): bigint {
  let f = fuel, a = lo, b = hi;
  while (f > 0) {
    if (b <= a) return a;
    const mid = ediv(a + b + Z1, Z2);
    if (trigPt(mid).sh <= s) a = mid;
    else b = mid - Z1;
    f -= 1;
  }
  return a;
}

function asinSearchHi(fuel: number, s: bigint, lo: bigint, hi: bigint): bigint {
  let f = fuel, a = lo, b = hi;
  while (f > 0) {
    if (b <= a) return b;
    const mid = ediv(a + b, Z2);
    if (s <= trigPt(mid).sl) b = mid;
    else a = mid + Z1;
    f -= 1;
  }
  return b;
}

function asinLo(s: bigint): bigint {
  const th = asinSearchLo(BOX_FUEL, s, -halfPiLo, halfPiLo);
  return -halfPiLo <= th && th <= halfPiLo && trigPt(th).sh <= s ? th : -halfPiHi;
}

function asinHi(s: bigint): bigint {
  const th = asinSearchHi(BOX_FUEL, s, -halfPiLo, halfPiLo);
  return -halfPiLo <= th && th <= halfPiLo && s <= trigPt(th).sl ? th : halfPiHi;
}

function nxOf(b: Box): bigint {
  if (Z0 < b.rl) return b.rl;
  if (b.rh < Z0) return -b.rh;
  return Z0;
}

function nyOf(b: Box): bigint {
  if (Z0 < b.il) return b.il;
  if (b.ih < Z0) return -b.ih;
  return Z0;
}

function rloOf(b: Box): bigint {
  const x = nxOf(b), y = nyOf(b);
  return sqrtLo(x * x + y * y);
}

function rhiOf(b: Box): bigint {
  return sqrtHi(maxI(b.rl * b.rl, b.rh * b.rh) + maxI(b.il * b.il, b.ih * b.ih));
}

function ratioBox(b: Box): [bigint, bigint] {
  const rlo = rloOf(b), rhi = rhiOf(b);
  return Z0 < b.rl ? idiv(b.il, b.ih, rlo, rhi) : idiv(b.rl, b.rh, rlo, rhi);
}

function argLoOf(b: Box): bigint {
  const s = ratioBox(b);
  if (Z0 < b.rl) return asinLo(clampU(s[0]));
  if (Z0 < b.il) return halfPiLo - asinHi(clampU(s[1]));
  return asinLo(clampU(s[0])) - halfPiHi;
}

function argHiOf(b: Box): bigint {
  const s = ratioBox(b);
  if (Z0 < b.rl) return asinHi(clampU(s[1]));
  if (Z0 < b.il) return halfPiHi - asinLo(clampU(s[0]));
  return asinHi(clampU(s[1])) - halfPiLo;
}

function bExp(b: Box): Box | null {
  const h = expHi(b.rh);
  if (h === null) return null;
  if (b.il === Z0 && b.ih === Z0) return { rl: expLo(b.rl), rh: h, il: Z0, ih: Z0 };
  const q = trigI(b.il, b.ih);
  const lo = expLo(b.rl);
  const re = imul(lo, h, q.cl, q.ch, D);
  const im = imul(lo, h, q.sl, q.sh, D);
  return { rl: re[0], rh: re[1], il: im[0], ih: im[1] };
}

function bLn(b: Box): Box | null {
  if (b.il === Z0 && b.ih === Z0) {
    if (Z0 < b.rl) return { rl: lnSLo(b.rl), rh: lnSHi(b.rh), il: Z0, ih: Z0 };
    if (b.rh < Z0) return { rl: lnSLo(-b.rh), rh: lnSHi(-b.rl), il: -PI_HI, ih: -PI_LO };
    return null;
  }
  if (!(Z0 < b.rl || Z0 < b.il || b.ih < Z0)) return null;
  if (rloOf(b) <= Z0) return null;
  return { rl: lnSLo(rloOf(b)), rh: lnSHi(rhiOf(b)), il: argLoOf(b), ih: argHiOf(b) };
}

/** Fixed-point box of `s` (`n` stands for `n / 2^48`), as `Eml.Cert.bnd`. Exported for checks. */
export function leanSymBox(s: LeanSym): Box | null {
  return bnd(s);
}

export const LEAN_BOX_SCALE = D;

function bnd(s: LeanSym): Box | null {
  switch (s.kind) {
    case "int":
      return { rl: s.n * D, rh: s.n * D, il: Z0, ih: Z0 };
    case "e":
      return { rl: E_LO, rh: E_HI, il: Z0, ih: Z0 };
    case "ipi":
      return Z0 <= s.k
        ? { rl: Z0, rh: Z0, il: s.k * PI_LO, ih: s.k * PI_HI }
        : { rl: Z0, rh: Z0, il: s.k * PI_HI, ih: s.k * PI_LO };
    case "exp": {
      const b = bnd(s.a);
      return b ? bExp(b) : null;
    }
    case "ln": {
      const b = bnd(s.a);
      return b ? bLn(b) : null;
    }
    case "neg": {
      const b = bnd(s.a);
      return b ? { rl: -b.rh, rh: -b.rl, il: -b.ih, ih: -b.il } : null;
    }
    case "add": {
      const x = bnd(s.a);
      const y = bnd(s.b);
      return x && y ? { rl: x.rl + y.rl, rh: x.rh + y.rh, il: x.il + y.il, ih: x.ih + y.ih } : null;
    }
    case "sub": {
      const x = bnd(s.a);
      const y = bnd(s.b);
      return x && y ? { rl: x.rl - y.rh, rh: x.rh - y.rl, il: x.il - y.ih, ih: x.ih - y.il } : null;
    }
  }
}

function boxNz(s: LeanSym): boolean {
  const b = bnd(s);
  return !!b && (Z0 < b.rl || b.rh < Z0 || Z0 < b.il || b.ih < Z0);
}

function boxPos(s: LeanSym): boolean {
  const b = bnd(s);
  return !!b && b.il === Z0 && b.ih === Z0 && Z0 < b.rl;
}

function boxNeg(s: LeanSym): boolean {
  const b = bnd(s);
  return !!b && b.il === Z0 && b.ih === Z0 && b.rh < Z0;
}

function boxStrip(s: LeanSym): boolean {
  const b = bnd(s);
  return !!b && -PI_LO <= b.il && b.ih < PI_LO;
}

/** `e − n` for any integer `n`: never 0, since 2 < e < 3 (Cert.lean eSubInt). */
function eSubInt(a: LeanSym, b: LeanSym): boolean {
  return a.kind === "e" && b.kind === "int";
}

/** Provably nonzero: structurally, or by the value's box (Cert.lean nz). */
function nz(s: LeanSym): boolean {
  return nz0(s) || boxNz(s);
}

function nz0(s: LeanSym): boolean {
  switch (s.kind) {
    case "int":
      return s.n !== Z0;
    case "e":
      return true;
    case "ipi":
      return s.k !== Z0;
    case "exp":
      return true;
    case "ln":
      return false;
    case "neg":
      return nz0(s.a);
    case "add":
      return false;
    case "sub":
      return eSubInt(s.a, s.b);
  }
}

/** `exp (ln u) = u` needs only `u ≠ 0` (Cert.lean lnInvOk). */
function lnInvOk(u: LeanSym): boolean {
  return cls(u) === 2 || nz(u);
}

function negOf(v: LeanSym): LeanSym {
  if (v.kind === "int") return { kind: "int", n: -v.n };
  if (v.kind === "ipi") return { kind: "ipi", k: -v.k };
  if (v.kind === "neg") return v.a;
  return { kind: "neg", a: v };
}

function rExp(a: LeanSym): LeanSym {
  if (a.kind === "int") {
    if (a.n === Z0) return { kind: "int", n: Z1 };
    if (a.n === Z1) return { kind: "e" };
    return { kind: "exp", a };
  }
  if (a.kind === "ipi") {
    return { kind: "int", n: a.k % Z2 === Z0 ? Z1 : ZM1 };
  }
  if (a.kind === "ln") {
    return lnInvOk(a.a) ? a.a : { kind: "exp", a };
  }
  if ((a.kind === "sub" || a.kind === "add") && a.b.kind === "ipi") {
    // exp(a ± kiπ) = ±exp a
    const r = rExp(a.a);
    return a.b.k % Z2 === Z0 ? r : negOf(r);
  }
  return { kind: "exp", a };
}

function rSub(a: LeanSym, b: LeanSym): LeanSym {
  // Exact same rule order as `Eml.Cert.subRules`.
  if (b.kind === "int" && b.n === Z0) return a;
  if (a.kind === "int" && a.n === Z0) return negOf(b);
  if (symEq(a, b)) return { kind: "int", n: Z0 };
  if (a.kind === "int" && b.kind === "int") return { kind: "int", n: a.n - b.n };
  if (a.kind === "ipi" && b.kind === "ipi") {
    const d = a.k - b.k;
    return d === Z0 ? { kind: "int", n: Z0 } : { kind: "ipi", k: d };
  }
  if (b.kind === "sub" && symEq(a, b.a)) return b.b;
  if (a.kind === "add" && symEq(a.a, b)) return a.b;
  if (a.kind === "add" && symEq(a.b, b)) return a.a;
  if (b.kind === "neg") return { kind: "add", a, b: b.a };
  if (a.kind === "sub" && a.b.kind === "int" && b.kind === "int") {
    const t = a.b.n + b.n;
    return t === Z0 ? a.a : { kind: "sub", a: a.a, b: { kind: "int", n: t } };
  }
  if (a.kind === "sub" && symEq(a.a, b)) return negOf(a.b);
  // r14 / r15: keep iπ multiples outermost.
  if (b.kind === "sub" && b.b.kind === "ipi") return { kind: "add", a: { kind: "sub", a, b: b.a }, b: b.b };
  if (a.kind === "sub" && a.b.kind === "ipi") return { kind: "sub", a: { kind: "sub", a: a.a, b }, b: a.b };
  return { kind: "sub", a, b };
}

function inStrip(u: LeanSym): boolean {
  if (cls(u) >= 1) return true;
  if (u.kind === "ipi" && u.k >= ZM1 && u.k < Z1) return true;
  return boxStrip(u);
}

/** `ln a` with no structural rule: `ln(−a) − iπ` on the negative real axis (Cert.lean lnRest). */
function lnRest(a: LeanSym): LeanSym {
  return boxNeg(a) ? rSub({ kind: "ln", a: negOf(a) }, { kind: "ipi", k: Z1 }) : { kind: "ln", a };
}

function rLn(a: LeanSym): LeanSym | null {
  if (a.kind === "int") {
    if (a.n === Z1) return { kind: "int", n: Z0 };
    if (a.n === Z0) return null;
    if (a.n === ZM1) return { kind: "ipi", k: ZM1 };
    return lnRest(a);
  }
  if (a.kind === "e") return { kind: "int", n: Z1 };
  if (a.kind === "neg") {
    if (cls(a.a) === 2 || boxPos(a.a)) {
      const inner = rLn(a.a);
      return inner ? rSub(inner, { kind: "ipi", k: Z1 }) : null;
    }
    return { kind: "ln", a };
  }
  if (a.kind === "exp") {
    return inStrip(a.a) ? a.a : { kind: "ln", a };
  }
  return lnRest(a);
}

function gate(a: LeanSym, b: LeanSym): LeanSym | null {
  if (!nz(b)) return null;
  const l = rLn(b);
  if (!l) return null;
  return rSub(rExp(a), l);
}

export function formatLeanSymTerm(s: LeanSym, parens = false): string {
  const wrap = (inner: string) => (parens ? `(${inner})` : inner);
  switch (s.kind) {
    case "int":
      return wrap(`Sym.int ${s.n < Z0 ? `(${s.n})` : s.n}`);
    case "e":
      return "Sym.e";
    case "ipi":
      return wrap(`Sym.ipi ${s.k < Z0 ? `(${s.k})` : s.k}`);
    case "exp":
      return wrap(`Sym.exp ${formatLeanSymTerm(s.a, true)}`);
    case "ln":
      return wrap(`Sym.ln ${formatLeanSymTerm(s.a, true)}`);
    case "neg":
      return wrap(`Sym.neg ${formatLeanSymTerm(s.a, true)}`);
    case "add":
      return wrap(`Sym.add ${formatLeanSymTerm(s.a, true)} ${formatLeanSymTerm(s.b, true)}`);
    case "sub":
      return wrap(`Sym.sub ${formatLeanSymTerm(s.a, true)} ${formatLeanSymTerm(s.b, true)}`);
  }
}

export function formatLeanSymDisplay(s: LeanSym): string {
  switch (s.kind) {
    case "int":
      return s.n < Z0 ? `−${-s.n}` : String(s.n);
    case "e":
      return "e";
    case "ipi":
      if (s.k === Z0) return "0";
      if (s.k === Z1) return "iπ";
      if (s.k === ZM1) return "−iπ";
      return `${s.k < Z0 ? `−${-s.k}` : s.k}iπ`;
    case "exp":
      return `exp(${formatLeanSymDisplay(s.a)})`;
    case "ln":
      return `ln(${formatLeanSymDisplay(s.a)})`;
    case "neg": {
      const inner = formatLeanSymDisplay(s.a);
      return s.a.kind === "add" || s.a.kind === "sub" ? `−(${inner})` : `−${inner}`;
    }
    case "add":
      return `${formatLeanSymDisplay(s.a)} + ${formatLeanSymDisplay(s.b)}`;
    case "sub": {
      const right = formatLeanSymDisplay(s.b);
      const wrap = s.b.kind === "add" || s.b.kind === "sub";
      return `${formatLeanSymDisplay(s.a)} − ${wrap ? `(${right})` : right}`;
    }
  }
}

export function rpnToLeanBits(rpn: string): string {
  const items = rpn.split("").map((ch) => (ch === "1" ? "true" : "false"));
  return `[${items.join(", ")}]`;
}

/**
 * Run the exact mirror of `Eml.Cert.certify` on a pure RPN or binary program.
 * Returns `null` if the program is invalid or not certifiable without `ln 0`.
 */
export function certifyRpnForLean(program: string, maxLen = 201): LeanCert | null {
  const trimmed = program.trim();
  if (!trimmed || trimmed.length > maxLen) return null;
  const rpn = /^[01]+$/.test(trimmed) ? binaryToRpn(trimmed) : trimmed;
  if (!/^[1E]+$/.test(rpn) || !isProgram(rpn)) return null;

  const stack: Array<LeanSym | null> = [];
  for (let i = 0; i < rpn.length; i += 1) {
    if (rpn[i] === "1") {
      stack.push({ kind: "int", n: Z1 });
    } else {
      if (stack.length < 2) return null;
      const b = stack.pop()!;
      const a = stack.pop()!;
      stack.push(a && b ? gate(a, b) : null);
    }
  }
  if (stack.length !== 1 || !stack[0]) return null;
  const sym = stack[0];
  return {
    rpn,
    sym,
    leanSym: formatLeanSymTerm(sym, false),
    display: formatLeanSymDisplay(sym),
  };
}

// ---- EmlExt certificates (formal/lean/Eml/CertExt.lean): ln 0 = −∞ ----

export type LeanXSym = { kind: "fin"; s: LeanSym } | { kind: "posInf" } | { kind: "negInf" };

export type LeanExtCert = {
  rpn: string;
  xsym: LeanXSym;
  /** Lean term of type `Eml.Cert.XSym`, e.g. `XSym.negInf` or `XSym.fin (Sym.int (-1))`. */
  leanXSym: string;
  display: string;
};

function xExp(a: LeanXSym): LeanXSym {
  if (a.kind === "fin") return { kind: "fin", s: rExp(a.s) };
  if (a.kind === "posInf") return a;
  return { kind: "fin", s: { kind: "int", n: Z0 } };
}

function xLn(b: LeanXSym): LeanXSym | null {
  if (b.kind === "fin") {
    if (b.s.kind === "int" && b.s.n === Z0) return { kind: "negInf" };
    if (!nz(b.s)) return null;
    const l = rLn(b.s);
    return l ? { kind: "fin", s: l } : null;
  }
  if (b.kind === "posInf") return b;
  return null;
}

function xSub(a: LeanXSym, b: LeanXSym): LeanXSym | null {
  if (a.kind === "fin") {
    if (b.kind === "fin") return { kind: "fin", s: rSub(a.s, b.s) };
    return { kind: b.kind === "negInf" ? "posInf" : "negInf" };
  }
  if (b.kind === "fin") return a;
  if (a.kind === "posInf" && b.kind === "negInf") return a;
  if (a.kind === "negInf" && b.kind === "posInf") return a;
  return null;
}

function xGate(a: LeanXSym, b: LeanXSym): LeanXSym | null {
  const l = xLn(b);
  return l ? xSub(xExp(a), l) : null;
}

export function formatLeanXSymTerm(x: LeanXSym): string {
  if (x.kind === "posInf") return "XSym.posInf";
  if (x.kind === "negInf") return "XSym.negInf";
  return `XSym.fin ${formatLeanSymTerm(x.s, true)}`;
}

export function formatLeanXSymDisplay(x: LeanXSym): string {
  if (x.kind === "posInf") return "+∞";
  if (x.kind === "negInf") return "−∞";
  return formatLeanSymDisplay(x.s);
}

/**
 * Run the exact mirror of `Eml.Cert.certifyExt` (EmlExt, `ln 0 = −∞`) on a pure
 * RPN or binary program. Returns `null` if the program is invalid or not
 * certifiable. Agrees with `certifyRpnForLean` whenever that succeeds.
 */
export function certifyRpnForLeanExt(program: string, maxLen = 201): LeanExtCert | null {
  const trimmed = program.trim();
  if (!trimmed || trimmed.length > maxLen) return null;
  const rpn = /^[01]+$/.test(trimmed) ? binaryToRpn(trimmed) : trimmed;
  if (!/^[1E]+$/.test(rpn) || !isProgram(rpn)) return null;

  const stack: Array<LeanXSym | null> = [];
  for (let i = 0; i < rpn.length; i += 1) {
    if (rpn[i] === "1") {
      stack.push({ kind: "fin", s: { kind: "int", n: Z1 } });
    } else {
      if (stack.length < 2) return null;
      const b = stack.pop()!;
      const a = stack.pop()!;
      stack.push(a && b ? xGate(a, b) : null);
    }
  }
  if (stack.length !== 1 || !stack[0]) return null;
  const xsym = stack[0];
  return { rpn, xsym, leanXSym: formatLeanXSymTerm(xsym), display: formatLeanXSymDisplay(xsym) };
}

