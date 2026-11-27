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

function nz(s: LeanSym): boolean {
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
      return nz(s.a);
    case "add":
      return false;
    case "sub":
      return eSubSmall(s.a, s.b);
  }
}

function lnInvOk(u: LeanSym): boolean {
  return cls(u) === 2 || (u.kind === "int" && u.n !== Z0);
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
  return { kind: "exp", a };
}

function negOf(v: LeanSym): LeanSym {
  if (v.kind === "int") return { kind: "int", n: -v.n };
  if (v.kind === "ipi") return { kind: "ipi", k: -v.k };
  if (v.kind === "neg") return v.a;
  return { kind: "neg", a: v };
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
  return { kind: "sub", a, b };
}

function inStrip(u: LeanSym): boolean {
  if (cls(u) >= 1) return true;
  return u.kind === "ipi" && u.k >= ZM1 && u.k < Z1;
}

function rLn(a: LeanSym): LeanSym | null {
  if (a.kind === "int") {
    if (a.n === Z1) return { kind: "int", n: Z0 };
    if (a.n === Z0) return null;
    if (a.n === ZM1) return { kind: "ipi", k: ZM1 };
    return { kind: "ln", a };
  }
  if (a.kind === "e") return { kind: "int", n: Z1 };
  if (a.kind === "neg") {
    if (cls(a.a) === 2) {
      const inner = rLn(a.a);
      return inner ? rSub(inner, { kind: "ipi", k: Z1 }) : null;
    }
    return { kind: "ln", a };
  }
  if (a.kind === "exp") {
    return inStrip(a.a) ? a.a : { kind: "ln", a };
  }
  return { kind: "ln", a };
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
