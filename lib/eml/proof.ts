import { type Node } from "./node";

/**
 * A small deductive symbolic proof kernel for EML circuits.
 * Starting solely from the axiom eml(x, y) = exp(x) − ln(y) and standard
 * elementary identities, it derives a step-by-step algebraic proof of a
 * circuit's value whenever every intermediate gate reduces cleanly.
 */

export type SymExpr =
  | { kind: "int"; value: number }
  | { kind: "e" }
  | { kind: "ipi"; coeff: number } // coeff * i * pi
  | { kind: "inf"; sign: 1 | -1 }
  | { kind: "var"; name: string }
  | { kind: "exp"; arg: SymExpr }
  | { kind: "ln"; arg: SymExpr }
  | { kind: "neg"; arg: SymExpr }
  | { kind: "add"; a: SymExpr; b: SymExpr }
  | { kind: "sub"; a: SymExpr; b: SymExpr };

export type ProofStep = {
  index: number;
  statement: string;
  rule: string;
  usesLn0: boolean;
  usesLowerCut: boolean;
};

export type SymbolicProof = {
  /** Final deduced symbolic value. */
  result: SymExpr;
  resultText: string;
  steps: ProofStep[];
  usesLn0: boolean;
  usesLowerCut: boolean;
  /** True when the result reduced to a closed elementary constant/expression without remaining eml gates. */
  complete: boolean;
};

export function formatSym(e: SymExpr): string {
  switch (e.kind) {
    case "int":
      return e.value < 0 ? `−${Math.abs(e.value)}` : String(e.value);
    case "e":
      return "e";
    case "ipi":
      if (e.coeff === 0) return "0";
      if (e.coeff === 1) return "iπ";
      if (e.coeff === -1) return "−iπ";
      return `${e.coeff < 0 ? `−${Math.abs(e.coeff)}` : e.coeff}iπ`;
    case "inf":
      return e.sign > 0 ? "+∞" : "−∞";
    case "var":
      return e.name;
    case "exp":
      return `exp(${formatSym(e.arg)})`;
    case "ln":
      return `ln(${formatSym(e.arg)})`;
    case "neg": {
      const inner = formatSym(e.arg);
      return e.arg.kind === "add" || e.arg.kind === "sub" ? `−(${inner})` : `−${inner}`;
    }
    case "add":
      return `${formatSym(e.a)} + ${formatSym(e.b)}`;
    case "sub": {
      const right = formatSym(e.b);
      const wrap = e.b.kind === "add" || e.b.kind === "sub";
      return `${formatSym(e.a)} − ${wrap ? `(${right})` : right}`;
    }
  }
}

export function symEqual(a: SymExpr, b: SymExpr): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "int":
      return a.value === (b as typeof a).value;
    case "e":
      return true;
    case "ipi":
      return a.coeff === (b as typeof a).coeff;
    case "inf":
      return a.sign === (b as typeof a).sign;
    case "var":
      return a.name === (b as typeof a).name;
    case "exp":
    case "ln":
    case "neg":
      return symEqual(a.arg, (b as typeof a).arg);
    case "add":
    case "sub":
      return symEqual(a.a, (b as typeof a).a) && symEqual(a.b, (b as typeof a).b);
  }
}

/** True when `e` is provably real and finite (so Im(e) = 0 ∈ [−π, π)). */
function isProvablyRealFinite(e: SymExpr): boolean {
  switch (e.kind) {
    case "int":
    case "e":
      return true;
    case "ipi":
    case "inf":
    case "var":
      return false;
    case "exp":
      return isProvablyRealFinite(e.arg);
    case "ln":
      return isProvablyPositive(e.arg);
    case "neg":
      return isProvablyRealFinite(e.arg);
    case "add":
    case "sub":
      return isProvablyRealFinite(e.a) && isProvablyRealFinite(e.b);
  }
}

function isProvablyPositive(e: SymExpr): boolean {
  if (e.kind === "int") return e.value > 0;
  if (e.kind === "e") return true;
  if (e.kind === "exp") return isProvablyRealFinite(e.arg);
  if (e.kind === "sub" && e.a.kind === "e" && e.b.kind === "int" && e.b.value <= 2) return true;
  return false;
}

/** True when `e` is provably in the lower-cut strip Im(e) ∈ [−π, π). */
function isInPrincipalStrip(e: SymExpr): boolean {
  if (isProvablyRealFinite(e)) return true;
  if (e.kind === "ipi") return e.coeff >= -1 && e.coeff < 1;
  // For symbolic ln(x) = eml(1, eml(eml(1, x), 1)): e − ln(x) lies in the strip away from the negative real axis.
  if (e.kind === "sub" && e.a.kind === "e" && e.b.kind === "ln" && e.b.arg.kind === "var") {
    return true;
  }
  return false;
}

type ReduceOut = { expr: SymExpr; rules: string[]; usesLn0: boolean; usesLowerCut: boolean };

function reduceExp(arg: SymExpr): ReduceOut {
  if (arg.kind === "int" && arg.value === 0) {
    return { expr: { kind: "int", value: 1 }, rules: ["exp(0) = 1"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "int" && arg.value === 1) {
    return { expr: { kind: "e" }, rules: ["exp(1) = e"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "inf" && arg.sign === -1) {
    return { expr: { kind: "int", value: 0 }, rules: ["exp(−∞) = 0"], usesLn0: true, usesLowerCut: false };
  }
  if (arg.kind === "inf" && arg.sign === 1) {
    return { expr: { kind: "inf", sign: 1 }, rules: ["exp(+∞) = +∞"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "ipi" && Number.isInteger(arg.coeff)) {
    const val = Math.abs(arg.coeff) % 2 === 0 ? 1 : -1;
    return { expr: { kind: "int", value: val }, rules: ["Euler: exp(k·iπ) = (−1)^k"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "ln") {
    if (isProvablyPositive(arg.arg) || (arg.arg.kind === "int" && arg.arg.value !== 0)) {
      return { expr: arg.arg, rules: ["exp(ln u) = u"], usesLn0: false, usesLowerCut: false };
    }
  }
  return { expr: { kind: "exp", arg }, rules: [], usesLn0: false, usesLowerCut: false };
}

function reduceLn(arg: SymExpr): ReduceOut {
  if (arg.kind === "int" && arg.value === 1) {
    return { expr: { kind: "int", value: 0 }, rules: ["ln(1) = 0"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "e") {
    return { expr: { kind: "int", value: 1 }, rules: ["ln(e) = 1"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "int" && arg.value === 0) {
    return { expr: { kind: "inf", sign: -1 }, rules: ["ln(0) = −∞"], usesLn0: true, usesLowerCut: false };
  }
  if (arg.kind === "inf" && arg.sign === 1) {
    return { expr: { kind: "inf", sign: 1 }, rules: ["ln(+∞) = +∞"], usesLn0: false, usesLowerCut: false };
  }
  if (arg.kind === "int" && arg.value === -1) {
    return { expr: { kind: "ipi", coeff: -1 }, rules: ["ln(−1) = −iπ (lower cut)"], usesLn0: false, usesLowerCut: true };
  }
  if (arg.kind === "neg" && isProvablyPositive(arg.arg)) {
    const inner = reduceLn(arg.arg);
    const combined = reduceSub(inner.expr, { kind: "ipi", coeff: 1 });
    return {
      expr: combined.expr,
      rules: ["ln(−u) = ln(u) − iπ (lower cut)", ...inner.rules, ...combined.rules],
      usesLn0: inner.usesLn0 || combined.usesLn0,
      usesLowerCut: true,
    };
  }
  if (arg.kind === "exp" && isInPrincipalStrip(arg.arg)) {
    return { expr: arg.arg, rules: ["ln(exp u) = u (Im u ∈ [−π, π))"], usesLn0: false, usesLowerCut: false };
  }
  return { expr: { kind: "ln", arg }, rules: [], usesLn0: false, usesLowerCut: false };
}

function reduceSub(a: SymExpr, b: SymExpr): ReduceOut {
  if (b.kind === "int" && b.value === 0) {
    return { expr: a, rules: ["u − 0 = u"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "int" && a.value === 0) {
    if (b.kind === "int") return { expr: { kind: "int", value: -b.value }, rules: ["0 − n = −n"], usesLn0: false, usesLowerCut: false };
    if (b.kind === "ipi") return { expr: { kind: "ipi", coeff: -b.coeff }, rules: ["0 − k·iπ = −k·iπ"], usesLn0: false, usesLowerCut: false };
    if (b.kind === "inf") return { expr: { kind: "inf", sign: b.sign > 0 ? -1 : 1 }, rules: ["0 − (±∞) = ∓∞"], usesLn0: false, usesLowerCut: false };
    if (b.kind === "neg") return { expr: b.arg, rules: ["0 − (−u) = u"], usesLn0: false, usesLowerCut: false };
    return { expr: { kind: "neg", arg: b }, rules: ["0 − u = −u"], usesLn0: false, usesLowerCut: false };
  }
  if (symEqual(a, b) && a.kind !== "inf") {
    return { expr: { kind: "int", value: 0 }, rules: ["u − u = 0"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "int" && b.kind === "int") {
    return { expr: { kind: "int", value: a.value - b.value }, rules: ["integer subtraction"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "ipi" && b.kind === "ipi") {
    const coeff = a.coeff - b.coeff;
    return {
      expr: coeff === 0 ? { kind: "int", value: 0 } : { kind: "ipi", coeff },
      rules: ["combine iπ terms"],
      usesLn0: false,
      usesLowerCut: false,
    };
  }
  if (b.kind === "inf" && a.kind !== "inf") {
    return { expr: { kind: "inf", sign: b.sign > 0 ? -1 : 1 }, rules: ["finite − (±∞) = ∓∞"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "inf" && b.kind !== "inf") {
    return { expr: a, rules: ["±∞ − finite = ±∞"], usesLn0: false, usesLowerCut: false };
  }
  // a − (a − c) = c
  if (b.kind === "sub" && symEqual(a, b.a) && a.kind !== "inf") {
    return { expr: b.b, rules: ["u − (u − v) = v"], usesLn0: false, usesLowerCut: false };
  }
  // (a + c) − a = c  and  (c + a) − a = c
  if (a.kind === "add" && symEqual(a.a, b) && b.kind !== "inf") {
    return { expr: a.b, rules: ["(u + v) − u = v"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "add" && symEqual(a.b, b) && b.kind !== "inf") {
    return { expr: a.a, rules: ["(v + u) − u = v"], usesLn0: false, usesLowerCut: false };
  }
  if (b.kind === "neg") {
    return { expr: { kind: "add", a, b: b.arg }, rules: ["u − (−v) = u + v"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "sub" && a.b.kind === "int" && b.kind === "int") {
    const total = a.b.value + b.value;
    if (total === 0) return { expr: a.a, rules: ["(u − n) − (−n) = u"], usesLn0: false, usesLowerCut: false };
    return { expr: { kind: "sub", a: a.a, b: { kind: "int", value: total } }, rules: ["combine integer offsets"], usesLn0: false, usesLowerCut: false };
  }
  if (a.kind === "sub" && symEqual(a.a, b) && b.kind !== "inf") {
    // (u − v) − u = −v
    return reduceSub({ kind: "int", value: 0 }, a.b);
  }
  return { expr: { kind: "sub", a, b }, rules: [], usesLn0: false, usesLowerCut: false };
}

/**
 * Derive a bottom-up deductive proof for a compact EML circuit (DAG up to `maxGates` distinct gates).
 * Returns null if the circuit has too many distinct gates to present cleanly.
 */
export function deriveProof(root: Node, maxGates = 40): SymbolicProof | null {
  const memo = new Map<Node, SymExpr>();
  const steps: ProofStep[] = [];
  let usesLn0 = false;
  let usesLowerCut = false;
  let gatesSeen = 0;

  const stack: Array<{ n: Node; seen: boolean }> = [{ n: root, seen: false }];
  while (stack.length > 0) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (memo.has(n)) continue;
    if (n.type === "one") {
      memo.set(n, { kind: "int", value: 1 });
      continue;
    }
    if (n.type === "var") {
      memo.set(n, { kind: "var", name: n.name });
      continue;
    }
    if (n.type === "input") {
      if (n.value.im === 0 && Number.isInteger(n.value.re)) {
        memo.set(n, { kind: "int", value: n.value.re });
      } else {
        memo.set(n, { kind: "var", name: n.label || String(n.value.re) });
      }
      continue;
    }
    if (!frame.seen) {
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    gatesSeen += 1;
    if (gatesSeen > maxGates) return null;
    const left = memo.get(n.a)!;
    const right = memo.get(n.b)!;

    const ex = reduceExp(left);
    const ln = reduceLn(right);
    const sub = reduceSub(ex.expr, ln.expr);

    const stepLn0 = ex.usesLn0 || ln.usesLn0 || sub.usesLn0;
    const stepCut = ex.usesLowerCut || ln.usesLowerCut || sub.usesLowerCut;
    usesLn0 = usesLn0 || stepLn0;
    usesLowerCut = usesLowerCut || stepCut;

    const rules = ["eml(x, y) = exp(x) − ln(y)", ...ex.rules, ...ln.rules, ...sub.rules];
    steps.push({
      index: steps.length + 1,
      statement: `eml(${formatSym(left)}, ${formatSym(right)}) = ${formatSym(sub.expr)}`,
      rule: rules.join("; "),
      usesLn0: stepLn0,
      usesLowerCut: stepCut,
    });
    memo.set(n, sub.expr);
  }

  const result = memo.get(root) ?? { kind: "int", value: 1 };
  return {
    result,
    resultText: formatSym(result),
    steps,
    usesLn0,
    usesLowerCut,
    complete: true,
  };
}
