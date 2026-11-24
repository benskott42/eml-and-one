import {
  type C,
  c,
  cadd,
  ccos,
  cdiv,
  cexp,
  clogPrincipal,
  cmul,
  cneg,
  cpow,
  csin,
  cacos,
  cacosh,
  casin,
  casinh,
  catan,
  catanh,
  ccosh,
  csinh,
  cavg,
  csub,
  ctan,
  ctanh,
  chypot,
} from "./complex";
import {
  builtHugeAngle,
  tAvg,
  tDiv,
  tE,
  tHypot,
  tI,
  tLn,
  tLogBase,
  tMul,
  tNeg,
  tPi,
  tPow,
  tSqrt,
  literalNode,
  userAdd,
  userSub,
  unaryBuilders,
} from "./library";
import { mayBeInfinite } from "./lowering";
import { formatC, isUsable } from "./format";
import { EmlError, input, isExactUnsure, isUnverified, isolateCircuit, markExactUnsure, markUnverified, precisionNoteOf, type Node } from "./node";

/** Short names for the same unary program. log is unary ln, and binary log below. */
const UNARY_ALIAS: Record<string, string> = {
  sq: "sqr",
  asin: "arcsin",
  acos: "arccos",
  atan: "arctan",
  asinh: "arsinh",
  acosh: "arcosh",
  atanh: "artanh",
  sigmoid: "sigma",
};

const UNARY: Record<string, (t: Node) => Node> = { ...unaryBuilders, log: tLn };
for (const [alias, canon] of Object.entries(UNARY_ALIAS)) {
  const build = unaryBuilders[canon];
  if (build) UNARY[alias] = build;
}

const binaryCalls = {
  hypot: { node: tHypot, ref: chypot },
  avg: { node: tAvg, ref: cavg },
  pow: { node: tPow, ref: cpow },
  log: {
    node: tLogBase,
    ref: (base: C, value: C) => cdiv(clogPrincipal(value), clogPrincipal(base)),
  },
};

const BINARY_CALL: Record<string, (a: Node, b: Node) => Node> = Object.fromEntries(
  Object.entries(binaryCalls).map(([name, pair]) => [name, pair.node]),
);

/** π is its own token: πi is pi i, and 2πi says to put * after 2, as 2 pi i does. */
function preprocess(source: string): string {
  return source
    .replace(/π/g, " pi ")
    .replace(/×/g, "*")
    .replace(/÷/g, "/")
    .replace(/−/g, "-");
}

type Tok =
  | { k: "num"; text: string }
  | { k: "id"; text: string }
  | { k: "op"; text: string };

function tokenize(source: string): Tok[] {
  const s = preprocess(source);
  const tokens: Tok[] = [];
  let i = 0;
  while (i < s.length) {
    const ch = s[i];
    if (ch === " " || ch === "\t" || ch === "\n" || ch === "\r") {
      i += 1;
      continue;
    }
    if (/[0-9.]/.test(ch)) {
      const start = i;
      if (ch === "." && !/[0-9]/.test(s[i + 1] ?? "")) {
        throw new EmlError("A decimal point needs digits.");
      }
      i += 1;
      while (i < s.length && /[0-9.]/.test(s[i])) i += 1;
      if (s[i] === "e" || s[i] === "E") {
        i += 1;
        if (s[i] === "+" || s[i] === "-") i += 1;
        const expStart = i;
        while (i < s.length && /[0-9]/.test(s[i])) i += 1;
        if (i === expStart) throw new EmlError("The exponent needs digits.");
      }
      tokens.push({ k: "num", text: s.slice(start, i) });
      continue;
    }
    if (/[A-Za-z]/.test(ch)) {
      const start = i;
      i += 1;
      while (i < s.length && /[A-Za-z0-9]/.test(s[i])) i += 1;
      tokens.push({ k: "id", text: s.slice(start, i) });
      continue;
    }
    if ("+-*/^(),√".includes(ch)) {
      if (ch === "*" && s[i + 1] === "*") {
        tokens.push({ k: "op", text: "^" });
        i += 2;
        continue;
      }
      tokens.push({ k: "op", text: ch });
      i += 1;
      continue;
    }
    throw new EmlError(`Cannot read “${ch}” in the expression.`);
  }
  return tokens;
}

type Out =
  | { k: "num"; text: string }
  | { k: "const"; name: "pi" | "e" | "i" }
  | { k: "var"; name: string }
  | { k: "op"; name: "+" | "-" | "*" | "/" | "^" | "neg" | "sqrt" }
  | { k: "call"; name: string; argc: number };

type Mark =
  | { k: "bin"; name: "+" | "-" | "*" | "/" | "^"; prec: number; right: boolean }
  | { k: "pre"; name: "neg" | "sqrt"; prec: number }
  | { k: "lp"; argc: number; call: string | null };

const PREC: Record<string, number> = { "+": 1, "-": 1, "*": 2, "/": 2, neg: 3, "^": 4, sqrt: 5 };

function knownCall(name: string): boolean {
  return Object.hasOwn(UNARY, name) || Object.hasOwn(BINARY_CALL, name);
}

function popUntil(ops: Mark[], out: Out[], untilLowerThan: number, right: boolean): void {
  while (ops.length) {
    const top = ops[ops.length - 1];
    if (!top || top.k === "lp") break;
    const prec = top.prec;
    if (prec < untilLowerThan || (right && prec === untilLowerThan)) break;
    ops.pop();
    if (top.k === "pre") out.push({ k: "op", name: top.name });
    else out.push({ k: "op", name: top.name });
  }
}

/**
 * Iterative Pratt/shunting-yard. Nested parentheses and long sums do not use
 * the JavaScript stack, so 10,000 parentheses and 20,000 additions parse.
 *
 * Unary minus binds looser than power, so −2^2 is −(2^2) and 2^−2 is 2^(−2).
 * √ binds to the next atom, so √2^2 is (√2)^2.
 */
/** Two values side by side, such as 2pi or 2(3). Multiplication is written with *. */
function missingTimes(tokens: Tok[], i: number): EmlError {
  const prev = tokens[i - 1]?.text;
  const next = tokens[i]?.text;
  if (!prev || !next) return new EmlError("The expression has an extra symbol.");
  return new EmlError(`Put * between “${prev}” and “${next}”.`);
}

/** An operator where a value belongs, as the second ^ in 2^^3. */
function missingValue(tokens: Tok[], i: number): EmlError {
  const op = tokens[i]?.text;
  return new EmlError(op ? `A value is missing before “${op}”.` : "The expression ended early.");
}

function toRpn(tokens: Tok[]): Out[] {
  if (tokens.length === 0) throw new EmlError("Enter an expression.");
  const out: Out[] = [];
  const ops: Mark[] = [];
  let wantValue = true;
  for (let i = 0; i < tokens.length; i += 1) {
    const tok = tokens[i];
    if (!tok) break;
    if (tok.k === "num") {
      if (!wantValue) throw missingTimes(tokens, i);
      out.push({ k: "num", text: tok.text });
      wantValue = false;
      continue;
    }
    if (tok.k === "id") {
      const name = tok.text.toLowerCase();
      if (!wantValue && name === "i") {
        popUntil(ops, out, PREC["*"] ?? 2, false);
        ops.push({ k: "bin", name: "*", prec: PREC["*"] ?? 2, right: false });
        out.push({ k: "const", name: "i" });
        wantValue = false;
        continue;
      }
      if (!wantValue) throw missingTimes(tokens, i);
      const next = tokens[i + 1];
      if (next?.k === "op" && next.text === "(") {
        i += 1;
        ops.push({ k: "lp", argc: 0, call: name });
        wantValue = true;
        continue;
      }
      if (name === "inf" || name === "infinity") {
        if (!wantValue) throw new EmlError("The expression has an extra symbol.");
        out.push({ k: "num", text: "inf" });
        wantValue = false;
        continue;
      }
      if (name === "pi" || name === "e" || name === "i") out.push({ k: "const", name });
      else if (name === "x" || name === "y") out.push({ k: "var", name });
      else if (knownCall(name)) throw new EmlError(`Write ${name} with parentheses, as ${name}(1).`);
      else throw new EmlError(`Unknown name “${tok.text}”. Use x, y, pi, e, i, or inf.`);
      wantValue = false;
      continue;
    }
    const text = tok.text;
    if (text === "(") {
      if (!wantValue) throw missingTimes(tokens, i);
      ops.push({ k: "lp", argc: 0, call: null });
      wantValue = true;
      continue;
    }
    if (text === ")") {
      let found = false;
      while (ops.length) {
        const top = ops.pop();
        if (!top) break;
        if (top.k === "lp") {
          if (wantValue && top.argc === 0 && out.length === 0) throw new EmlError("The expression ended early.");
          if (wantValue && top.call && top.argc === 0) {
            out.push({ k: "call", name: top.call, argc: 0 });
          } else if (top.call) {
            if (wantValue) throw new EmlError(`Missing ) after ${top.call}.`);
            out.push({ k: "call", name: top.call, argc: top.argc + 1 });
          } else if (wantValue) {
            throw new EmlError("The expression ended early.");
          }
          found = true;
          wantValue = false;
          break;
        }
        out.push({ k: "op", name: top.k === "pre" ? top.name : top.name });
      }
      if (!found) throw new EmlError("Missing ).");
      continue;
    }
    if (text === ",") {
      let found = false;
      while (ops.length) {
        const top = ops[ops.length - 1];
        if (!top) break;
        if (top.k === "lp") {
          if (!top.call) throw new EmlError("The expression has an unexpected symbol.");
          if (wantValue) throw new EmlError("The expression ended early.");
          top.argc += 1;
          found = true;
          wantValue = true;
          break;
        }
        ops.pop();
        out.push({ k: "op", name: top.k === "pre" ? top.name : top.name });
      }
      if (!found) throw new EmlError("The expression has an unexpected symbol.");
      continue;
    }
    if (text === "√" || ((text === "-" || text === "+") && wantValue)) {
      if (text === "+") continue;
      const name = text === "√" ? "sqrt" : "neg";
      ops.push({ k: "pre", name, prec: PREC[name] ?? 4 });
      wantValue = true;
      continue;
    }
    if (text === "+" || text === "-" || text === "*" || text === "/" || text === "^") {
      if (wantValue) throw missingValue(tokens, i);
      const right = text === "^";
      popUntil(ops, out, PREC[text] ?? 1, right);
      ops.push({ k: "bin", name: text, prec: PREC[text] ?? 1, right });
      wantValue = true;
      continue;
    }
    throw new EmlError("The expression has an unexpected symbol.");
  }
  if (wantValue) throw new EmlError("The expression ended early.");
  while (ops.length) {
    const top = ops.pop();
    if (!top || top.k === "lp") throw new EmlError("Missing ).");
    out.push({ k: "op", name: top.k === "pre" ? top.name : top.name });
  }
  return out;
}

function assertCall(name: string, count: number): void {
  if (!knownCall(name)) throw new EmlError(`Unknown function “${name}”.`);
  const ok = (count === 1 && Object.hasOwn(UNARY, name)) || (count === 2 && Object.hasOwn(BINARY_CALL, name));
  if (!ok) throw new EmlError(`${name} does not take ${count} argument${count === 1 ? "" : "s"}.`);
}

function applyNode(name: string, args: Node[]): Node {
  assertCall(name, args.length);
  const first = args[0];
  const second = args[1];
  const unary = UNARY[name];
  if (args.length === 1 && unary && first) return unary(first);
  const binary = BINARY_CALL[name];
  if (binary && first && second) return binary(first, second);
  throw new EmlError(`${name} does not take ${args.length} argument${args.length === 1 ? "" : "s"}.`);
}

type Ast =
  | { k: "n"; node: Node }
  | { k: "+"; args: Ast[] }
  | { k: "*"; args: Ast[] }
  | { k: "bin"; name: "-" | "/" | "^"; args: [Ast, Ast] }
  | { k: "pre"; name: "neg" | "sqrt"; arg: Ast }
  | { k: "call"; name: string; args: Ast[] };

function balanced(op: "+" | "*", nodes: Node[]): Node {
  if (nodes.length === 1) {
    const only = nodes[0];
    if (!only) throw new EmlError("The expression ended early.");
    return only;
  }
  const mid = Math.floor(nodes.length / 2);
  const left = balanced(op, nodes.slice(0, mid));
  const right = balanced(op, nodes.slice(mid));
  return op === "+" ? userAdd(left, right) : tMul(left, right);
}

/** True when a sum contains the negation of another sum or difference. Iterative: a sum of many terms is a deep spine. */
function holdsNegatedGroup(root: Ast): boolean {
  const stack: Ast[] = [root];
  const seen = new Set<Ast>();
  while (stack.length) {
    const ast = stack.pop();
    if (!ast || seen.has(ast)) continue;
    seen.add(ast);
    if (ast.k === "pre" && ast.name === "neg") {
      if (ast.arg.k === "+" || (ast.arg.k === "bin" && ast.arg.name === "-")) return true;
      continue;
    }
    if (ast.k === "+") for (const child of ast.args) stack.push(child);
  }
  return false;
}

let taintCount = 0;

/**
 * A refused operand refuses every result built on it. The library's folds read a
 * refused leaf as its placeholder 0: 1 + (10^400 + π) is refused, and minus 2 it
 * folded to a certified −2. A circuit still built on the operand is exact-unsure,
 * so float mode keeps its own reading. A fold that dropped the operand becomes a
 * fresh refused leaf, so a shared node such as 0 is not marked.
 */
function refuseFrom(args: Node[], out: Node): Node {
  // An infinite operand is the library's own refusal path: (1 + ∞) − ∞ stays ∞ − ∞.
  const refused = args.filter((arg) => isUnverified(arg) && !mayBeInfinite(arg));
  if (!refused.length || isUnverified(out) || isExactUnsure(out)) return out;
  if (refused.some((arg) => builtOn(out, arg))) return markExactUnsure(out);
  taintCount += 1;
  return markUnverified(input({ re: Number.NaN, im: Number.NaN }, `unverified-from:${taintCount}`));
}

function builtOn(root: Node, part: Node): boolean {
  const seen = new Set<Node>();
  const stack: Node[] = [root];
  while (stack.length) {
    const node = stack.pop();
    if (!node || seen.has(node)) continue;
    if (node === part) return true;
    seen.add(node);
    if (node.type === "eml") stack.push(node.a, node.b);
  }
  return false;
}

function foldAst(ast: Ast): Node {
  if (ast.k === "n") return ast.node;
  // Flattening would split (a+b)+(-(a+b)) into a, b, and -(a+b), so the identical nodes never meet.
  if (ast.k === "+" && holdsNegatedGroup(ast)) {
    const parts = ast.args.map(foldAst);
    const first = parts[0];
    if (!first) throw new EmlError("The expression ended early.");
    return parts.slice(1).reduce((sum, part) => refuseFrom([sum, part], userAdd(sum, part)), first);
  }
  if (ast.k === "+" || ast.k === "*") {
    const flat: Ast[] = [];
    const pending: Ast[] = [ast];
    while (pending.length) {
      const item = pending.pop();
      if (!item) break;
      if (item.k === ast.k) {
        for (let i = item.args.length - 1; i >= 0; i -= 1) {
          const child = item.args[i];
          if (child) pending.push(child);
        }
      } else flat.push(item);
    }
    const parts = flat.map(foldAst);
    return refuseFrom(parts, balanced(ast.k, parts));
  }
  if (ast.k === "pre") {
    const arg = foldAst(ast.arg);
    return refuseFrom([arg], ast.name === "neg" ? tNeg(arg) : tSqrt(arg));
  }
  if (ast.k === "call") {
    const args = ast.args.map(foldAst);
    return refuseFrom(args, applyNode(ast.name, args));
  }
  const left = foldAst(ast.args[0]);
  const right = foldAst(ast.args[1]);
  const pair = [left, right];
  if (ast.name === "-") return refuseFrom(pair, userSub(left, right));
  if (ast.name === "/") return refuseFrom(pair, tDiv(left, right));
  return refuseFrom(pair, tPow(left, right));
}

export function compileExpression(source: string, variables: Record<string, Node>): Node {
  return isolateCircuit(() => {
    const root = compileParsed(source, variables);
    // A trig angle past 10^15 under the root is refused; the root's own trig or
    // pole note already says the angle is too large.
    const note = precisionNoteOf(root);
    const own = note?.kind === "trig" || note?.kind === "pole";
    if (builtHugeAngle() && !own && root.type === "eml") markExactUnsure(root);
    return root;
  });
}

function compileParsed(source: string, variables: Record<string, Node>): Node {
  const stack: Ast[] = [];
  for (const item of toRpn(tokenize(source))) {
    if (item.k === "num") {
      stack.push({ k: "n", node: literalNode(item.text) });
      continue;
    }
    if (item.k === "const") {
      stack.push({ k: "n", node: item.name === "pi" ? tPi() : item.name === "e" ? tE() : tI() });
      continue;
    }
    if (item.k === "var") {
      const node = variables[item.name];
      if (!node) throw new EmlError(`Give ${item.name} a value first.`);
      stack.push({ k: "n", node });
      continue;
    }
    if (item.k === "call") {
      if (stack.length < item.argc) throw new EmlError("The expression ended early.");
      const args = stack.splice(stack.length - item.argc, item.argc);
      stack.push({ k: "call", name: item.name, args });
      continue;
    }
    if (item.name === "neg" || item.name === "sqrt") {
      const arg = stack.pop();
      if (!arg) throw new EmlError("The expression ended early.");
      stack.push({ k: "pre", name: item.name, arg });
      continue;
    }
    const right = stack.pop();
    const left = stack.pop();
    if (!left || !right) throw new EmlError("The expression ended early.");
    if (item.name === "+" || item.name === "*") stack.push({ k: item.name, args: [left, right] });
    else stack.push({ k: "bin", name: item.name, args: [left, right] });
  }
  const root = stack.pop();
  if (!root || stack.length) throw new EmlError("The expression has an extra symbol.");
  return foldAst(root);
}

const REF_UNARY: Record<string, (z: C) => C> = {
  exp: cexp,
  ln: clogPrincipal,
  sqrt: (z) => cpow(z, c(0.5)),
  sqr: (z) => cmul(z, z),
  inv: (z) => cdiv(c(1), z),
  half: (z) => cdiv(z, c(2)),
  minus: cneg,
  sin: csin,
  cos: ccos,
  tan: ctan,
  sinh: csinh,
  cosh: ccosh,
  tanh: ctanh,
  arcsin: casin,
  arccos: cacos,
  arctan: catan,
  arsinh: casinh,
  arcosh: cacosh,
  artanh: catanh,
  sigma: (z) => cdiv(c(1), cadd(c(1), cexp(cneg(z)))),
};

function applyRef(name: string, args: C[]): C {
  const z = args[0];
  const w = args[1];
  if (!z) return { re: NaN, im: NaN };
  if (name === "log" && !w) return clogPrincipal(z);
  const key = UNARY_ALIAS[name] ?? name;
  if (w && Object.hasOwn(binaryCalls, key)) return binaryCalls[key as keyof typeof binaryCalls].ref(z, w);
  const unary = REF_UNARY[key];
  return unary ? unary(z) : { re: NaN, im: NaN };
}

function refNumber(text: string): C {
  const value = Number(text);
  if (Number.isNaN(value)) throw new EmlError(`Cannot read the number ${text}.`);
  return c(value);
}

function refNeg(value: C): C {
  if (value.im === 0 && value.re === 0 && !Object.is(value.re, -0)) return { re: -0, im: 0 };
  return cneg(value);
}

/** The same expression on an ordinary complex calculator, for comparison. */
export function referenceExpression(source: string, variables: Record<string, C>): C | null {
  try {
    const stack: C[] = [];
    for (const item of toRpn(tokenize(source))) {
      if (item.k === "num") {
        stack.push(refNumber(item.text));
        continue;
      }
      if (item.k === "const") {
        stack.push(item.name === "pi" ? c(Math.PI) : item.name === "e" ? c(Math.E) : c(0, 1));
        continue;
      }
      if (item.k === "var") {
        stack.push(variables[item.name] ?? { re: NaN, im: NaN });
        continue;
      }
      if (item.k === "call") {
        const args = stack.splice(stack.length - item.argc, item.argc);
        stack.push(applyRef(item.name, args));
        continue;
      }
      if (item.name === "neg" || item.name === "sqrt") {
        const arg = stack.pop();
        if (!arg) return null;
        stack.push(item.name === "neg" ? refNeg(arg) : cpow(arg, c(0.5)));
        continue;
      }
      const right = stack.pop();
      const left = stack.pop();
      if (!left || !right) return null;
      if (item.name === "+") stack.push(cadd(left, right));
      else if (item.name === "-") stack.push(csub(left, right));
      else if (item.name === "*") stack.push(cmul(left, right));
      else if (item.name === "/") stack.push(cdiv(left, right));
      else stack.push(cpow(left, right));
    }
    return stack.length === 1 ? stack[0] ?? null : null;
  } catch {
    return null;
  }
}

/**
 * How the screen compares a result with an ordinary calculator.
 * A reference that collapsed to 0 while the printed value did not is float underflow,
 * including ln(1+10^(−130)), whose addend never reaches the float sum.
 */
export function agreementNote(caption: string, value: C, variables: Record<string, C>, text: string): string | null {
  const ref = referenceExpression(caption, variables);
  if (!ref || !isUsable(ref)) return null;
  const refZero = ref.re === 0 && (ref.im === 0 || Object.is(ref.im, -0));
  const textZero = text.trim() === "0" || text.trim() === "−0" || text.trim() === "-0";
  if (refZero && !textZero) return "float underflows";
  if (isUsable(value) && formatC(value) === formatC(ref)) return "matches the usual value";
  if (/tan\s*\(\s*pi\s*\/\s*2\s*\)/i.test(preprocess(caption))) {
    return "near a pole: this π/2 is not the mathematical pole, and the digits depend on the engine";
  }
  return `usual value ${formatC(ref)}`;
}
