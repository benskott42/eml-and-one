import { cexp, clogPrincipal, csub, eml, type C } from "./complex";
import { ballVerdict, enclose } from "./enclose";
import { type Z, exactClose, exactReport, exactValueAt, valueMatchesTarget } from "./exact";
import { E, ONE, type Node, SINGULAR_LN0, evaluate, evaluateReport, expUnderflows } from "./node";

/**
 * Bottom-up search for short 1-and-EML circuits.
 * K is the RPN length, 2·(tree gates)+1. A float match is a hit only after
 * the wide-exponent evaluator agrees. A component that the target says is 0
 * must be exactly 0. A 40-digit zero is not enough: the K 33 word
 * 11111EE1E1111E1E1EEEE1EE11E1E1EEE reads as 0 and is about 5.7e-116,
 * and the K 35 word 11111111E1E1EEEEEE111EEE1E11E1E1EEE is about −3e-196.
 * An enclosure certifies a hit only when the whole ball lies inside a
 * 240-digit neighborhood of the target. A wider ball, a cut, or an overflow
 * is not a certificate. The 240-digit comparison used after that is a
 * high-precision check, not a proof: a component smaller than the working
 * tolerance is erased, and a residue such as 10^(−1 000 000) is still
 * rejected by the float overflow flag.
 * Any program that overflowed is rejected, even when a later step looks finite.
 * An exponential of a finite nonzero input that underflows to 0 or a
 * subnormal is rejected the same way. exp(−∞) from ln 0 is not that case.
 * The pool is not deduplicated by value. Every circuit whose float value is
 * finite, and which did not overflow or underflow, is kept, so the pool is a
 * set of programs, not of value classes. See `commit` for the one exception.
 */

export type GolfHit = {
  id: string;
  k: number;
  rpn: string;
  /** ln 0 changed the value (the result is not finite). */
  singular: boolean;
  /** The circuit logs 0, whether or not that cancels. */
  usesLn0: boolean;
  /** Which cut the evaluator was on when this hit was checked. */
  branch: "lower-bank" | "either";
  domain: "C" | "extended";
};
export type SearchProgress = { k: number; pool: number };

type Target = { id: string; re: number; im: number };

const CONSTANT_TARGETS: Target[] = [
  { id: "e", re: Math.E, im: 0 },
  { id: "0", re: 0, im: 0 },
  { id: "-1", re: -1, im: 0 },
  { id: "2", re: 2, im: 0 },
  { id: "ipi", re: 0, im: Math.PI },
  { id: "-ipi", re: 0, im: -Math.PI },
  { id: "-2", re: -2, im: 0 },
  { id: "3", re: 3, im: 0 },
  { id: "1/2", re: 0.5, im: 0 },
  { id: "-1/2", re: -0.5, im: 0 },
  { id: "-3", re: -3, im: 0 },
];

/**
 * Nonzero parts must agree with the exact target to 240 digits. A zero part
 * must be exactly zero at the precision of `value`. Twelve digits is not
 * enough: −1 + 10^(−20) and i(π + 10^(−20)) both pass a 12-digit test.
 * This comparison is not a proof past the working tolerance. Evaluating at
 * 240 digits erases a component smaller than about 10^(−232).
 */
export function acceptsConstantValue(value: Z, targetRe: number, targetIm: number): boolean {
  return valueMatchesTarget(value, targetRe, targetIm);
}

/**
 * Overflow or underflow rejects the hit. A ball that certifies 240-digit
 * agreement with the target is accepted. Anything else is not a certificate: a cut, a loose radius, or an
 * overflow from ln 0 falls through to a 240-digit comparison. That comparison
 * still requires a zero part to be exactly zero and a nonzero part to agree
 * to 240 digits. It is not a proof below the working tolerance.
 */
export function acceptsConstantProgram(node: Node, targetRe: number, targetIm: number): boolean {
  const floated = evaluateReport(node);
  if (floated.overflowed || floated.underflowed) return false;
  if (!Number.isFinite(floated.value.re) || !Number.isFinite(floated.value.im)) return false;
  const coarse = exactValueAt(node, 40);
  if (!exactClose(coarse, targetRe, targetIm, 12)) return false;
  const ball = enclose(node);
  const verdict = ballVerdict(ball, targetRe, targetIm);
  if (verdict === "unequal") return false;
  if (verdict !== "equal") {
    if (ball.overflow && !ball.cut && !floated.touchedLn0) return false;
    // Guard digits past 240, so the last place of a 240-digit target is stable.
    if (!acceptsConstantValue(exactValueAt(node, 280), targetRe, targetIm)) return false;
  }
  // Both checks above stop at about 10^(−240): the K 35 word
  // 11111111E11E1EE1EEEEEE1E1E11E1E1EEE is −9×10^(−307) − i(π − 4×10^(−307)),
  // and a ball or a 280-digit compare reads it as exactly −iπ. Exact mode raises
  // its precision for the 10^(−306) part it passes through and certifies that part,
  // so a component the target has as 0 must be certified 0 as well.
  const report = exactReport(node);
  if (report.unverified === true) return false;
  if (targetRe === 0 && !report.value.re.isZero()) return false;
  if (targetIm === 0 && !report.value.im.isZero()) return false;
  return true;
}

function near(re: number, im: number, target: Target, slack = 1): boolean {
  const scale = slack * Math.max(1, Math.abs(target.re), Math.abs(target.im));
  return Math.abs(re - target.re) <= 1e-6 * scale && Math.abs(im - target.im) <= 1e-6 * scale;
}

function sig(x: number): [number, number] {
  if (!Number.isFinite(x)) return [x > 0 ? 1 : 2, 0];
  if (x === 0) return [3, 0];
  const neg = x < 0 ? 1 : 0;
  const ax = Math.abs(x);
  let exp = Math.floor(Math.log10(ax));
  // 10 ** exp is subnormal below 10^(−307) and 0 below 10^(−323), which left
  // about one key per decade there. Scale first so the mantissa keeps 10 digits.
  const scaled = exp < -307 ? (ax * 1e300) / 10 ** (exp + 300) : ax / 10 ** exp;
  let mant = Math.round(scaled * 1e9);
  if (mant >= 10_000_000_000) {
    mant = 1_000_000_000;
    exp += 1;
  }
  const hi = (neg << 20) | ((exp + 1024) << 4) | (Math.floor(mant / 2 ** 32) & 0xf);
  return [hi, mant >>> 0];
}

/** An open-addressed set of four unsigned 32-bit words. Every word is stored and compared as `>>> 0`. */
class KeySet {
  private cap = 0;
  private mask = 0;
  private w0 = new Uint32Array(0);
  private w1 = new Uint32Array(0);
  private w2 = new Uint32Array(0);
  private w3 = new Uint32Array(0);
  private used = new Uint8Array(0);
  size = 0;

  add(a: number, b: number, c: number, d: number): boolean {
    a >>>= 0;
    b >>>= 0;
    c >>>= 0;
    d >>>= 0;
    if (this.size * 10 >= this.cap * 7) this.grow();
    let i = (Math.imul(a ^ Math.imul(b, 0x9e3779b1), 0x85ebca6b) ^ Math.imul(c ^ d, 0xc2b2ae35)) & this.mask;
    for (;;) {
      if (this.used[i] === 0) {
        this.used[i] = 1;
        this.w0[i] = a;
        this.w1[i] = b;
        this.w2[i] = c;
        this.w3[i] = d;
        this.size += 1;
        return true;
      }
      if (this.w0[i] === a && this.w1[i] === b && this.w2[i] === c && this.w3[i] === d) return false;
      i = (i + 1) & this.mask;
    }
  }

  private grow() {
    const prev = { w0: this.w0, w1: this.w1, w2: this.w2, w3: this.w3, used: this.used, cap: this.cap };
    const cap = this.cap < 1024 ? 1024 : this.cap << 1;
    this.cap = cap;
    this.mask = cap - 1;
    this.w0 = new Uint32Array(cap);
    this.w1 = new Uint32Array(cap);
    this.w2 = new Uint32Array(cap);
    this.w3 = new Uint32Array(cap);
    this.used = new Uint8Array(cap);
    this.size = 0;
    for (let i = 0; i < prev.cap; i += 1) {
      if (prev.used[i]) this.add(prev.w0[i] ?? 0, prev.w1[i] ?? 0, prev.w2[i] ?? 0, prev.w3[i] ?? 0);
    }
  }
}

function keyOf(re: number, im: number): [number, number, number, number] {
  const [a, b] = sig(re);
  const [c, d] = sig(im);
  return [a, b, c, d];
}

function buildNode(left: Int32Array, right: Int32Array, id: number, memo: Array<Node | undefined>): Node {
  const stack: { id: number; seen: boolean }[] = [{ id, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame || memo[frame.id]) continue;
    if ((left[frame.id] ?? -1) < 0) {
      memo[frame.id] = ONE;
      continue;
    }
    if (!frame.seen) {
      stack.push({ id: frame.id, seen: true });
      stack.push({ id: right[frame.id] ?? 0, seen: false });
      stack.push({ id: left[frame.id] ?? 0, seen: false });
      continue;
    }
    const a = memo[left[frame.id] ?? 0];
    const b = memo[right[frame.id] ?? 0];
    if (a && b) memo[frame.id] = E(a, b);
  }
  return memo[id] ?? ONE;
}

function rpnOf(left: Int32Array, right: Int32Array, id: number): string {
  const tokens: string[] = [];
  const stack: { id: number; seen: boolean }[] = [{ id, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    if ((left[frame.id] ?? -1) < 0) {
      tokens.push("1");
      continue;
    }
    if (!frame.seen) {
      stack.push({ id: frame.id, seen: true });
      stack.push({ id: right[frame.id] ?? 0, seen: false });
      stack.push({ id: left[frame.id] ?? 0, seen: false });
      continue;
    }
    tokens.push("E");
  }
  return tokens.join("");
}

/** Evaluate a constant circuit under principal Log (arg = +π on negative reals) to detect branch dependence. */
function principalValue(node: Node): C {
  const memo = new Map<Node, C>();
  const stack: { n: Node; seen: boolean }[] = [{ n: node, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const n = frame.n;
    if (memo.has(n)) continue;
    if (n.type === "one") {
      memo.set(n, { re: 1, im: 0 });
      continue;
    }
    if (n.type !== "eml" || !n.a || !n.b) return { re: NaN, im: NaN };
    if (!frame.seen) {
      stack.push({ n, seen: true });
      stack.push({ n: n.b, seen: false });
      stack.push({ n: n.a, seen: false });
      continue;
    }
    const a = memo.get(n.a);
    const b = memo.get(n.b);
    if (!a || !b) return { re: NaN, im: NaN };
    memo.set(n, csub(cexp(a), clogPrincipal(b)));
  }
  return memo.get(node) ?? { re: NaN, im: NaN };
}

export function searchConstants(
  maxK: number,
  options: {
    workers?: number;
    partition?: boolean;
    /** When false, programs that log 0 are left out of the pool. */
    allowLn0?: boolean;
    shouldStop?: () => boolean;
    onProgress?: (progress: SearchProgress) => void;
  } = {},
): { hits: GolfHit[]; pool: number } {
  const workers = options.workers !== undefined && Number.isInteger(options.workers) && options.workers >= 1 ? options.workers : 1;
  const maxGates = (maxK - 1) >> 1;
  let cap = 4096;
  let left = new Int32Array(cap);
  let right = new Int32Array(cap);
  let re = new Float64Array(cap);
  let im = new Float64Array(cap);
  let logged = new Uint8Array(cap);
  const grow = () => {
    cap *= 2;
    const nextLeft = new Int32Array(cap);
    const nextRight = new Int32Array(cap);
    const nextRe = new Float64Array(cap);
    const nextIm = new Float64Array(cap);
    const nextLogged = new Uint8Array(cap);
    nextLeft.set(left);
    nextRight.set(right);
    nextRe.set(re);
    nextIm.set(im);
    nextLogged.set(logged);
    left = nextLeft;
    right = nextRight;
    re = nextRe;
    im = nextIm;
    logged = nextLogged;
  };
  left[0] = -1;
  right[0] = -1;
  re[0] = 1;
  im[0] = 0;
  logged[0] = 0;
  let count = 1;
  // Circuits of the last length are never a child, so they are counted, not stored.
  let unstored = 0;
  const level = [0, 1];
  const found = new Map<string, GolfHit>();
  const nodeMemo: Array<Node | undefined> = [];
  // 10-digit keys of circuits near a target that overflowed, underflowed, or
  // failed the certifier. A later near-target circuit that fails with one of
  // these keys is left out. Only a key whose last word has bit 31 set counts
  // as a repeat: v1.0 compared that word signed against an unsigned store, so
  // other repeats were never seen, and this keeps the pool circuit for circuit.
  const repeats = new KeySet();
  const isRepeat = (valueRe: number, valueIm: number): boolean => {
    const [a, b, c, d] = keyOf(valueRe, valueIm);
    if (d < 0x80000000) return false;
    return !repeats.add(a, b, c, d);
  };

  const touchesLn0 = (a: number, b: number) =>
    logged[a] === 1 || logged[b] === 1 || ((re[b] ?? 0) === 0 && (im[b] ?? 0) === 0);

  const store = (a: number, b: number, valueRe: number, valueIm: number, fromLn: boolean) => {
    if (count >= cap) grow();
    logged[count] = fromLn ? 1 : 0;
    left[count] = a;
    right[count] = b;
    re[count] = valueRe;
    im[count] = valueIm;
    count += 1;
  };

  const commit = (a: number, b: number, valueRe: number, valueIm: number, gates: number, last: boolean) => {
    const fromLn = touchesLn0(a, b);
    const finite = Number.isFinite(valueRe) && Number.isFinite(valueIm);
    // An infinity born from finite inputs without logging 0 at this gate is float overflow,
    // even if a child had an ancestor ln 0 that already cancelled (e.g. K=15 −1).
    const aFinite = Number.isFinite(re[a] ?? 0) && Number.isFinite(im[a] ?? 0);
    const bFinite = Number.isFinite(re[b] ?? 0) && Number.isFinite(im[b] ?? 0);
    const bZero = (re[b] ?? 0) === 0 && (im[b] ?? 0) === 0;
    const overflow = !finite && (aFinite && bFinite && !bZero ? true : !fromLn);
    // exp of this gate's finite input. A stored child is never itself an
    // underflow: those nodes are left out of the pool, same as overflow.
    const under = expUnderflows({ re: re[a] ?? 0, im: im[a] ?? 0 });
    const imagAbs = Math.abs(valueIm);
    const nearAxis = imagAbs < 1e-4 || Math.abs(imagAbs - Math.PI) < 1e-4;
    if (overflow || under) {
      // A shorter overflowed or underflowed word keeps its key, so a clean
      // circuit with the same 10 digits that fails the certifier is a repeat.
      // Equal keys are within about 10^(−9) of each other, so only a value
      // close to a target can share a key with a circuit that is checked.
      if (finite && nearAxis && CONSTANT_TARGETS.some((target) => near(valueRe, valueIm, target, 2))) isRepeat(valueRe, valueIm);
      return;
    }
    const watch = nearAxis ? CONSTANT_TARGETS.filter((target) => !found.has(target.id) && near(valueRe, valueIm, target)) : [];
    if (watch.length > 0) {
      const built = E(buildNode(left, right, a, nodeMemo), buildNode(left, right, b, nodeMemo));
      let kept = false;
      for (const target of watch) {
        if (found.has(target.id) || !acceptsConstantProgram(built, target.re, target.im)) continue;
        const report = evaluateReport(built);
        const princ = principalValue(built);
        const scale = Math.max(1, Math.abs(valueRe), Math.abs(valueIm));
        const branchDiffers =
          !Number.isFinite(princ.re) ||
          !Number.isFinite(princ.im) ||
          Math.abs(princ.re - valueRe) > 1e-6 * scale ||
          Math.abs(princ.im - valueIm) > 1e-6 * scale;
        found.set(target.id, {
          id: target.id,
          k: gates * 2 + 1,
          rpn: `${rpnOf(left, right, a)}${rpnOf(left, right, b)}E`,
          singular: report.singular === SINGULAR_LN0,
          usesLn0: report.touchedLn0,
          branch: branchDiffers ? "lower-bank" : "either",
          domain: report.touchedLn0 ? "extended" : "C",
        });
        kept = true;
      }
      if (!kept && isRepeat(valueRe, valueIm)) return;
    }
    if (last) unstored += 1;
    else store(a, b, valueRe, valueIm, fromLn);
  };

  const result = () => ({
    hits: [...found.values()].sort((p, q) => p.k - q.k || p.id.localeCompare(q.id)),
    pool: count + unstored,
  });

  for (let gates = 1; gates <= maxGates; gates += 1) {
    if (options.shouldStop?.()) break;
    const start = count;
    const last = gates === maxGates;
    let pair = 0;
    const buckets: { pair: number; a: number; b: number; re: number; im: number }[][] = options.partition
      ? Array.from({ length: workers }, () => [])
      : [];
    for (let i = 0; i < gates; i += 1) {
      const j = gates - 1 - i;
      for (let a = level[i] ?? 0; a < (level[i + 1] ?? count); a += 1) {
        for (let b = level[j] ?? 0; b < (level[j + 1] ?? count); b += 1) {
          const index = pair++;
          if ((index & 2047) === 0 && options.shouldStop?.()) {
            level[gates + 1] = count;
            return result();
          }
          if (options.allowLn0 === false && touchesLn0(a, b)) continue;
          const value = eml({ re: re[a] ?? 0, im: im[a] ?? 0 }, { re: re[b] ?? 0, im: im[b] ?? 0 });
          if (Number.isNaN(value.re) || Number.isNaN(value.im)) continue;
          if (options.partition) {
            buckets[index % workers]?.push({ pair: index, a, b, re: value.re, im: value.im });
            continue;
          }
          commit(a, b, value.re, value.im, gates, last);
        }
      }
    }
    if (options.partition) {
      const ordered = buckets.flat().sort((p, q) => p.pair - q.pair);
      for (const item of ordered) commit(item.a, item.b, item.re, item.im, gates, last);
    }
    level[gates + 1] = count;
    options.onProgress?.({ k: gates * 2 + 1, pool: count + unstored - start });
  }

  return result();
}

// ln0Dependence lives in ./golf-label so the screen can label hits without loading the search.
export { ln0Dependence } from "./golf-label";

export function searchConstantsMerged(maxK: number, workers: number): GolfHit[] {
  return searchConstants(maxK, { workers, partition: workers > 1 }).hits;
}

export const FINGERPRINT_POINTS = [
  { re: 0.7, im: 0.4 },
  { re: 1.7, im: 0 },
  { re: -0.4, im: 0 },
  { re: -2.5, im: 1e-4 },
  { re: -2.5, im: -1e-4 },
  { re: 0.5, im: 4 },
  { re: 2.2, im: -0.8 },
  { re: -1.1, im: 2.4 },
];

export function functionFingerprint(node: Node, envFor: (point: { re: number; im: number }) => Record<string, { re: number; im: number }>): string {
  return FINGERPRINT_POINTS.map((point) => {
    const value = evaluate(node, envFor(point));
    const coarse = (x: number) => (Number.isFinite(x) ? x.toExponential(5) : String(x));
    return `${coarse(value.re)},${coarse(value.im)}`;
  }).join(";");
}
