import { unitUlp, type C } from "./complex";

/** True on the negative-real axis, including −∞. An imaginary part of ±0 is on the axis. */
export function onNegativeCutF(re: number, im: number): boolean {
  if (!(re < 0)) return false;
  return im === 0 || Object.is(im, -0);
}

/**
 * What the exact rule reads: a zero imaginary part and a negative real part.
 * A real part of −0 is zero, so it is not the negative-real axis here. ln(−0)
 * still takes Arg −π in the zero branch of lnEml; this predicate only decides
 * the cut count, and it matches onNegativeCutF(−0, 0).
 */
export type ZCut = { re: { isNeg(): boolean; isZero(): boolean }; im: { isZero(): boolean } };

export function onNegativeCutZ(z: ZCut): boolean {
  if (z.re.isZero()) return false;
  return z.im.isZero() && z.re.isNeg();
}

/** 32 ulps of max(1, |re|). Same scale the float comparator already uses. */
export function cutDustTolerance(re: number): number {
  return 32 * unitUlp(Math.max(1, Math.abs(re)));
}

type TraceNode = { type: string; a?: TraceNode; b?: TraceNode };

const floatInputs = new WeakMap<object, C>();
const exactInputs = new WeakMap<object, ZCut>();
let traceOn = false;

/** Test and `?debug=cut` only. Off on the shipped page, and it does not change values. */
export function setCutTrace(on: boolean): void {
  traceOn = on;
}

export function cutTraceActive(): boolean {
  return traceOn;
}

export function noteFloatGate(node: object, y: C): void {
  if (!traceOn) return;
  floatInputs.set(node, { re: y.re, im: y.im });
}

export function noteExactGate(node: object, y: ZCut): void {
  if (!traceOn) return;
  const reNeg = y.re.isNeg();
  const reZero = y.re.isZero();
  const imZero = y.im.isZero();
  exactInputs.set(node, { re: { isNeg: () => reNeg, isZero: () => reZero }, im: { isZero: () => imZero } });
}

function occurrenceTrace<T>(root: TraceNode, valueOf: (node: object) => T | undefined): T[] {
  const out: T[] = [];
  const visiting = new Set<object>();
  const stack: { n: TraceNode; seen: boolean }[] = [{ n: root, seen: false }];
  while (stack.length) {
    const frame = stack.pop();
    if (!frame) break;
    const node = frame.n;
    if (!frame.seen) {
      if (node.type !== "eml" || !node.a || !node.b) continue;
      if (visiting.has(node)) throw new Error("The cut trace hit a cycle.");
      visiting.add(node);
      stack.push({ n: node, seen: true });
      stack.push({ n: node.b, seen: false });
      stack.push({ n: node.a, seen: false });
      continue;
    }
    visiting.delete(node);
    const y = valueOf(node);
    if (y === undefined) throw new Error("A logarithm was taken with no traced input.");
    out.push(y);
  }
  return out;
}

export function floatTraceOf(root: TraceNode): C[] {
  return occurrenceTrace(root, (node) => floatInputs.get(node));
}

export function exactTraceOf(root: TraceNode): ZCut[] {
  return occurrenceTrace(root, (node) => exactInputs.get(node));
}

export type Case2 = { gate: number; floatIm: number };
export type CutCheck = {
  ok: boolean;
  lengthOk: boolean;
  floatHits: number;
  exactHits: number;
  case2: Case2[];
  violations: string[];
};

/**
 * Gate-by-gate comparison. The traces must be the same length.
 * A gate passes when the two decisions agree, or when exact is on the cut,
 * float is off it, float's real part is negative, and float's imaginary part
 * is finite, nonzero, and within cutDustTolerance.
 */
export function checkCutTraces(floatYs: C[], exactYs: ZCut[]): CutCheck {
  const violations: string[] = [];
  const case2: Case2[] = [];
  let floatHits = 0;
  let exactHits = 0;
  const lengthOk = floatYs.length === exactYs.length;
  if (!lengthOk) violations.push(`trace lengths differ: float ${floatYs.length}, exact ${exactYs.length}`);
  for (let i = 0; lengthOk && i < floatYs.length; i += 1) {
    const y = floatYs[i];
    if (!y) {
      violations.push(`gate ${i}: missing float input`);
      continue;
    }
    const exact = exactYs[i];
    if (!exact) {
      violations.push(`gate ${i}: missing exact input`);
      continue;
    }
    const floatOn = onNegativeCutF(y.re, y.im);
    const exactOn = onNegativeCutZ(exact);
    if (floatOn) floatHits += 1;
    if (exactOn) exactHits += 1;
    if (floatOn === exactOn) continue;
    const dust =
      exactOn &&
      !floatOn &&
      y.re < 0 &&
      Number.isFinite(y.im) &&
      y.im !== 0 &&
      Math.abs(y.im) <= cutDustTolerance(y.re);
    if (dust) case2.push({ gate: i, floatIm: y.im });
    else violations.push(`gate ${i}: float ${floatOn ? "on" : "off"} (${y.re}, ${y.im}), exact ${exactOn ? "on" : "off"}`);
  }
  if (lengthOk && Math.abs(exactHits - floatHits) !== case2.length) {
    violations.push(`|exact ${exactHits} − float ${floatHits}| ≠ ${case2.length} case-2 gates`);
  }
  return { ok: violations.length === 0, lengthOk, floatHits, exactHits, case2, violations };
}

/** Four synthetic traces that fail, and one case-2 trace that passes. */
export function ruleSelfTest(): { name: string; want: "fail" | "pass"; got: "fail" | "pass" }[] {
  const z = (reNeg: boolean, imZero: boolean): ZCut => ({
    re: { isNeg: () => reNeg, isZero: () => false },
    im: { isZero: () => imZero },
  });
  const tol = cutDustTolerance(-2);
  const cases: [string, "fail" | "pass", C[], ZCut[]][] = [
    ["(a) float on the cut, exact off it", "fail", [{ re: -2, im: 0 }], [z(false, false)]],
    ["(b) float im at 2 × cutDustTolerance", "fail", [{ re: -2, im: 2 * tol }], [z(true, true)]],
    ["(c) exact im 1e-130, float exactly on the axis", "fail", [{ re: -2, im: 0 }], [z(true, false)]],
    ["(d) traces of different lengths", "fail", [{ re: -2, im: 0 }, { re: 3, im: 0 }], [z(true, true)]],
    ["case 2: float dust off an exact cut point", "pass", [{ re: 1, im: 0 }, { re: -2, im: tol / 2 }], [z(false, true), z(true, true)]],
  ];
  return cases.map(([name, want, floatYs, exactYs]) => ({
    name,
    want,
    got: checkCutTraces(floatYs, exactYs).ok ? "pass" : "fail",
  }));
}
