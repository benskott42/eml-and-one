/**
 * Rigorous complex disks for sound float mode.
 *
 * The formulas are mathbot's derivation, copied in docs/interval-bounds.md.
 * A disk D(c, r) claims the true value lies within distance r of the float
 * midpoint c. Radii are rounded up. An inconclusive disk never certifies
 * that two values are distinct; the search sends that pair to the exact engine.
 *
 * There is no provable-realness flag on the exact side, so the optional fast
 * path for a negative real (bounds §5) is not implemented. Log of a disk that
 * meets the closed ray (−∞, 0] is inconclusive, and those values escalate.
 */
import fixtures from "./libm-fixtures.json";

/** One correctly rounded + − × ÷, as a relative unit. */
export const U = 2 ** -52;
/**
 * Per-call relative budget for Math.exp, log, log1p, expm1, cos, sin, atan2
 * and hypot. About 4096 ulp. The self-test requires a 256× tighter margin.
 */
export const EPS = 2 ** -40;
/** Absolute pad so a rounded-up radius cannot collapse to 0. */
export const RAD_FLOOR = 2 ** -1020;
const MARGIN = 2 ** -48;
const COMP_CAP = 2 ** 60;
const REL_CAP = 2 ** -10;

export type Disk = {
  re: number;
  im: number;
  /** Always an upper bound when `ok` is true. */
  r: number;
  /** False: NaN, overflow, branch cut, or a radius too wide to trust. */
  ok: boolean;
};

type Fixture = { fn: string; x: string; y?: string; expect: string };

const TABLE = fixtures.entries as Fixture[];

function fromHex(hex: string): number {
  const view = new DataView(new ArrayBuffer(8));
  view.setUint32(0, Number.parseInt(hex.slice(0, 8), 16), true);
  view.setUint32(4, Number.parseInt(hex.slice(8, 16), 16), true);
  return view.getFloat64(0, true);
}

function libm(fn: string, x: number, y: number): number {
  if (fn === "exp") return Math.exp(x);
  if (fn === "expm1") return Math.expm1(x);
  if (fn === "log") return Math.log(x);
  if (fn === "log1p") return Math.log1p(x);
  if (fn === "sin") return Math.sin(x);
  if (fn === "cos") return Math.cos(x);
  if (fn === "atan2") return Math.atan2(y, x);
  if (fn === "hypot") return Math.hypot(x, y);
  return Number.NaN;
}

/**
 * Relative error, except sin/cos (absolute ε in the derivation) and atan2
 * (absolute ε·π). The limit is 2^−48, 256× under ε = 2^−40.
 */
export function libmError(fn: string, got: number, truth: number): number {
  const err = Math.abs(got - truth);
  if (fn === "sin" || fn === "cos") return err / MARGIN;
  if (fn === "atan2") return err / (MARGIN * Math.PI);
  const scale = Math.abs(truth);
  if (scale === 0) return err === 0 ? 0 : Number.POSITIVE_INFINITY;
  return err / (MARGIN * scale);
}

export type LibmReport = { ok: boolean; checked: number; worst: number; worstFn: string };

let cached: LibmReport | null = null;

/** Startup self-test. A failure turns certification off for the rest of the process. */
export function libmCertification(): LibmReport {
  if (cached) return cached;
  let worst = 0;
  let worstFn = "";
  let checked = 0;
  for (const row of TABLE) {
    const x = fromHex(row.x);
    const y = row.y === undefined ? 0 : fromHex(row.y);
    const truth = fromHex(row.expect);
    const got = libm(row.fn, x, y);
    const ratio = libmError(row.fn, got, truth);
    checked += 1;
    if (ratio > worst) {
      worst = ratio;
      worstFn = row.fn;
    }
  }
  const ok = checked >= 200 && worst <= 1;
  cached = { ok, checked, worst, worstFn };
  return cached;
}

export function certificationEnabled(): boolean {
  return libmCertification().ok;
}

/** r ← fl(r)·(1+8u) + 2^−1020. */
export function roundRadius(r: number): number {
  if (!(r >= 0) || !Number.isFinite(r)) return Number.POSITIVE_INFINITY;
  return r * (1 + 8 * U) + RAD_FLOOR;
}

/** NaN, infinity, a component above 2^60, or a radius wider than 2^−10·max(1, |c|). */
export function diskInconclusive(re: number, im: number, r: number): boolean {
  if (!Number.isFinite(re) || !Number.isFinite(im) || !Number.isFinite(r)) return true;
  if (Math.abs(re) > COMP_CAP || Math.abs(im) > COMP_CAP) return true;
  const limit = REL_CAP * Math.max(1, Math.hypot(re, im));
  return !(r <= limit);
}

function bad(re = Number.NaN, im = Number.NaN): Disk {
  return { re, im, r: Number.POSITIVE_INFINITY, ok: false };
}

/** Exact float input. A nonzero radius is rounded up. The leaf 1 uses r = 0. */
export function pointDisk(re: number, im = 0, r = 0): Disk {
  const radius = r === 0 ? 0 : roundRadius(r);
  if (!certificationEnabled() || diskInconclusive(re, im, radius)) return bad(re, im);
  return { re, im, r: radius, ok: true };
}

/**
 * exp(D(c, r)). Inconclusive unless −700 < x < 700 and |y| < 2^20.
 * r′ = X(1+ε)·[expm1(r)(1+ε) + 3ε + 4u], then rounded up.
 */
export function expDisk(z: Disk): Disk {
  if (!z.ok || !certificationEnabled()) return bad(z.re, z.im);
  const x = z.re;
  const y = z.im;
  const r = z.r;
  if (!(r >= 0) || !(x > -700 && x < 700) || !(Math.abs(y) < 2 ** 20)) return bad(x, y);
  if (diskInconclusive(x, y, r)) return bad(x, y);
  const mag = Math.exp(x);
  const re = mag * Math.cos(y);
  const im = mag * Math.sin(y);
  const grown = Math.expm1(r) * (1 + EPS) + 3 * EPS + 4 * U;
  const radius = roundRadius(mag * (1 + EPS) * grown);
  if (diskInconclusive(re, im, radius)) return bad(re, im);
  return { re, im, r: radius, ok: true };
}

/**
 * Log on a disk that stays off the closed ray (−∞, 0]. Both cuts agree there.
 * dist = |Im c| when Re c < 0, otherwise |c|. Require dist·(1−4ε) > r.
 * t = r/ρ↓ with ρ↓ = hypot·(1−2ε), and t ≥ 0.5 is inconclusive.
 * r′ = −log1p(−t)(1+ε) + ε(1+|ln ρ|) + επ + 2u(|Lre|+π), then rounded up.
 */
export function logDisk(z: Disk): Disk {
  if (!z.ok || !certificationEnabled()) return bad(z.re, z.im);
  const x = z.re;
  const y = z.im;
  const r = z.r;
  if (!(r >= 0) || diskInconclusive(x, y, r)) return bad(x, y);
  const rho = Math.hypot(x, y);
  const dist = x < 0 ? Math.abs(y) : rho;
  if (!(dist * (1 - 4 * EPS) > r)) return bad(x, y);
  const rhoDown = rho * (1 - 2 * EPS);
  if (!(rhoDown > 0) || !Number.isFinite(rhoDown)) return bad(x, y);
  // Division can round down. (1+2u) pushes t up; ρ↓ is already a lower bound.
  const t = r === 0 ? 0 : (r / rhoDown) * (1 + 2 * U);
  if (!(t >= 0) || t >= 0.5) return bad(x, y);
  const lRe = Math.log(rho);
  const lIm = Math.atan2(y, x);
  // |ln ρ| ≤ |Lre|(1+ε) + ε, so the ε|ln ρ| term stays an upper bound.
  const lnAbs = Math.abs(lRe) * (1 + EPS) + EPS;
  const prop = -Math.log1p(-t) * (1 + EPS);
  const radius = roundRadius(prop + EPS * (1 + lnAbs) + EPS * Math.PI + 2 * U * (Math.abs(lRe) + Math.PI));
  if (diskInconclusive(lRe, lIm, radius)) return bad(lRe, lIm);
  return { re: lRe, im: lIm, r: radius, ok: true };
}

/**
 * eml(a, b) = exp(a) − Log(b).
 * r = r_exp + r_log + u·(|m_exp| + |m_log|)·√2, then rounded up.
 */
export function emlDisk(a: Disk, b: Disk): Disk {
  if (!certificationEnabled()) return bad();
  const left = expDisk(a);
  const right = logDisk(b);
  if (!left.ok || !right.ok) return bad();
  const re = left.re - right.re;
  const im = left.im - right.im;
  const slack = U * (Math.hypot(left.re, left.im) + Math.hypot(right.re, right.im)) * Math.SQRT2;
  const radius = roundRadius(left.r + right.r + slack);
  if (diskInconclusive(re, im, radius)) return bad(re, im);
  return { re, im, r: radius, ok: true };
}

/**
 * Max-norm separation. Disjoint when |Δre| or |Δim| exceeds
 * (r1+r2)(1+4u)^2 + 4u·max|c|, which covers the rounding of Δ.
 * A false answer is "not disjoint": the search then goes to exact.
 */
export function disksDisjoint(a: Disk, b: Disk): boolean {
  if (!a.ok || !b.ok) return false;
  if (!Number.isFinite(a.r) || !Number.isFinite(b.r)) return false;
  const reach = (a.r + b.r) * (1 + 4 * U);
  const maxC = Math.max(Math.abs(a.re), Math.abs(a.im), Math.abs(b.re), Math.abs(b.im));
  const threshold = reach * (1 + 4 * U) + 4 * U * maxC;
  return Math.abs(a.re - b.re) > threshold || Math.abs(a.im - b.im) > threshold;
}

/**
 * Relative grid. Cell width at octave e is 2^(e−7), at least twice the
 * largest radius a conclusive disk at that octave can have
 * (r ≤ 2^−10·|c| and |c| < 2^(e+1)). A query checks octaves e−1, e, e+1
 * and a 5×5 neighbourhood, which covers a disk that stops at the next cell.
 * Any id returned might overlap; the caller still runs disksDisjoint.
 */
export class DiskGrid {
  private cells = new Map<string, number[]>();

  add(id: number, disk: Disk): void {
    if (!disk.ok) return;
    const key = cellKey(disk.re, disk.im);
    const bucket = this.cells.get(key);
    if (bucket) bucket.push(id);
    else this.cells.set(key, [id]);
  }

  nearby(disk: Disk): number[] {
    if (!disk.ok) return [];
    const base = octave(disk.re, disk.im);
    const out: number[] = [];
    for (let level = Math.max(0, base - 1); level <= base + 1; level += 1) {
      const width = 2 ** (level - 7);
      const ix = Math.floor(disk.re / width);
      const iy = Math.floor(disk.im / width);
      for (let dx = -2; dx <= 2; dx += 1) {
        for (let dy = -2; dy <= 2; dy += 1) {
          const bucket = this.cells.get(`${level}:${ix + dx}:${iy + dy}`);
          if (bucket) out.push(...bucket);
        }
      }
    }
    return out;
  }
}

function octave(re: number, im: number): number {
  const rho = Math.hypot(re, im);
  if (!(rho >= 2) || !Number.isFinite(rho)) return 0;
  const e = Math.floor(Math.log2(rho));
  return e > 0 ? e : 0;
}

function cellKey(re: number, im: number): string {
  const level = octave(re, im);
  const width = 2 ** (level - 7);
  return `${level}:${Math.floor(re / width)}:${Math.floor(im / width)}`;
}
