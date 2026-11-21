/**
 * Full containment sample from docs/interval-bounds.md §6.
 * 10^5 random disks, plus 10^5 pairs drawn from a K=15 sound pool.
 * CI runs a smaller sample inside lib/eml/check.ts.
 *
 *   npx tsx scripts/interval-containment.ts
 */
import Decimal from "decimal.js";
import { emlDisk, expDisk, logDisk, pointDisk, type Disk } from "../lib/eml/interval";
import { searchConstants } from "../lib/eml/golf";

const D = Decimal.clone({ precision: 60 });
const SAMPLES = 100_000;
const PAIRS = 100_000;

function decOf(n: number): Decimal {
  if (!Number.isFinite(n)) return new D(n);
  const view = new DataView(new ArrayBuffer(8));
  view.setFloat64(0, n, false);
  const hi = view.getUint32(0, false);
  const lo = view.getUint32(4, false);
  const sign = hi >>> 31 ? -1 : 1;
  const exp = (hi >>> 20) & 0x7ff;
  const frac = new D(hi & 0xfffff).mul(new D(2).pow(32)).add(lo);
  if (exp === 0) {
    if (frac.isZero()) return sign < 0 ? new D(0).neg() : new D(0);
    const mag = frac.mul(new D(2).pow(-1074));
    return sign < 0 ? mag.neg() : mag;
  }
  return frac.add(new D(2).pow(52)).mul(new D(2).pow(exp - 1075)).mul(sign);
}

function contains(disk: Disk, re: Decimal, im: Decimal): boolean {
  if (!disk.ok) return false;
  const dist = re.sub(disk.re).pow(2).add(im.sub(disk.im).pow(2)).sqrt();
  return dist.lte(disk.r);
}

let rng = 0x51f00d;
function rand(): number {
  rng = (rng + 0x6d2b79f5) | 0;
  let t = Math.imul(rng ^ (rng >>> 15), 1 | rng);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
function span(lo: number, hi: number): number {
  return lo + (hi - lo) * rand();
}

let checked = 0;
let missed = 0;
let inconclusive = 0;
for (let n = 0; n < SAMPLES; n += 1) {
  const band = n % 4;
  let x = 0;
  let y = 0;
  let radius = 0;
  if (band === 0) {
    x = span(-3, 3);
    y = span(-3, 3);
    radius = rand() < 0.5 ? 0 : 10 ** span(-14, -8);
  } else if (band === 1) {
    x = span(-4, -0.05);
    y = (rand() < 0.5 ? -1 : 1) * 10 ** span(-10, -7);
    radius = 10 ** span(-14, -9);
  } else if (band === 2) {
    x = span(-2, 2);
    y = (rand() < 0.5 ? -1 : 1) * (2 ** 20 - span(1, 5000));
    radius = rand() < 0.7 ? 0 : 1e-6;
  } else {
    x = (rand() < 0.5 ? -1 : 1) * (700 - span(0, 3));
    y = span(-1, 1);
    radius = 0;
  }
  const input = pointDisk(x, y, radius);
  const shift = radius === 0 ? 0 : radius * 0.3;
  const px = decOf(x).add(shift);
  const py = decOf(y).add(shift * 0.5);
  const expOut = expDisk(input);
  if (!expOut.ok) inconclusive += 1;
  else {
    checked += 1;
    const mag = px.exp();
    if (!contains(expOut, mag.mul(py.cos()), mag.mul(py.sin()))) missed += 1;
  }
  const logOut = logDisk(input);
  if (!logOut.ok) inconclusive += 1;
  else {
    checked += 1;
    const rho = px.pow(2).add(py.pow(2)).sqrt();
    if (!contains(logOut, rho.ln(), D.atan2(py, px))) missed += 1;
  }
}

type Value = { re: Decimal; im: Decimal };
function evalRpn(rpn: string): Value | null {
  const stack: Value[] = [];
  for (const token of rpn) {
    if (token === "1") {
      stack.push({ re: new D(1), im: new D(0) });
      continue;
    }
    const right = stack.pop();
    const left = stack.pop();
    if (!left || !right) return null;
    const mag = left.re.exp();
    const rho = right.re.pow(2).add(right.im.pow(2)).sqrt();
    stack.push({
      re: mag.mul(left.im.cos()).sub(rho.ln()),
      im: mag.mul(left.im.sin()).sub(D.atan2(right.im, right.re)),
    });
  }
  return stack.length === 1 ? (stack[0] ?? null) : null;
}

const traced = searchConstants(15, { sound: true, trace: true });
const classes = (traced.classes ?? []).filter((item) => item.diskOk);
const values = new Map<string, Value>();
let poolMiss = 0;
let poolChecked = 0;
for (const item of classes) {
  const value = evalRpn(item.rpn);
  if (!value) continue;
  values.set(item.rpn, value);
  poolChecked += 1;
  if (!contains({ re: item.diskRe, im: item.diskIm, r: item.diskR, ok: true }, value.re, value.im)) poolMiss += 1;
}
let pairChecked = 0;
let pairMiss = 0;
for (let n = 0; n < PAIRS; n += 1) {
  const left = classes[Math.floor(rand() * classes.length)];
  const right = classes[Math.floor(rand() * classes.length)];
  if (!left || !right) continue;
  const a = values.get(left.rpn);
  const b = values.get(right.rpn);
  if (!a || !b) continue;
  const disk = emlDisk(
    { re: left.diskRe, im: left.diskIm, r: left.diskR, ok: true },
    { re: right.diskRe, im: right.diskIm, r: right.diskR, ok: true },
  );
  if (!disk.ok) {
    inconclusive += 1;
    continue;
  }
  const mag = a.re.exp();
  const rho = b.re.pow(2).add(b.im.pow(2)).sqrt();
  pairChecked += 1;
  if (!contains(disk, mag.mul(a.im.cos()).sub(rho.ln()), mag.mul(a.im.sin()).sub(D.atan2(b.im, b.re)))) pairMiss += 1;
}

console.log(JSON.stringify({ samples: SAMPLES, checked, missed, inconclusive, poolChecked, poolMiss, pairChecked, pairMiss }, null, 2));
if (missed !== 0 || poolMiss !== 0 || pairMiss !== 0 || checked < 1000 || pairChecked < 1000) process.exit(1);
