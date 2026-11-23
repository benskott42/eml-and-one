// Prototype of the proposed ball rules (ball-soundness.md §1-§3) on decimal.js 10.6.0.
// Centre clone D: precision P, default ROUND_HALF_UP. Radius clones: DU (ROUND_UP), DD (ROUND_DOWN), Q digits.
// From a checkout with dependencies installed (`npm ci`):
//   node docs/design/ball-checks/proto.mjs
// ref.py is spawned beside this file and needs python3 and mpmath. The series check is separate:
//   python3 docs/design/ball-checks/series_tails.py
import { createRequire } from "node:module";
import { spawnSync } from "node:child_process";
const require = createRequire(import.meta.url);
const Decimal = require("decimal.js");
const P = Number(process.env.P ?? 300), Q = 20;
const D = Decimal.clone({ precision: P });
const DU = Decimal.clone({ precision: Q, rounding: Decimal.ROUND_UP });
const DD = Decimal.clone({ precision: Q, rounding: Decimal.ROUND_DOWN });
const R = Decimal.clone({ precision: 650 });
const u = new DU(10).pow(1 - P);                 // unit roundoff bound for one centre op, 10^(1-P)
const up = (x) => new DU(x.abs().toString());     // exact conversion (constructor does not round)
const pad = (x) => x.mul(new DU(1).add(new DU(10).pow(1 - Q))); // one radius-clone ulp after a transcendental
// e^rho - 1 <= rho(1+rho) for rho <= 1 (polynomial, no cancellation); rho*e^rho otherwise.
const em1 = (rho) => (rho.lte(1) ? rho.mul(rho.add(1)) : pad(rho.mul(pad(rho.exp()))));

export function cexp(z) {
  const M = z.re.exp(), C = z.im.cos(), S = z.im.sin();
  if (!M.isFinite() || M.isZero()) return { overflow: true };
  const re = M.mul(C), im = M.mul(S);
  const rho = up(z.rr).add(up(z.ir));
  const Mup = up(M).mul(u.mul(2).add(1));          // >= e^x
  const r = Mup.mul(em1(rho).add(u.mul(8)));       // Lipschitz term + rounding charged on |e^c|, not on re/im
  return { re, im, rr: r, ir: r };
}

// Lower bank: Arg on the negative real axis is -pi. Rectangle [x±rx]×[y±ry].
export function cln(z) {
  const { re: x, im: y, rr: rx, ir: ry } = z;
  const ax = new D(x).abs(), ay = new D(y).abs();
  if (ax.lte(rx.toString()) && ay.lte(ry.toString())) return { undecided: "contains 0" };
  const xlNeg = x.lt(rx.toString());              // x - rx < 0, exact comparison
  const ylLe0 = y.lte(ry.toString());              // y - ry <= 0
  const yhPos = y.gt(ry.neg().toString());         // y + ry > 0
  if (xlNeg && ylLe0 && yhPos) return { cut: true }; // touches or crosses the closed ray from above
  const dx = ax.gt(rx.toString()) ? new DD(ax.toString()).sub(rx.toString()) : new DD(0);
  const dy = ay.gt(ry.toString()) ? new DD(ay.toString()).sub(ry.toString()) : new DD(0);
  const d = DD.max(dx, dy);                        // lower bound on dist(0, Z)
  const rho = up(rx).add(up(ry));
  const lip = rho.div(d.toString());               // >= |delta| / min|w|
  const s = x.mul(x).add(y.mul(y));
  const re = s.ln().mul(0.5);
  const im = y.isZero() && x.isNeg() ? D.acos(-1).neg() : D.atan2(y, x);
  return { re, im, rr: lip.add(u.mul(up(re).mul(2).add(1))), ir: lip.add(u.mul(2)) };
}

function mp(tasks) {
  const r = spawnSync("python3", [new URL("./ref.py", import.meta.url).pathname], { input: JSON.stringify(tasks), encoding: "utf8", maxBuffer: 1 << 30 });
  if (r.status !== 0) throw new Error(r.stderr);
  return JSON.parse(r.stdout).map(([a, b]) => [new R(a), new R(b)]);
}
const ratio = (c, rad, t) => { const e = t.sub(new R(c.toString())).abs(); if (e.lt("1e-600")) return new R(0); return e.div(new R(rad.toString())); };
const ball = (re, im, rr = 0, ir = 0) => ({ re: new D(re), im: new D(im), rr: new D(rr), ir: new D(ir) });
let seed = 12345; const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);

// Check a ball op on a list of input rectangles: sample corners, edge midpoints, centre and random points.
function check(name, op, kind, balls) {
  const tasks = [], idx = [];
  const outs = balls.map((b) => op(b));
  balls.forEach((b, i) => {
    const o = outs[i]; if (!o.re) return;
    const pts = [[0, 0], [1, 1], [1, -1], [-1, 1], [-1, -1], [1, 0], [-1, 0], [0, 1], [0, -1], [rnd() * 2 - 1, rnd() * 2 - 1], [rnd() * 2 - 1, rnd() * 2 - 1]];
    for (const [s, t] of pts) {
      tasks.push([kind, b.re.add(b.rr.mul(s)).toString(), b.im.add(b.ir.mul(t)).toString()]); idx.push(i);
    }
  });
  const refs = mp(tasks);
  let worst = new R(0), miss = 0, refused = outs.filter((o) => !o.re).length, ex = "";
  const missed = new Set();
  refs.forEach((t, k) => {
    const o = outs[idx[k]];
    const r = R.max(ratio(o.re, o.rr, t[0]), ratio(o.im, o.ir, t[1]));
    if (r.gt(worst)) worst = r;
    if (r.gt(1)) { missed.add(idx[k]); if (!ex) ex = `input #${idx[k]} sample ${tasks[k][1].slice(0, 20)}, ${tasks[k][2].slice(0, 20)}`; }
  });
  console.log(`${name}: ${balls.length} inputs, ${refused} refused (cut/0/overflow), ${missed.size} with a sample outside the ball, worst err/radius ${worst.toExponential(3)} ${ex}`);
  return missed.size;
}

let bad = 0;
// 1. The B3 point set (same generator and seed as tests/review-B/b3-cexp.ts): 3010 float point inputs.
{
  seed = 12345; const pts = [];
  for (let i = 0; i < 3000; i += 1) pts.push([(rnd() - 0.5) * 6, (rnd() - 0.5) * 20]);
  for (const k of [1, 3, 5, 101, 1e5 + 1]) pts.push([0, (k * Math.PI) / 2], [1.5, (k * Math.PI) / 2]);
  bad += check("cexp, B3 point set", cexp, "exp", pts.map(([a, b]) => ball(a, b)));
}
// 2. B3.3 stretch cases and random rectangles, radii 10^U(-310, -1).
{
  const bs = [ball(0, "1e-20", 0, "1e-310"), ball(0, "1e-20", 0, "3.4e-299"), ball(0, "1e-20", 0, "1.9e-298"), ball(0, D.acos(0), "1e-5", "1e-5"), ball(2, "1e6", "1e-200", "1e-200")];
  for (let i = 0; i < 400; i += 1) bs.push(ball((rnd() - 0.5) * 20, (rnd() - 0.5) * 40, new D(10).pow(-310 * rnd()), new D(10).pow(-310 * rnd())));
  bad += check("cexp, random rectangles", cexp, "exp", bs);
}
// 3. The B6 point set (same generator and seed as tests/review-B/b6-cln.ts): 2004 float point inputs.
{
  seed = 777; const pts = [[0.6, 0.8], [0.28, 0.96], [0.8, 0.6], [Math.SQRT1_2, Math.SQRT1_2]];
  for (let i = 0; i < 1500; i += 1) pts.push([(rnd() - 0.5) * 8, (rnd() - 0.5) * 8]);
  for (let i = 0; i < 500; i += 1) { const t = rnd() * 6.28; pts.push([Math.cos(t), Math.sin(t)]); }
  bad += check("cln, B6 point set", cln, "log", pts.map(([a, b]) => ball(a, b)));
}
// 4. cln rectangles: random, near |z|=1, and the cut edges.
{
  const bs = [ball(-1, "1e-10", 0, "1e-10") /* B4: must refuse */, ball(-1, "-1e-10", 0, "1e-10") /* touches from below: lower bank, certify */,
    ball(-1, 0, "1e-30", 0) /* on the ray, radius only in re: certify, -pi */, ball(-1, 0, 0, "1e-30") /* crosses: refuse */, ball("1e-30", "1e-30", "1e-30", "1e-30") /* contains 0 */];
  for (let i = 0; i < 300; i += 1) bs.push(ball((rnd() - 0.5) * 8, (rnd() - 0.5) * 8, new D(10).pow(-310 * rnd()), new D(10).pow(-310 * rnd())));
  for (let i = 0; i < 200; i += 1) { const t = rnd() * 6.28; bs.push(ball(Math.cos(t), Math.sin(t), new D(10).pow(-310 * rnd()), new D(10).pow(-310 * rnd()))); }
  for (let i = 0; i < 100; i += 1) bs.push(ball(-rnd() * 4, -rnd() * 1e-5, new D(10).pow(-6 - 300 * rnd()), new D(10).pow(-6 - 300 * rnd())));
  bad += check("cln, random rectangles", cln, "log", bs);
  const tags = ["B4 imLo=0", "imHi=0", "on ray, ir=0", "crosses ray", "contains 0"];
  bs.slice(0, 5).forEach((b, i) => { const o = cln(b); console.log(`  cln ${tags[i]}: ${o.cut ? "cut" : o.undecided ? "undecided (" + o.undecided + ")" : "im=" + o.im.toSignificantDigits(12) + " ± " + o.ir.toExponential(2)}`); });
}
// 5. e^rho - 1 <= rho(1+rho) on (0, 1].
{
  let ok = true; for (const r of ["1e-320", "1e-300", "3.4e-299", "1e-20", "0.001", "0.1", "0.5", "1"]) { const x = new R(r); if (x.exp().sub(1).gt(x.mul(x.add(1)))) ok = false; }
  console.log(`e^rho-1 <= rho(1+rho) on samples in (0,1]: ${ok}`);
}
// 6. decimal.js sin/cos large-argument behaviour (argument reduction uses pi to P+max(e,sd)+7 digits; pi is capped at 1025).
for (const a of ["1e6", "1e22", "1e100", "1e600"]) {
  try { const c = new D(a).cos(); const t = mp([["exp", "0", a]])[0][0]; console.log(`cos(${a}) abs err ${t.sub(c.toString()).abs().toExponential(2)} vs u=${u.toExponential()}`); }
  catch (e) { console.log(`cos(${a}): throws "${e.message}" -> must map to undecided`); }
}
console.log(bad === 0 ? "ALL CONTAINED" : `MISSES IN ${bad} GROUPS`);
