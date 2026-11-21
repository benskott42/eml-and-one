import { searchConstants, setAuditPrincipal, setAuditNoWatch, AUDIT_POOL } from "./lib/eml/golf";
if (process.argv[3] === "nowatch") setAuditNoWatch(true);
const maxK = Number(process.argv[2] ?? 21);
function run(principal: boolean) {
  setAuditPrincipal(principal);
  const t = Date.now();
  const r = searchConstants(maxK);
  const p = { re: AUDIT_POOL.re.slice(0, AUDIT_POOL.count), im: AUDIT_POOL.im.slice(0, AUDIT_POOL.count), left: AUDIT_POOL.left.slice(0, AUDIT_POOL.count), right: AUDIT_POOL.right.slice(0, AUDIT_POOL.count), count: AUDIT_POOL.count };
  return { r, p, ms: Date.now() - t };
}
const L = run(false), P = run(true);
let structural = 0, reDiff = 0, imDiff = 0, zeroSign = 0;
const n = Math.min(L.p.count, P.p.count);
for (let i = 0; i < n; i++) {
  if (L.p.left[i] !== P.p.left[i] || L.p.right[i] !== P.p.right[i]) structural++;
  if (!(L.p.re[i] === P.p.re[i] || (Number.isNaN(L.p.re[i]) && Number.isNaN(P.p.re[i])))) reDiff++;
  if (!(L.p.im[i] === -P.p.im[i] || (Number.isNaN(L.p.im[i]) && Number.isNaN(P.p.im[i])))) imDiff++;
  if (L.p.im[i] === 0 && Object.is(L.p.im[i], -0) === Object.is(-P.p.im[i], -0) ? false : L.p.im[i] === 0) zeroSign++;
}
console.log(`maxK ${maxK}: pool lower ${L.p.count} principal ${P.p.count}; same (left,right) at every index: ${structural === 0} (diffs ${structural}); re mismatches ${reDiff}; im != -im mismatches ${imDiff}; zero-imag sign not mirrored ${zeroSign}`);
console.log("hits lower:", L.r.hits.map((h) => `${h.id}@${h.k}`).join(" "));
console.log("hits principal:", P.r.hits.map((h) => `${h.id}@${h.k}`).join(" "));
console.log(`time lower ${L.ms} ms, principal ${P.ms} ms`);
