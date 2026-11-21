import { searchConstants, setAuditPrincipal, AUDIT_POOL } from "./lib/eml/golf";
const maxK = Number(process.argv[2] ?? 21);
function run(principal: boolean) {
  setAuditPrincipal(principal);
  searchConstants(maxK);
  return { re: AUDIT_POOL.re.slice(0, AUDIT_POOL.count), im: AUDIT_POOL.im.slice(0, AUDIT_POOL.count), left: AUDIT_POOL.left.slice(0, AUDIT_POOL.count), right: AUDIT_POOL.right.slice(0, AUDIT_POOL.count), count: AUDIT_POOL.count };
}
const L = run(false), P = run(true);
const n = Math.min(L.count, P.count);
let shown = 0;
for (let i = 0; i < n && shown < 6; i++) {
  const same = L.left[i] === P.left[i] && L.right[i] === P.right[i] && L.re[i] === P.re[i] && L.im[i] === -P.im[i];
  if (!same) {
    shown++;
    console.log(`idx ${i}: lower (${L.left[i]},${L.right[i]}) ${L.re[i]} ${L.im[i]} | principal (${P.left[i]},${P.right[i]}) ${P.re[i]} ${P.im[i]}`);
    for (const j of [L.left[i], L.right[i]]) console.log(`    operand ${j}: lower ${L.re[j]} ${L.im[j]} principal ${P.re[j]} ${P.im[j]}`);
  }
}
