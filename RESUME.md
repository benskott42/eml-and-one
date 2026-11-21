# RESUME

WIP hotfix off `d6be0d1`. Exact mode should refuse confidently wrong infinities instead of printing them. Not verified with `tsc`, lint, `eml:check`, or `eml:smoke`.

## Done

- User-facing `+` and `−` (`userAdd` / `userSub` in `lib/eml/library.ts`, used from `lib/eml/parse.ts` and the add/sub button builders) mark the sum unverified when one side is a real ±∞ or a directed infinity and the float circuit does not already show that real infinity. A float NaN is left as undefined. `inf-inf` is unchanged because the two operands are the same node.
- `tLn`, `tDiv`, and `tSqrt` mark an odd-turn directed infinity (∞i or −∞i) unverified. Finite ÷ directed infinity still returns 0. Real ±∞ division and `sqrt(ln(0))` are unchanged.
- `lib/eml/check.ts` expects `ln(0)-1`, `ln(0)+i`, `(inf*i)/2`, and `ln(ln(0)*i)` to be unverified, in process and on the packed fresh-process path.
- A local probe showed those four as unverified in both modes, and kept `inf*i`, `ln(0)*i`, `(inf*i)^3`, `(inf*i)^4`, `(-inf)^2`, `(-inf)^3`, `ln(0)*2`, `ln(0)/2`, `ln(ln(0))`, `1/(inf*i)`, `exp(800)+1`, and `(1+1/0)-1/0`.

## Left

- `ln(0)+0` is wrongly unverified. `tAdd(ln(0), 0)` returns the `ln(0)` node, and `knownValue(ln(0))` is null there, so the sign is treated as unknown even though the float value is −∞. Keep that node when the float value is already the real infinity. Check `ln(0)-0` the same way.
- Run `npx tsc --noEmit`, `npm run lint`, `npm run eml:check`, and `npm run eml:smoke`. There is no `eml:layout` script.
- Do not change directed multiply/power results that are already right (`267555b`, `d6be0d1`). Do not turn `inf-inf` into unverified; the check requires the indeterminate singular.
