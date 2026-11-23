# Porting main's exact-engine fixes to v1.1

`main` (1.0.1, 1.0.2) and `v1.1` fixed exact mode with two different engines. The merge of main into v1.1 (2026-11-23) brought over the UI fixes, the records and tools, the atanh/arctan branch formulas, the record-certifier hardening, ln(1±x) tracking, and 0·finite = 0. It kept **v1.1's engine**: `lib/eml/exact.ts`, `check.ts`, the scaled tiny sums in `lowering.ts`, and v1.1's infinity-sign model in `library.ts`. main's engine rules below are not active on v1.1 yet. Port them one at a time onto v1.1's engine, each with its row from main's `lib/eml/check.ts` (git show origin/main:lib/eml/check.ts, the `release refusal` and `release kept` blocks).

Not yet active on v1.1:

- **Refusals (1.0.1 b08814d and others).** Huge trig angles anywhere below the root (−cos(1e119), cos(1e119)+1); a part cancelled to 0 beside a nonzero part ((1+10^-500)−1)+i/2. When porting that one, use 1.0.2's per-component tiny channels, not the 1.0.1 rule that refused 10^400/7. Also: a finite result far below an overflowed operand ((exp(800)+1)−exp(800), exp(800)·0); tanh past 100; the sinh/artanh/arcsin series zeros. Most of these depend on marks the merge carries but v1.1's exact.ts does not read: `isExactUnsure` (xu on the wire), `isLostTiny` (cap), and `isLiftedCombine` (lc).
- **Lifted tiny sums (6704f98, 2c5db2f, 3a1329f).** main lifts by 10^k with liftBy/dropBy and sizes the cancellation from the lc mark (liftedGap in exact.ts). v1.1 keeps tenPow scaling.
- **Huge-sum marker walk (1.0.2 90c3eb9).** `hidesBeside` in exact.ts must walk the whole DAG, or (10^400+i)·2 is certified as 2×10^400.
- **Directed infinities (#22, #26, #32).** main's quarter-turn model (rememberDirection) for ∞i, (∞i)^3, ln(0)·2. v1.1 has its own infinity-sign model; port only the behaviors its tests lack.
- **Folds.** exp(−1000)+exp(−1000) = 2·exp(−1000), (−x)+x = 0 for past-cap x, and 0 + underflow = underflow. These must respect v1.1's series-shortcut guard: E3/E5 in v1.1's check.ts.
- **Float trig of ±∞ = undefined.** v1.1 expects "couldn't verify" (E3 item 6). Reconcile before porting.
- **Display rule (1.0.2).** A small component no longer prints extra digits when places 13–14 are 0 (formatDec hiddenTail looksRound).
- **eml:golden.** The harness and corpus came over, but golden.txt was recorded on main's engine. Regenerate it on v1.1 (`npm run eml:golden -- --update`, a reason per changed line) before wiring it into v1.1's CI.
