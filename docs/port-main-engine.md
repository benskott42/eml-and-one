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

## Status after the 2026-11-23 audit

main's 47 release rows were run on v1.1 and every disputed value was checked against mpmath (200 digits).

**Ported** (rows in `lib/eml/check-port.ts`, isolate shard):
- The huge-sum marker walk covers the whole DAG: (10^400+i)·2 and 2·(10^400+π) are refused.
- 0 × a finite value past float range is exactly 0. exp(800)·0 was certified −∞; there is a new `isFiniteOverflow` mark in lowering.ts.
- A lifted tiny sum sizes its cancellation. 1e−320·(1+1e−100) − 1e−320 was certified 1.00000003×10^−420. `shellLoss` in exact.ts now raises precision to gap + 48, or marks the result not certified past the cap.

**Not needed on v1.1**, because v1.1's engine already returns the mpmath value, so main's refusal would only lose a correct answer:
- Huge trig angles: −cos(1e119), cos(1e119)+1, cos(1e125)·cos(1e130), tan(1e140)+1, cos(2^400)+1, sin(1e22)+1.
- Tiny parts beside i/2: ((1+1/10^130)−1)+i/2, ((1+exp(−299.3))−1)+i/2, (exp(exp(−300))−1)+i/2, ((1+exp(−300))−1)·i+1/2.
- Series differences: sinh(1e−7)−1e−7, artanh(1e−7)−1e−7, sinh(5e−7)−5e−7, sinh(1e−7·i)−1e−7·i.

**Already flagged by v1.1** (`notCertified: absorbed`, shown as not certified, not a wrong value): ((1+10^−500)−1)+i/2, and ((1+10^−136)−1)+i·3/2. An improvement would be to raise precision for the 10^−136 case, which is inside the 480-digit cap, instead of only flagging it. 10^−130 beside i·3/2 already resolves.

**Open decisions, not bugs:** 0^0, (1−1)^0 and 0^(1−1) give 1 on v1.1 (the IEEE pow convention); main says undefined. tanh(130) displays 1, which is right to 12 digits (1 − 2.4×10^−113); main refuses it. exp(800)−exp(800) is unverified on v1.1, where main gives 0.

**Formatting only:** v1.1 shows 12 significant digits (1.57079632679), main 12 decimals (1.570796326795). The values agree.
