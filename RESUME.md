# Absorb-retry: parked on reviewbot's requested changes

Branch `cursor/gate-absorb-retry-410e`, head was `a84e0e7`. Draft PR #33. Do not merge. No GitHub issue.

Reviewbot requested changes. Confirmed in Chrome against v1.1: this branch certifies values v1.1 does not.

## M1

`absorbRetryCanChangeClaim` (`lib/eml/exact.ts` around 819–845, called around 768–774) gives an exactly-0 component depth +∞ (around 825–827) and `belowStored` true (around 832). A lost term that lands in a zero component never triggers the retry. The comment around 762–765 is wrong.

Repros, v1.1 versus this branch:

- `((1+10^(-130))-1)+i/2` gives 0.5i, shown as a match
- `(i*(1+10^(-130))-i)*i+i/2`
- `((1+10^(-110))-1)+i*10^10/3`
- `((1+10^(-136))-1)+i*3/2` — v1.1 says not certified, this branch certifies
- `k = 124..132` crossed with `c` in `{1/2, 1/3, 3/2, −1/2}`

42 certified-wrong rows out of 1,314 cross-component rows. Reviewbot's corpus tools are on Ben's machine (`/workspace/rv/pr33-tools`); rebuild the rows from these patterns.

## M2

Add all of those as parity rows in `lib/eml/check.ts`. The gate currently skips only 9 of 144 rows.

## Should-fix

The claim that digits past the 40-digit floor are only rounding dust is false. `sin`/`tan(10^22)` stores 94/120 correct digits (v1.1 stores 119/118), and `cos(10^7)` stores 110. Round to the trusted digits, or reword the claim.

## Nits

- `oversizedPressNodeIsRejected` is a test-only export (`exprSeq.ts` around line 556).
- `80_000` is hard-coded in `check.ts` and `countCutDebug.ts`.

## Plan

1. Track the lost term per real and imaginary part, and propagate that through exp, ln, and ×i. Skip the retry only when no component's claim can change.
2. If that brings the retry back for `sin`/`tan(10^22)`, `cos(10^7)`, and `1-cos(sqrt(1/10^130))`, and the speedup disappears, say so and recommend closing #33. Keep v1.1's behaviour.

## Pre-existing v1.1 bug

`(i*(1+10^(-124))-i)*i+i*10^10/3` drops its real part `−10^(−124)` on v1.1 and on this branch. The screen shows `3333333333.33i` and does not mark it not-certified. `lib/eml/check.ts` records this as a known failure: the suite stays green while the real part is missing, and fails once the real part is kept so the skip can be removed. Not introduced by the absorb retry. No GitHub issue.
