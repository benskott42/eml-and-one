# Resume

WIP on `cursor/long-literal-wire-a4e8` for the PR #15 review of `0b30506`. This commit merges `origin/v1.1` (`304de9a`) and starts the requested fixes. The suite was still running and was stopped. Do not force-push. Do not rebase.

## Done

The merge conflict was only `lib/eml/check.ts` imports. The resolution keeps `exactShownText` and `import Decimal from "decimal.js"`, and drops the extra `import type { Decimal }`.

1. `lib/eml/exact.ts`. `roundedTail` is gone. A non-plain pasted literal whose span plus 152 digits exceeds 480 says it could not verify, instead of a certified zero. On top of that restore: a zero at the span guard is recomputed at `2 * span + 32` when that fits in 480, and otherwise stays unverified. A pasted decimal longer than 40 digits is kept only when a second precision, 96 digits higher, shows the same 12-digit text, and a magnitude past 480 digits stays unverified.

2. `lib/eml/lowering.ts` `rangeOf`, with a note in `lib/eml/library.ts` `exactRealInput`. A pasted literal whose text is not exactly the stored float is not a known point, so shortcuts do not fold that rounded float. Integers that are marked exact still use their integer range.

3. `domainSubBuild` again folds a small integer difference only when an operand is outside the safe integer range. A local probe packed `7-3` as 32 wire tokens. `lib/eml/check.ts` asserts that length.

4. `README.md` and `docs/known-limitations.md`. Removed the claims that `1e-433` / `10^(−433)` cannot be verified, that every exact 0 times a finite factor stays certified, that `6.103*10^(−120)i` added to itself shows half the sum, and that `tan(10^(−5000))` and `exp(10^(−1000))−1` cannot be verified. Documented the pasted-literal limits: 4,000 digits, the rounded float is not the exact value, and arithmetic that needs more than 480 digits says it could not verify.

5. `.github/workflows/ci.yml`. `1, 1, EML` is pressed once, after `CalculatorView` marks the screen `data-ready="1"`. The wait for that marker is at most 40 tries. The screen showing `0` does not cause another press.

6. `lib/eml/check.ts` rows, not yet run to completion on this tree: `sqrt`, `sin`, and the square of the 41-digit pasted `1.000…1`; the same values written as powers; the 200-digit square; `sin` of the 200-digit case unverified; `A−1` at 479 and 480 digits unverified; 479 nines times 2 minus 2 unverified; the 329-digit square unverified; `1/A−1+(A−1)` at 299 digits unverified.

Local probes, not a full suite, matched those screen texts. `tsc --noEmit` passed before the last magnitude check in `exact.ts`. eslint passed on the edited files before that same check. `eml:check` core was killed mid-run. Isolate, props, smoke, and CI were not run. The killed run had loaded an earlier tree, without the magnitude check or the 299-digit row.

## Left from the review

- Re-run `tsc`, eslint, `eml:check` for `core`, `isolate`, and `props`, `eml:smoke`, and the checks the merged workflow runs: `eml:parity`, `program-id:check`, `load-bits:smoke`, `count-check`, the production build, and headless Chrome. Confirm `1, 1, EML` shows `2.71828182846` after the ready marker, and that a press after the keys are live is not repeated.
- Watch CI on the pushed head. The pull request still describes the previous head.
- Leave `(1e−400)/2·2−(1e−400)` alone. Do not merge the other open exact-mode branch.
