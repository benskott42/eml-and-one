# Cut conjugation checkpoint

Branch `cursor/cut-conjugation-410e`, based on `baca175` (v1.1 when this branch was cut). Do not open the PR until the next step below is done. `origin/v1.1` has since moved to `304de9a` (#30 is `df517dd`, then #23). This branch was not rebased.

## Done

- `reducedTrig` rounds exact halves away from zero (`roundHalfAway`), so `round(−x) = −round(x)`. Positive non-halves still match `Math.round`.
- `±∞` keys use the finite sign bit. `+∞` stays `[1, 0]`. `−∞` is `[(1 << 20) | 1, 0]`. `NaN` is `[0, 0]`, not the old shared `[2, 0]`.
- `lowerHitTarget`: a principal hit is the lower-cut hit of the conjugate target. The search always passes `otherCut: false`, because `eml` still returns the lower cut.
- `searchConstants(..., { digest: true })` hashes committed `(re, im)` bits in commit order (FNV-1a, seed `1` excluded). Off unless asked.
- `lib/eml/check.ts` (core shard) locks K=17/19/21/23 pools, hit records, and digests to the `baca175` numbers, including the K=23 `allowLn0: false` `ipi` word `111111E1E1EEE1EE11E1EEE`. Also checks the half-turn `cexp` symmetry, the `±∞` keys, and `lowerHitTarget`.
- That core shard passed. `npm run eml:parity` (K≤29 pool and hits vs the existing fixture) passed on this branch.

## Half-done

Conjugate-pair reuse is not in the tree. A pair cache was tried and removed: at K=23 it had 0 conjugate hits (the pool is not closed under conjugation; only a handful of pairs even have both conjugate children), duplicate float pairs were about 35%, and the cache was slower than calling `eml`. `eml` itself is a small part of K≤23 wall time; exact hit acceptance dominates, and `exact.ts` must not change.

Warm medians on unmodified `baca175`, same machine: K17 76 ms, K19 153 ms, K21 211 ms, K23 232 ms, K23 without ln 0 352 ms. A later timing of this tree, taken while the digest hash still ran on every commit, was a bit slower (K23 median 253 ms). The hash was then taken off the hot path. The retime of that last edit was not collected.

## Next step

Retime this tree (digest off) against those `baca175` medians at K17/19/21/23 and K=23 `allowLn0: false`. Then either find a conjugate reuse that does not regress and still matches the digests, or write up that v1.1 already evaluates only the lower cut and conjugate input pairs do not occur. After that, draft PR into current `v1.1`. Do not start that until asked.
