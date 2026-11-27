# Next Steps Plan (Post-1.0.12 / 2026-11-26)

Every engineering item in [architecture-plan.md](architecture-plan.md) is done:
- `formal/lean/` is built on Lean 4.28.0 + Mathlib over `ℂ`, `EmlExt`, and `EmlDir` across 15 modules with automatic axiom auditing over all `Eml.*` declarations, proof-carrying circuit certificates (`Eml.Cert`), 100% coverage of all 45 constant records in `lib/eml/best-known.json` (including `-ipi` K 45 and `-ipi-strict` K 47, and the 11 substitution words in `Eml.MoreRecords`; check 112 fails if a stored word has no theorem link), general inverse-trig branch-cut theorems, Raney's Cycle Lemma + Catalan enumeration, unconditional minimality of `0` at K 7, and CI cross-checking of UI theorem links and compiled snippets (`scripts/lean-bridge-check.ts`).
- `tools/minimality/decide.py 13` runs automatically in `.github/workflows/ci.yml`.
- Structural precision/pole/large-angle notes in `lib/eml/node.ts` persist across fresh browser sessions via `localStorage` (`exportPrecisionRegistry` / `importPrecisionRegistry`).

## Ongoing Hygiene
- **Periodic mpmath fuzz sweeps:** Run `tools/fuzz/` across multiple seeds (e.g. Seeds 1–10) after any change to `exact.ts`, `exact-ball.ts`, `library.ts`, or `facts.ts`, and keep `wireMismatches === 0` and `wrong === 0`.

## Engineering Next (2026-11-27 review)

1. **Ball arithmetic as the exact engine** ([design/ball-engine.md](design/ball-engine.md), design only). The point engine's certification is a stack of heuristics (raise, re-read, scrub, snap, refuse), and each fuzz round has found an input between them. Balls prove digits by construction. Migrate in stages behind the golden gate, with the nightly fuzz (now checking each part) as the net.
2. **Exact-engine speed.** `(−5 − 10^(−300) i) − (10^(−236) + 10^(−236) i)` is a 404-gate circuit and takes about 14 s: three full re-reads at 357, 456, and 480 digits from `hiddenComponent`, `refusedResult`, and `squaredTinyPart`. Item 1 replaces those passes with one adaptive loop.
3. **Link the compiler's own circuits to Lean.** The app compiles `x − y` to a K 565 word of the same shape as `Eml.DirectedInf.dirScaledSub` (`k · rotSub(iπ, x/k, y/k)`, `k = √(y²) + 1`), but its sub-words (the square root, the division by `k`) are spelled differently from the Lean definitions. Define the Lean side to spell the app's word exactly, add an `evalRpn` over `{1, x, y, E}`, and prove that word computes `a − b` for all `a, b` (directed infinities included); then do `+`, `·`, `÷`. The bridge compares the TypeScript word with the Lean list.
4. **A richer certificate language.** `Eml.Cert.certify` certifies 0, 2, 3, 4, e, e², ln 2 and strict 1/e by kernel computation. The ±1/2, ±1/3 and ±3/2 words pass through `c · e^e` and `exp(−ln c) = 1/c`, which `Sym` cannot express. Add rational scaling (and its `exp`/`ln` rules) in Lean and `leanCert.ts` together; the bridge already cross-checks the two on 237 programs.

## Mathematical / Search Open Problems (No Code Fix Expected)
- **`−2` without `ln 0` at K 27:** Only two K 25 programs remain (`exp(exp(exp(T4/z)))` and `exp(exp(T5/z))`). As documented in [minimality.md](minimality.md), numerical enclosure requires ~10^1656519–10^1656521 bits and standard unconditional transcendence theorems do not apply; both are excluded conditionally under Schanuel's conjecture. Settling this unconditionally requires a new transcendence result.
- **Shorter records past K 41:** `−iπ` (K 45 / K 47 without `ln 0`), `4` (K 39), `2/3` (K 39), `−1/3` (K 41), `−3` (K 35), `1/3` (K 35 / K 37), and scaled subtraction/addition (K 565 / K 655) remain shortest known, not proved minimal.
