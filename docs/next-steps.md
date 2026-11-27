# Next Steps Plan (Post-1.0.12 / 2026-11-26)

Every engineering item in [architecture-plan.md](architecture-plan.md) is done:
- `formal/lean/` is built on Lean 4.28.0 + Mathlib over `ℂ`, `EmlExt`, and `EmlDir` across 15 modules with automatic axiom auditing over all `Eml.*` declarations, proof-carrying circuit certificates (`Eml.Cert`), 100% coverage of all 41 constant records in `lib/eml/best-known.json` (including `-ipi` K 45 and `-ipi-strict` K 47, and the 11 substitution words in `Eml.MoreRecords`; check 112 fails if a stored word has no theorem link), general inverse-trig branch-cut theorems, Raney's Cycle Lemma + Catalan enumeration, unconditional minimality of `0` at K 7, and CI cross-checking of UI theorem links and compiled snippets (`scripts/lean-bridge-check.ts`).
- `tools/minimality/decide.py 13` runs automatically in `.github/workflows/ci.yml`.
- Structural precision/pole/large-angle notes in `lib/eml/node.ts` persist across fresh browser sessions via `localStorage` (`exportPrecisionRegistry` / `importPrecisionRegistry`).

## Ongoing Hygiene
- **Periodic mpmath fuzz sweeps:** Run `tools/fuzz/` across multiple seeds (e.g. Seeds 1–10) after any change to `exact.ts`, `exact-ball.ts`, `library.ts`, or `facts.ts`, and keep `wireMismatches === 0` and `wrong === 0`.

## Mathematical / Search Open Problems (No Code Fix Expected)
- **`−2` without `ln 0` at K 27:** Only two K 25 programs remain (`exp(exp(exp(T4/z)))` and `exp(exp(T5/z))`). As documented in [minimality.md](minimality.md), numerical enclosure requires ~10^1656519–10^1656521 bits and standard unconditional transcendence theorems do not apply; both are excluded conditionally under Schanuel's conjecture. Settling this unconditionally requires a new transcendence result.
- **Shorter records past K 41:** `−iπ` (K 45 / K 47 without `ln 0`), `4` (K 39), `2/3` (K 39), `−1/3` (K 41), `−3` (K 35), `1/3` (K 35 / K 37), and scaled subtraction/addition (K 565 / K 655) remain shortest known, not proved minimal.
