# Next Steps Plan (Post-1.0.10 / 2026-11-26)

Every step in [architecture-plan.md](architecture-plan.md) is done, the Lean 4 formalization has been rebuilt on Mathlib over `ℂ`, and the remaining silent-certification, branch-cut note, rebuild-flag, and `exp(3.5×10^(−479)) − 1` limitations from [known-limitations.md](known-limitations.md) are resolved.

This document lists what genuinely remains open, ordered by priority.

## 1. Release 1.0.11
- Review `CHANGELOG.md` under `## Unreleased`, date it as `## 1.0.11`, bump `package.json` and `package-lock.json`, push `main`, verify both `pages` and `Lean 4 Formal Proofs` workflows pass on GitHub Actions, tag `v1.0.11`, and publish the GitHub release.

## 2. Exact Engine & Fuzzing Hygiene
- **Fresh-session press-string rebuilds:** Rebuilding a circuit from a press string in the same session now preserves low-precision, pole, and large-angle flags via the structural registry in `lib/eml/node.ts`. A fresh session loading a raw press string still sees only the gates; if desired, serialize optional note metadata alongside shared press strings or re-infer pole/large-angle notes during exact evaluation.
- **Periodic mpmath fuzz sweeps:** Run `tools/fuzz/` across multiple seeds (e.g. Seeds 1–10) after any change to `exact.ts`, `exact-ball.ts`, `library.ts`, or `facts.ts`, and keep `wireMismatches === 0` and `wrong === 0`.
- **CI test for `tools/minimality/decide.py`:** Add a fast CI check running `python tools/minimality/decide.py 13` (takes ~2 s) so accidental regressions like the dropped helpers in `c072b43` are caught immediately.

## 3. Mathematical / Search Open Problems (No Code Fix Expected)
- **`−2` without `ln 0` at K 27:** Only two K 25 programs remain (`exp(exp(exp(T4/z)))` and `exp(exp(T5/z))`). As documented in [minimality.md](minimality.md), numerical enclosure requires ~10^1656519–10^1656521 bits and standard unconditional transcendence theorems do not apply; both are excluded conditionally under Schanuel's conjecture. Settling this unconditionally requires a new transcendence result.
- **Shorter records past K 41:** `−iπ` (K 45 / K 47 without `ln 0`), `4` (K 39), `2/3` (K 39), `−1/3` (K 41), `−3` (K 35), `1/3` (K 35 / K 37), and scaled subtraction/addition (K 565 / K 655) remain shortest known, not proved minimal.
