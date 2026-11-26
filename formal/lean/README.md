# Machine-Checked Lean 4 + Mathlib Formalization (`formal/lean/`)

This directory contains a concrete Lean 4 (`v4.28.0`) + Mathlib (`v4.28.0`) formalization of **EML and One** over `ℂ`, with zero `sorry` and zero custom axioms. Every main theorem is audited by [`AxiomCheck.lean`](AxiomCheck.lean) to depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

> **Note on the earlier Lean 4.14 axiomatic version:** An earlier formalization in this directory used abstract uninstantiated typeclasses without Mathlib. Its `EmlExtendedModel` was inconsistent and collapsed to `1 = 0` (`sub_self(negInf)` vs. `sub_negInf` gave `posInf = zero`, `ln_posInf` and `ln_zero` then gave `negInf = zero`, and `exp_negInf` with `exp_zero` gave `one = zero`), its `Transcendental` proofs were tautologies over `cos_def` axioms rather than `eml` words, and `RotSub` assumed `raw(b, b) = unwind(b)` without modeling the rotation into the strip. That entire axiomatic layer has been replaced with concrete Mathlib definitions over `ℂ` and an honest inductive type `EmlExt`.

## What is proved

### Core operator & branch cut ([`Eml/Basic.lean`](Eml/Basic.lean))

The operator is defined concretely over `ℂ` as `eml x y := Complex.exp x - lowerLog y`, where `lowerLog` is the lower-cut logarithm (`Arg ∈ [-π, π)`): equal to Mathlib's principal `Complex.log` off the negative real axis `(-∞, 0)` and equal to `Complex.log z - 2πi` on it.

- `lowerLog_eq_log_of_not_isNegReal`, `lowerLog_eq_log_sub_of_isNegReal` — exact relation between `lowerLog` and Mathlib's `Complex.log`.
- `lowerLog_im_mem` — `(lowerLog z).im ∈ [-π, π)` for all `z : ℂ`.
- `exp_lowerLog` — `Complex.exp (lowerLog z) = z` for `z ≠ 0`.
- `lowerLog_exp` — `lowerLog (Complex.exp z) = z` for `-π ≤ z.im` and `z.im < π`.
- `lowerLog_exp_eq_sub_unwind` — `lowerLog (Complex.exp z) = z - 2πi · κ_L(z)` for all `z : ℂ`, where `κ_L(z) = ⌊(z.im + π) / (2π)⌋` (Corless–Jeffrey unwinding number on the lower cut).
- `log_exp_eq_sub_principalUnwind` — `Complex.log (Complex.exp z) = z - 2πi · κ(z)` for all `z : ℂ`, where `κ(z) = ⌈(z.im - π) / (2π)⌉`.
- `cE_eq_exp_one` — `eml 1 1 = Complex.exp 1`.
- `cZero_eq_zero` — `eml 1 (eml (eml 1 1) 1) = 0` (K = 7 word `0x74`).
- `emlExp_eq` — `eml x 1 = Complex.exp x` for all `x : ℂ`.
- `emlLn_eq_log` — `eml 1 (eml (eml 1 x) 1) = Complex.log x` for all `x : ℂ` (in particular, the composed K = 7 logarithm is unconditionally the *principal* logarithm for every `x ≠ 0`, matching the top-level README).
- `append0xc_eq` — `eml x (eml 1 1) = Complex.exp x - 1` for all `x : ℂ`.
- `rawSub_eq_sub_add_unwind` — `rawSub a b = a - b + 2πi · κ_L(b)` for `a ≠ 0` and all `b : ℂ`.
- `rawSub_eq` — `rawSub a b = a - b` for `a ≠ 0` and `-π ≤ b.im < π`.
- `eml_zero_exp` — `eml cZero (emlExp x) = 1 - x` for `-π ≤ x.im < π`.

### Arithmetic words over `ℂ` ([`Eml/Arithmetic.lean`](Eml/Arithmetic.lean))

Every operation is defined as its actual `eml` word from `docs/rotsub.md` and `lib/eml/best-known.json` (no `ln 0`):

- `emlMul_eq` (K = 17 word `1111xEE1EEyE1EE1E`) — `emlMul a b = a * b` for `a ≠ 0`, `b ≠ 0`, `a ≠ exp(exp 1)` (no strip condition).
- `emlDiv_eq` (K = 17 word `111yEE1EE1xE1EE1E`) — `emlDiv a b = a / b` for `a ≠ 0`, `b ≠ 0`, `b ≠ exp(exp 1)` (no strip condition).
- `emlInv_eq` (`emlDiv 1 x`) — `emlInv x = x⁻¹` for `x ≠ 0`, `x ≠ exp(exp 1)`.
- `emlSqr_eq` (K = 17 word `1111xEE1EExE1EE1E`) — `emlSqr x = x ^ 2` for `x ≠ 0`, `x ≠ exp(exp 1)`.
- `emlAdd_eq` (K = 19 word `1111y1EEE1EEx1EE1EE`) — `emlAdd a b = a + b` for `eml 1 (emlExp b) ≠ 0` and `-π < (a + b).im ≤ π`.

### Rotated subtraction ([`Eml/RotSub.lean`](Eml/RotSub.lean) and [`Eml/Extended.lean`](Eml/Extended.lean))

Constructed genuinely as `rotSub c a b = emlDiv (rawSub (emlMul c (rawSub a b)) (emlMul c (rawSub b b))) c` (`docs/rotsub.md`):

- `rawSub_self_eq_unwind` — `rawSub b b = 2πi · κ_L(b)` for `b ≠ 0`.
- `mul_unwind_im_zero` — multiplying `2πi · k` by any purely imaginary `c` (`c.re = 0`) yields a real number (`Im = 0`), placing the inner subtrahend strictly inside the lower strip `[-π, π)`.
- `rotSub_eq_sub` (pure `ℂ`, no `ln 0`) — `rotSub c a b = a - b` for any `c` with `c.re = 0`, `c ≠ 0`, and any `a, b : ℂ` with `a ≠ 0`, `b ≠ 0`, `a ≠ b`, `κ_L(b) ≠ 0`, and `a - b + 2πi · κ_L(b) ≠ 0`.
- `extRotSub_eq_sub` (in `Eml/Extended.lean`, over `EmlExt`) — `extRotSub (.finite c) (.finite a) (.finite b) = .finite (a - b)` for any `c` with `c.re = 0`, `c ≠ 0`, and **all** `a, b : ℂ`, covering all `ln 0 = -∞` paths (`κ_L(b) = 0`, `a = 0`, `a = b`, `r1 = 0`, `b = 0`, and `x = e^e`).

### Concrete `ln 0`-free constant records over `ℂ` ([`Eml/Records.lean`](Eml/Records.lean))

Direct RPN stack evaluations `evalRpn (1 : ℂ) eml bits [] = some [v]` on the exact bitstrings from `lib/eml/best-known.json` and `tools/minimality/decide.py`:

- `evalRpn_negOne_strict` — `11111EEE1EE11E1EE` (K = 17) → `-1`.
- `evalRpn_two` — `111111EEE1EE11EE1EE` (K = 19, `0x7e264`) → `2`.
- `evalRpn_ipi_strict` — `111111E1E1EEE1EE11E1EEE` (K = 23) → `+iπ` on the lower cut (genuinely distinguishes `lowerLog` from Mathlib's principal `Complex.log`).
- `evalRpn_ln2` — `11111111EEE1EE11EE1EEE1EE` (K = 25, `0x1fe2644`) → `Complex.log 2`.
- `evalRpn_three` — `11111111EEE1EE11EEE1EE11EE1EE` (K = 29, `0x1fe26264`) → `3`.

### Phase-free extended domain & `ln 0` records ([`Eml/Extended.lean`](Eml/Extended.lean))

Models `ℂ ∪ {+∞, -∞, NaN}` as a concrete inductive type `EmlExt` (zero axioms; indeterminate forms such as `∞ - ∞` and `ln (-∞)` map to `EmlExt.nan`):

- `extEmlMul_eq` (`a ≠ 0`, all `b : ℂ`, including `b = 0` and `a = e^e`), `extEmlDiv_eq` (`b ≠ 0`, all `a : ℂ`, including `a = 0` and `b = e^e`), `extRawSub_eq` (all `a, b : ℂ`), `extRotSub_eq_sub` (all `a, b : ℂ`, nonzero purely imaginary `c`).
- `evalRpn_0x7d0` (K = 11) → `EmlExt.negInf` (`-∞`).
- `evalRpn_0x7d0c` (K = 15) → `EmlExt.finite (-1)`.
- `evalRpn_0x1fa1a8` (K = 21) → `EmlExt.finite (π * I)` (lower cut).
- `evalRpn_0x1fa1a8c` (K = 25) → `EmlExt.finite (-2)` (lower cut).

### Transcendental `eml` words ([`Eml/Transcendental.lean`](Eml/Transcendental.lean))

Built genuinely from `eml` and `1` (no `ln 0`):

- `emlPow_eq` (`emlExp (emlMul y (emlLn x)) = x ^ y`) for `x ≠ 0`, `Complex.log x ≠ 0`, `y ≠ 0`, `y ≠ exp(exp 1)`.
- `emlSqrt_eq` (`emlExp (emlDiv (emlLn x) cTwo) = x ^ (1/2)`) for `x ≠ 0`, `Complex.log x ≠ 0`.
- `emlLogBase_eq` (`emlDiv (emlLn x) (emlLn b) = Complex.log x / Complex.log b`) for `Complex.log x ≠ 0`, `Complex.log b ≠ 0`, `Complex.log b ≠ exp(exp 1)`.

### Binary encoding, syntax trees & RPN soundness

- [`Eml/Binary.lean`](Eml/Binary.lean) — Pure inductive proofs of Dyck-prefix validity (`valid_one`, `valid_e`, `valid_zero`, `valid_append_0xc`, `valid_eml_combine`, `valid_program_starts_true`, `valid_program_odd_length`, `evalRpn_append_0xc`).
- [`Eml/TreeBijection.lean`](Eml/TreeBijection.lean) — Pure inductive proofs of `EmlTree` compilation (`toRpn_valid`, `toRpn_length`, `evalRpn_toRpn`, `toRpn_injective`).
- [`Eml/RpnSoundness.lean`](Eml/RpnSoundness.lean) — Stack-depth soundness (`evalRpn_some_of_runDepth`, `valid_program_evals_singleton`) and concrete RPN stack proofs over `ℂ` (`evalRpn_0x1`, `evalRpn_0x6`, `evalRpn_0x74`, `evalRpn_append_0xc_value`).

## What is NOT formalized

- **Minimality proofs / lower bounds** (e.g. excluding all shorter programs for `0`, `-1`, `2`, `+iπ`, `-2`): these remain computer-assisted interval/tower certificates in `tools/minimality/`.
- **Directed infinities** needed for `b = 0` on the *scaled* subtraction circuit (`sub(5, 0)`, `add(5, 0)` in `docs/rotsub.md`): `EmlExt` models the phase-free extended domain (`ℂ ∪ {+∞, -∞, NaN}`), which suffices for unscaled `rotSub` and all `ln 0` constant records, but does not track phases on infinities.
- **Circular and hyperbolic functions (`cos`, `sin`, `cosh`, `sinh`)**: dropped from `Eml/Transcendental.lean` because the earlier version did not express them as `eml` words (and `i` in `best-known.json` uses `ln 0`).
- **Floating-point error bounds / exact-mode precision thresholds**: numerical properties in `docs/rotsub.md` and `docs/known-limitations.md` are not formalized.

## Building and auditing locally

With [elan](https://github.com/leanprover/elan) installed:

```bash
cd formal/lean
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

Every push or pull request touching `formal/lean/` or `.github/workflows/lean.yml` runs `lake exe cache get`, `lake build`, and the `AxiomCheck.lean` axiom audit in CI.
