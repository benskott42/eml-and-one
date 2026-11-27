# Machine-Checked Lean 4 + Mathlib Formalization (`formal/lean/`)

This directory contains a concrete Lean 4 (`v4.28.0`) + Mathlib (`v4.28.0`) formalization of **EML and One** over `ℂ`, with zero `sorry` (`warningAsError := true` on `lean_lib Eml`) and zero custom axioms. Every declaration across all 14 modules (696 declarations) is automatically audited by [`AxiomCheck.lean`](AxiomCheck.lean) to depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and [`scripts/lean-bridge-check.ts`](../../scripts/lean-bridge-check.ts) verifies in CI that every UI theorem link, every `Eml.Cert.certify` mirror check, and sample `Copy Lean 4` snippets typecheck in Lean 4.

> **Note on the earlier Lean 4.14 axiomatic version:** An earlier formalization in this directory used abstract uninstantiated typeclasses without Mathlib. Its `EmlExtendedModel` was inconsistent and collapsed to `1 = 0` (`sub_self(negInf)` vs. `sub_negInf` gave `posInf = zero`, `ln_posInf` and `ln_zero` then gave `negInf = zero`, and `exp_negInf` with `exp_zero` gave `one = zero`), its `Transcendental` proofs were tautologies over `cos_def` axioms rather than `eml` words, and `RotSub` assumed `raw(b, b) = unwind(b)` without modeling the rotation into the strip. That entire axiomatic layer has been replaced with concrete Mathlib definitions over `ℂ`, an honest inductive phase-free extended domain `EmlExt`, and a concrete directed-infinity + signed-zero domain `EmlDir`.

## What is proved

### Core operator & branch cut ([`Eml/Basic.lean`](Eml/Basic.lean))

The operator is defined concretely over `ℂ` as `eml x y := Complex.exp x - lowerLog y`, where `lowerLog` is the lower-cut logarithm (`Arg ∈ [-π, π)`): equal to Mathlib's principal `Complex.log` off the negative real axis `(-∞, 0)` and equal to `Complex.log z - 2πi` on it.

- `lowerLog_eq_log_of_not_isNegReal`, `lowerLog_eq_log_sub_of_isNegReal`, `lowerLog_im_mem` (`-π ≤ (lowerLog z).im < π`), `exp_lowerLog` (`z ≠ 0`), `lowerLog_exp` (`-π ≤ z.im < π`).
- `lowerLog_exp_eq_sub_unwind` — `lowerLog (Complex.exp z) = z - 2πi · κ_L(z)` for all `z : ℂ`, where `κ_L(z) = ⌊(z.im + π) / (2π)⌋` (Corless–Jeffrey unwinding number on the lower cut).
- `log_exp_eq_sub_principalUnwind` — `Complex.log (Complex.exp z) = z - 2πi · κ(z)` for all `z : ℂ`, where `κ(z) = ⌈(z.im - π) / (2π)⌉`.
- `cE_eq_exp_one` (`eml 1 1 = exp 1`), `cZero_eq_zero` (K = 7 word `0x74`), `emlExp_eq` (`eml x 1 = exp x`), `emlLn_eq_log` (K = 7 `emlLn x = Complex.log x`, unconditionally the principal logarithm for all `x ≠ 0`; at `x = 0` it agrees with Mathlib's junk value `Complex.log 0 = 0`, whereas `Eml.Extended.extEmlLn_zero` models `ln 0 = -∞`), `append0xc_eq` (`eml x (eml 1 1) = exp x - 1`), `rawSub_eq_sub_add_unwind`, `rawSub_eq`, and `eml_zero_exp`.

### Arithmetic words over `ℂ` ([`Eml/Arithmetic.lean`](Eml/Arithmetic.lean))

Every operation is defined as its actual `eml` word from `docs/rotsub.md` and `lib/eml/best-known.json` (no `ln 0`):

- `emlMul_eq` (K = 17 word `1111xEE1EEyE1EE1E`) — `emlMul a b = a * b` for `a ≠ 0`, `b ≠ 0`, `a ≠ exp(exp 1)`.
- `emlDiv_eq` (K = 17 word `111yEE1EE1xE1EE1E`) — `emlDiv a b = a / b` for `a ≠ 0`, `b ≠ 0`, `b ≠ exp(exp 1)`.
- `emlInv_eq` (`emlDiv 1 x`), `emlSqr_eq` (K = 17 `1111xEE1EExE1EE1E`), `emlAdd_eq` (K = 19 `1111y1EEE1EEx1EE1EE` for `eml 1 (emlExp b) ≠ 0` and `-π < (a + b).im ≤ π`).

### Rotated subtraction & directed infinities ([`Eml/RotSub.lean`](Eml/RotSub.lean), [`Eml/Extended.lean`](Eml/Extended.lean), [`Eml/DirectedInf.lean`](Eml/DirectedInf.lean))

- `Eml/RotSub.lean` (pure `ℂ`, no `ln 0`): proves `rawSub_self_eq_unwind` (`rawSub b b = 2πi · κ_L(b)`), `mul_unwind_im_zero` (`(c · 2πi · k).im = 0` for `c.re = 0`), and `rotSub_eq_sub` for any nonzero purely imaginary `c` (`c.re = 0`, `c ≠ 0`) and `a, b : ℂ` with `a ≠ 0`, `b ≠ 0`, `a ≠ b`, `κ_L(b) ≠ 0`, and `a - b + 2πi · κ_L(b) ≠ 0`.
- `Eml/Extended.lean` (phase-free `EmlExt`): proves `extRotSub_eq_sub` for any nonzero purely imaginary `c` (`c.re = 0`, `c ≠ 0`) and **all** `a, b : ℂ` (covering `κ_L(b) = 0`, `a = 0`, `a = b`, `r1 = 0`, `b = 0`, `x = e^e`).
- `Eml/DirectedInf.lean` (scaled subtraction `k = 1 + √(b²)`, `k · rotSub c (a/k) (b/k)` from `docs/rotsub.md`, built purely from `extEml`/`dirEml` and `.finite 1` with zero smuggled constants):
  - In phase-free `EmlExt`: proves `extScaledSubRot_eq_sub` for any nonzero purely imaginary `c` (`c.re = 0`, `c ≠ 0`) and all `a, b : ℂ` with `b ≠ 0` (including `Re(1 + √(b²)) ≥ 1` so `k ≠ 0`), `extEmlSqr_zero : extEmlSqr (.finite 0) = .finite 0`, AND the **negative result** `extEmlSqrt_zero : extEmlSqrt (.finite 0) = .nan` and `extScaledSubRot_zero : extScaledSubRot (.finite c) (.finite a) (.finite 0) = .nan`, confirming why phase-free infinities cannot handle `b = 0` on the scaled path.
  - In `EmlDir` (concrete inductive type with directed infinities `posInf im | negInf im | dirInf θ` and signed zero `negZero`, implementing `exp(-∞ ± iπ) = -0`, `exp(+∞ + iθ) = ∞·e^{iθ}`, `ln(-∞) = +∞ - iπ`, `ln(-0) = -∞ - iπ`): proves `dirEmlSqrt_zero : dirEmlSqrt (.finite 0) = .finite 0` and `dirScaledSub_eq_sub` for any nonzero purely imaginary `c` (`c.re = 0`, `c ≠ 0`) and **all** `a, b : ℂ`, **including `b = 0`**.

### Concrete `ln 0`-free constant records over `ℂ` ([`Eml/Records.lean`](Eml/Records.lean))

Direct RPN stack evaluations `evalRpn (1 : ℂ) eml bits [] = some [v]` on the exact bitstrings from `lib/eml/best-known.json`:

- `evalRpn_negOne_strict` — `11111EEE1EE11E1EE` (K = 17) → `-1`.
- `evalRpn_two` — `111111EEE1EE11EE1EE` (K = 19, `0x7e264`) → `2`.
- `evalRpn_ipi_strict` — `111111E1E1EEE1EE11E1EEE` (K = 23) → `+iπ` on the lower cut (genuinely distinguishes `lowerLog` from `Complex.log`).
- `evalRpn_ln2` — `11111111EEE1EE11EE1EEE1EE` (K = 25, `0x1fe2644`) → `Complex.log 2`.
- `evalRpn_three` — `11111111EEE1EE11EEE1EE11EE1EE` (K = 29, `0x1fe26264`) → `3`.
- `evalRpn_negThree` — `11111111EEE1EE11EE1EEE11E1E1EEE11EE` (K = 35) → `-3`.
- `evalRpn_four` — `1111111111EEE1EE11EEE1EE11EEE1EE11EE1EE` (K = 39) → `4`.
- `evalRpn_twoThirds` — `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE1E` (K = 39) → `2/3`.
- `evalRpn_negThird` — `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE11EE` (K = 41) → `-1/3`.
- `evalRpn_half_strict` (K = 31) → `1/2`, `evalRpn_negHalf_strict` (K = 31) → `-1/2`, `evalRpn_half_alt` (K = 31) → `1/2`, `evalRpn_third_strict` (K = 37) → `1/3`, `evalRpn_sqrt2` (K = 61) → `√2`.

### Extended-domain (`ln 0 = -∞`) RPN constant records ([`Eml/Extended.lean`](Eml/Extended.lean))

Direct RPN stack evaluations `evalRpn (EmlExt.finite 1) extEml bits [] = some [v]`:

- `evalRpn_0x7d0` (K = 11) → `EmlExt.negInf` (`-∞`).
- `evalRpn_0x7d0c` (K = 15) → `EmlExt.finite (-1)`.
- `evalRpn_0x1fa1a8` (K = 21) → `EmlExt.finite (π * I)` (lower cut).
- `evalRpn_0x1fa1a8c` (K = 25) → `EmlExt.finite (-2)` (lower cut).
- `evalRpn_half` (K = 29) → `EmlExt.finite (1 / 2)`.
- `evalRpn_negHalf` (K = 29) → `EmlExt.finite (-1 / 2)`.
- `evalRpn_third` (K = 35) → `EmlExt.finite (1 / 3)`.
- `evalRpn_i` (K = 57) → `EmlExt.finite Complex.I`.
- `evalRpn_pi` (K = 93) → `EmlExt.finite Real.pi` (and `extCPi_eq_pi` via `extEmlDiv extCIpi extCI`).

### Genuine `eml`-word transcendental, circular, hyperbolic & logistic functions ([`Eml/Transcendental.lean`](Eml/Transcendental.lean))

Every function is built solely from `eml` / `extEml` and `1` (using `cTwo`/`extCTwo` K 19 and `extCI` K 57):

- Pure `ℂ` (`ln 0`-free): `emlPow_eq` (`x ^ y`), `emlSqrt_eq` (`x ^ (1/2)`), `emlLogBase_eq` (`log x / log b`).
- Extended `EmlExt` (all `x : ℂ`, zero strip restrictions): `extEmlNeg_eq` (`-x`), `extEmlAddRot_eq` (`a + b`), `extEmlCosh_eq` (`Complex.cosh x`), `extEmlSinh_eq` (`Complex.sinh x`), `extEmlTanh_eq` (`Complex.tanh x` for `cosh x ≠ 0`), `extEmlSigma_eq` (`(1 + exp(-x))⁻¹` for `1 + exp(-x) ≠ 0`), `extEmlCos_eq` (`Complex.cos x`), `extEmlSin_eq` (`Complex.sin x`), `extEmlTan_eq` (`Complex.tan x` for `cos x ≠ 0`), `extEmlPow_eq` (`x ^ y` for `x ≠ 0, y ≠ 0`), `extEmlLogBase_eq` (`log x / log b` for `b ≠ 0, x ≠ 0, log b ≠ 0`).

### Inverse trig & inverse hyperbolic `eml` words & branch cuts ([`Eml/InverseTrig.lean`](Eml/InverseTrig.lean))

Built purely from `extEml` and `.finite 1` (zero smuggled constants):

- `extEmlArtanh_eq`, `tanh_artanh`, and branch-cut theorem `extEmlArtanh_ofReal_gt_one` (`x > 1 → artanh(x) = ½ ln((x+1)/(x-1)) - iπ/2`, matching `mpmath` and `README.md`).
- `extEmlArctan_eq`, `tan_arctan`, and `extEmlArctan_neg_two_I` (`arctan(-2i) = -π/2 - (½ ln 3)i`).
- `extEmlArsinh_eq` / `sinh_arsinh`, `extEmlArcosh_eq` / `cosh_arcosh`, `extEmlArcsin_eq` / `sin_arcsin`, `extEmlArccos_eq` / `cos_arccos`, and `extEmlArccos_two` (`arccos(2) = i · ln(2 + √3)`).

### Binary encoding, Raney's Cycle Lemma, Catalan counting & `0` minimality

- [`Eml/Binary.lean`](Eml/Binary.lean) — Pure inductive proofs of Dyck-prefix validity (`valid_one`, `valid_e`, `valid_zero`, `valid_append_0xc`, `valid_eml_combine`, `valid_program_starts_true`, `valid_program_odd_length`, `evalRpn_append_0xc`).
- [`Eml/TreeBijection.lean`](Eml/TreeBijection.lean) — Full bijection `treeEquivValidProgram : EmlTree ≃ { p : List Bool // IsValidProgram p }` (`toRpn_valid`, `toRpn_length`, `evalRpn_toRpn`, `toRpn_injective`, `fromRpn`, `toRpn_fromRpn`, `fromRpn_toRpn`, `evalRpn_eq_eval_fromRpn`).
- [`Eml/CycleLemma.lean`](Eml/CycleLemma.lean) — **Raney's Cycle Lemma** (`raney_cycle_lemma`: every bitstring with `count true = count false + 1` has a unique valid cyclic rotation) and **Catalan enumeration** (`card_emlTreesOfGates`, `card_validProgramsOfGates`: exactly `catalan n` valid EML programs of length `K = 2n + 1`).
- [`Eml/RpnSoundness.lean`](Eml/RpnSoundness.lean) — Stack-depth soundness (`evalRpn_some_of_runDepth`, `valid_program_evals_singleton`) and concrete RPN stack proofs over `ℂ` (`evalRpn_0x1`, `evalRpn_0x6`, `evalRpn_0x74`, `evalRpn_append_0xc_value`).
- [`Eml/MinimalityZero.lean`](Eml/MinimalityZero.lean) — Unconditional machine-checked minimality of `0` at `K = 7` over both `ℂ` (`zero_minimal_k7`) and `EmlExt` (`ext_zero_minimal_k7`): no valid program with `K ≤ 5` evaluates to `0`.

## What is NOT formalized

- **Minimality lower bounds beyond `0` at K = 7** (excluding all shorter programs for `-1`, `2`, `+iπ`, `-2`): these remain computer-assisted interval/tower certificates in `tools/minimality/`.
- **Two `-iπ` words** (`-ipi` K 45 and `-ipi-strict` K 47): the remaining 26 `best-known.json` constant/RPN records are proved in `RpnSoundness.lean`, `Records.lean`, and `Extended.lean`.
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
