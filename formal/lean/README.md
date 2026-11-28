# Machine-Checked Lean 4 + Mathlib Formalization (`formal/lean/`)

This directory contains a concrete Lean 4 (`v4.28.0`) + Mathlib (`v4.28.0`) formalization of **EML and One** over `ℂ`, with zero `sorry` (`warningAsError := true` on `lean_lib Eml`) and zero custom axioms. Every declaration across all 21 modules is automatically audited by [`AxiomCheck.lean`](AxiomCheck.lean) to depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and [`scripts/lean-bridge-check.ts`](../../scripts/lean-bridge-check.ts) verifies in CI that every UI theorem link, every `Eml.Cert.certify` mirror check, and sample `Copy Lean 4` snippets typecheck in Lean 4.

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

### Constant-substitution words ([`Eml/MoreRecords.lean`](Eml/MoreRecords.lean))

The words the compiler substitutes for closed constants, proved from their proved sub-words with a generic gate lemma (`evalRpn_nd`: the program `p ++ q ++ [false]` evaluates to `op a b`):

- Over `ℂ` (no `ln 0`): `evalRpn_eSq` (K = 21) → `e²`, `evalRpn_invE_strict` (K = 19) → `exp (-1)`, `evalRpn_negE_strict` (K = 23) → `-e`, `evalRpn_threeHalves_strict` (K = 41) → `3/2`, `evalRpn_negThreeHalves_strict` (K = 33) → `-3/2`.
- Over `ℂ`, the `±2πi` words (K = 31, lower cut): `evalRpn_twoPiI` → `2πi` and `evalRpn_negTwoPiI` → `−2πi`. The `−2πi` proof bounds `Im(e^e / P) ∈ [−3π, −π)` from `11 < e^e < 20.1` and `3 < π < 3.15`.
- `−ln 2`, `−2/3`, `−5/3` via two general lemmas, `eml_one_scaledEE` (`eml 1 (c·e^e) = −ln c`) and `eml_one_negScaledEE` (`eml 1 (−c·e^e) = −ln c + iπ`) for real `c > 0`: `evalRpn_negLn2` (K = 27, `EmlExt`), `evalRpn_negTwoThirds` (K = 37, `EmlExt`), `evalRpn_negTwoThirds_strict` (K = 39, `ℂ`), `evalRpn_negFiveThirds` (K = 41, `EmlExt`).
- Over `EmlExt` (`ln 0 = -∞`): `evalRpn_invE` (K = 17) → `exp (-1)`, `evalRpn_negE` (K = 17) → `-e`, `evalRpn_threeHalves` (K = 39) → `3/2`, `evalRpn_negThreeHalves` (K = 31) → `-3/2`, `evalRpn_fiveHalves` (K = 41) → `5/2`, `evalRpn_negFiveHalves` (K = 41) → `-5/2`.

### The calculator's own `x − y` circuit ([`Eml/AppSub.lean`](Eml/AppSub.lean))

For general operands the compiler lowers `x − y` (`lib/eml/lowering.ts`, `scaledRot`) to a 565-token circuit: `k · rotSub(x/k, y/k)` with `k = √(y²) − (−1)`, the rotation constant `iπ` (the K 21 word), and the `subOfExp` shortcut `eml(H, exp v)` where the left operand is a word `exp H`. Its `mul`, `div`, `sqrt`, `sqr`, `sub` and `−1` words are token for token `dirEmlMul`, `dirEmlDiv`, `dirEmlSqrt`, `dirEmlSqr`, `dirRawSub` and `dirCNegOne`.

- `appSub_correct` — `evalTok (.finite 1) (.finite a) (.finite b) dirEml appSubToks [] = some [.finite (a - b)]` for **all** `a b : ℂ`, `b = 0` included (in `EmlDir`).
- `Tok.subst` / `evalTok_subst` — a word with its `x` and `y` slots replaced by sub-words evaluates as the word on those results. The trigonometric words are composed this way.
- `appSubToks_eval` — the token list unfolds to `appSub`, the circuit written with Lean's words; `shortSub_eq` — the shortcut is the raw subtraction whenever `exp H` is finite (not for every `EmlDir` value: an infinity at a general angle does not come back from `exp ∘ ln`; all four uses here have `exp H` finite); `dirCIpi_eq` — the K 21 word is `iπ` in `EmlDir`.
- `APP_SUB_WORD` in `lib/eml/export.ts` is the same word: check 115 fails if the compiler stops emitting it, and the bridge compares it with `appSubToks` token for token.

### The calculator's other operators ([`Eml/AppOps.lean`](Eml/AppOps.lean))

With variable operands the compiler emits a single stored word for most operators, and `x + y` is the `x − y` circuit with operand `(−1)·y` (scale still from `y`, 655 tokens). Each word below is the compiler's own (`APP_WORDS` in `lib/eml/export.ts`; check 115 and the bridge compare them token for token), proved in `EmlDir` for all complex inputs:

- `add_correct` (`x + y`, K 655), `twoMul_correct` (`2·x`), `sq_correct` (`x² = exp(2·ln x)`, `0` included), `sqrt_correct` (principal `a ^ (1/2)`, `0` included), `exp_correct`: exactly the value.
- `mul_correct` (`x · y`) and `neg_correct` (`−x = (−1)·x`): the value up to the sign of zero, read by `valueOf` (`(−1)·0 = −0`, as in IEEE).
- `div_correct` (`x / y`) for `b ≠ 0`, up to the sign of a zero quotient; `inv_correct` (`1/x`) for `a ≠ 0`.
- `ln_correct`: the principal `Complex.log a` for `a ≠ 0`; `ln_zero_correct`: `−∞` at `0`.
- With a constant: `subOne_correct`, `addOne_correct`, `subTwo_correct` (`x − 1`, `x + 1`, `x − 2` are the unscaled rotation `rotSub(x, c)`, `appRot_finite`), `mulTwo_correct`, `divTwo_correct`, `expE_correct` (`e^x = exp(x·ln e)`), and `cube_correct` (`x³ = exp(3·ln x)`, `0` included, with the `3` word's `EmlDir` value from its certificate): exactly the value.
- `pow_correct`: `x ^ y = exp(y·ln x)` is exactly the principal `a ^ b` for `a ≠ 0`.
- Along the way: `dirEmlDiv_eq_of_ne_zero` (no half-plane condition when `a ≠ 0`), `dirEmlMul_zero_left`, `dirEmlMul_negOne_zero` (`(−1)·0 = −0`), `dirEmlMul_pos_negInf` (`r·(−∞) = ∞·e^{iπ}` for real `r > 0`), and `appSubGen_negZero` (`x − (−0) = x` through the whole rotation).
- [`Eml/CertDir.lean`](Eml/CertDir.lean): `certify_sound_dir` — a certified constant word evaluates to its certificate's value in `EmlDir` too, so certified constants can be used inside compiled circuits (`dirConst_eq`). `certifyDir` evaluates a constant bit program directly in `EmlDir`, keeping infinity phases in units of `π/2`, and returns `none` when a zero test or a phase is not decided. The current boxes do not decide `π` or `10`.
- `*_correct_toC` (`Eml.AppOps`) reads an operand up to the sign of zero. `exp_correct_toC` accepts `−0`. The other operators require the operand not to be `−0` when its value is `0`, because `dirEml 1 0 = +∞` and `dirEml 1 (−0) = +∞ + iπ` (`dirEml_one_zero_ne_negZero`); `ln(−0) = −∞ + iπ`.

### Proof-carrying certificates ([`Eml/Cert.lean`](Eml/Cert.lean), [`Eml/CertSym.lean`](Eml/CertSym.lean), [`Eml/CertBox.lean`](Eml/CertBox.lean), [`Eml/CertExt.lean`](Eml/CertExt.lean))

`Eml.Cert.certify : List Bool → Option Sym` evaluates a constant program symbolically, and `certify_sound` (proved once) gives both `evalRpn (1 : ℂ) eml bits [] = some [s.denote]` and the same finite value in `EmlExt`, with every `ln` argument proved nonzero. A circuit is then certified by `certify_sound (by decide)`, with no per-circuit proof.

- Structural rules: integer and `kiπ` arithmetic, `exp(ln u) = u` for provably nonzero `u`, `exp(a ± kiπ) = ±exp a`, `ln(exp u) = u` in the strip, `ln(−u) = ln u − iπ` for positive real `u`, and subtraction rules that keep `iπ` multiples outermost.
- `Eml.CertBox`: `bnd s` gives integer fixed-point bounds (scale `2^48`) on the real and imaginary parts, proved by `bnd_sound`. `e` and `π` come from Mathlib's decimal bounds, `exp` on real boxes from `(1 ± x/2^16)^(±2^16)` with outward-rounded squarings, and `ln` from `1 − 1/x ≤ log x ≤ x − 1`. The checker uses boxes to prove values nonzero (`e − exp e`, `exp(e − ln 2) − exp e`), positive or negative real, or inside the strip. All of it is `Int` arithmetic, so the kernel evaluates it.
- `Eml.CertExt`: `certifyExt` runs the same gate in `EmlExt` with `±∞` as symbols (`ln 0 = −∞` for the symbol `0`, `exp(−∞) = 0`, the `extSub` table), and `certifyExt_sound` gives `evalRpn (EmlExt.finite 1) extEml bits [] = some [x.denote]`. It agrees with `certify` wherever that succeeds.
- Coverage: 23 of the 43 closed stored words certify in `ℂ`, and 17 more in `EmlExt` (check 114). `pi`, `-ipi` and `-ipi-strict` need bounds for `exp` and `ln` of genuinely complex values.
- `lib/eml/leanCert.ts` is an exact port; the bridge has the kernel re-decide `certify` and `certifyExt` on 237 programs (every program with K ≤ 13 plus every closed stored word) and compares. The inspector shows an EmlExt certificate when there is no `ℂ` one, and `Copy Lean 4` emits a `certifyExt_sound (by decide)` theorem for it.

### Genuine `eml`-word transcendental, circular, hyperbolic & logistic functions ([`Eml/Transcendental.lean`](Eml/Transcendental.lean))

Every function is built solely from `eml` / `extEml` and `1` (using `cTwo`/`extCTwo` K 19 and `extCI` K 57):

- Pure `ℂ` (`ln 0`-free): `emlPow_eq` (`x ^ y`), `emlSqrt_eq` (`x ^ (1/2)`), `emlLogBase_eq` (`log x / log b`).
- Extended `EmlExt` (all `x : ℂ`, zero strip restrictions): `extEmlNeg_eq` (`-x`), `extEmlAddRot_eq` (`a + b`), `extEmlCosh_eq` (`Complex.cosh x`), `extEmlSinh_eq` (`Complex.sinh x`), `extEmlTanh_eq` (`Complex.tanh x` for `cosh x ≠ 0`), `extEmlSigma_eq` (`(1 + exp(-x))⁻¹` for `1 + exp(-x) ≠ 0`), `extEmlCos_eq` (`Complex.cos x`), `extEmlSin_eq` (`Complex.sin x`), `extEmlTan_eq` (`Complex.tan x` for `cos x ≠ 0`), `extEmlPow_eq` (`x ^ y` for `x ≠ 0, y ≠ 0`), `extEmlLogBase_eq` (`log x / log b` for `b ≠ 0, x ≠ 0, log b ≠ 0`).

### Inverse trig & inverse hyperbolic `eml` words & branch cuts ([`Eml/InverseTrig.lean`](Eml/InverseTrig.lean))

Built purely from `extEml` and `.finite 1` (zero smuggled constants):

- `extEmlArtanh_eq`, `tanh_artanh`, and branch-cut theorems `extEmlArtanh_ofReal_gt_one` (`x > 1`) and `extEmlArtanh_ofReal_lt_neg_one` (`x < -1`), matching `mpmath` and `README.md`.
- `extEmlArctan_eq`, `tan_arctan`, and branch-cut theorems `extEmlArctan_ofImag_gt_one` (`y > 1`), `extEmlArctan_ofImag_lt_neg_one` (`y < -1`), and `extEmlArctan_neg_two_I`.
- `extEmlArsinh_eq` / `sinh_arsinh`, `extEmlArcosh_eq` / `cosh_arcosh`, `extEmlArcsin_eq` / `sin_arcsin` + `extEmlArcsin_ofReal_gt_one` (`x > 1`), `extEmlArccos_eq` / `cos_arccos` + `extEmlArccos_ofReal_gt_one` (`x > 1`) and `extEmlArccos_two`.

### Binary encoding, Raney's Cycle Lemma, Catalan counting & `0` minimality

- [`Eml/Binary.lean`](Eml/Binary.lean) — Pure inductive proofs of Dyck-prefix validity (`valid_one`, `valid_e`, `valid_zero`, `valid_append_0xc`, `valid_eml_combine`, `valid_program_starts_true`, `valid_program_odd_length`, `evalRpn_append_0xc`).
- [`Eml/TreeBijection.lean`](Eml/TreeBijection.lean) — Full bijection `treeEquivValidProgram : EmlTree ≃ { p : List Bool // IsValidProgram p }` (`toRpn_valid`, `toRpn_length`, `evalRpn_toRpn`, `toRpn_injective`, `fromRpn`, `toRpn_fromRpn`, `fromRpn_toRpn`, `evalRpn_eq_eval_fromRpn`).
- [`Eml/CycleLemma.lean`](Eml/CycleLemma.lean) — **Raney's Cycle Lemma** (`raney_cycle_lemma`: every bitstring with `count true = count false + 1` has a unique valid cyclic rotation) and **Catalan enumeration** (`card_emlTreesOfGates`, `card_validProgramsOfGates`: exactly `catalan n` valid EML programs of length `K = 2n + 1`).
- [`Eml/RpnSoundness.lean`](Eml/RpnSoundness.lean) — Stack-depth soundness (`evalRpn_some_of_runDepth`, `valid_program_evals_singleton`) and concrete RPN stack proofs over `ℂ` (`evalRpn_0x1`, `evalRpn_0x6`, `evalRpn_0x74`, `evalRpn_append_0xc_value`).
- [`Eml/MinimalityZero.lean`](Eml/MinimalityZero.lean) — Unconditional machine-checked minimality of `0` at `K = 7` over both `ℂ` (`zero_minimal_k7`) and `EmlExt` (`ext_zero_minimal_k7`): no valid program with `K ≤ 5` evaluates to `0`.

## What is NOT formalized

- **Minimality lower bounds beyond `0` at K = 7** (excluding all shorter programs for `-1`, `2`, `+iπ`, `-2`): these remain computer-assisted interval/tower certificates in `tools/minimality/`.
- **Floating-point error bounds / exact-mode precision thresholds**: numerical properties in `docs/rotsub.md` and `docs/known-limitations.md` are not formalized.
- *(All 45 constant/RPN records in `lib/eml/best-known.json` — including `-ipi` K 45 and `-ipi-strict` K 47 — are machine-checked in `RpnSoundness.lean`, `Records.lean`, `Extended.lean`, and `MoreRecords.lean`, and cross-checked against the UI in CI. `lib/eml/checks/112-lean-record-coverage.ts` fails if a stored word has no theorem link or if a link's stored `lean` value disagrees with the exact engine, `scripts/lean-bridge-check.ts` proves each link's word evaluates to exactly that stored value, and `lean.yml` runs when `best-known.json` changes.)*

## Building and auditing locally

With [elan](https://github.com/leanprover/elan) installed:

```bash
cd formal/lean
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

Every push or pull request touching `formal/lean/` or `.github/workflows/lean.yml` runs `lake exe cache get`, `lake build`, and the `AxiomCheck.lean` axiom audit in CI.
