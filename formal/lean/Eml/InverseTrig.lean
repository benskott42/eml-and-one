/-
  Machine-checked Lean 4 + Mathlib proofs of the inverse trigonometric and
  inverse hyperbolic `eml` words (`artanh`, `arctan`, `arsinh`, `arcosh`,
  `arcsin`, `arccos`) over `EmlExt`, built purely from `extEml` and `.finite 1`
  (zero smuggled constants, zero `sorry`, zero custom axioms).

  Includes exact branch-cut verifications matching `mpmath` and `README.md`:
    - `extEmlArtanh_ofReal_gt_one`: for real `x > 1`,
      `artanh(x) = (1/2) ln((x + 1)/(x - 1)) - iπ/2`
    - `extEmlArctan_neg_two_I`: `arctan(-2i) = -π/2 - (artanh 2)i`
    - `extEmlArccos_two`: `arccos(2) = i · arcosh(2)`
    - Right-inverse identities: `tanh(artanh z) = z`, `tan(arctan z) = z`,
      `sinh(arsinh z) = z`, `cosh(arcosh z) = z`, `sin(arcsin z) = z`,
      `cos(arccos z) = z`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Eml.Basic
import Eml.Extended
import Eml.DirectedInf
import Eml.Transcendental

namespace Eml.InverseTrig

open Eml
open Eml.Extended
open Eml.DirectedInf
open Eml.Transcendental

/-! ### Helper lemmas for principal complex square roots -/

private theorem cpow_half_sq {w : ℂ} (hw : w ≠ 0) :
    (w ^ ((1 : ℂ) / 2)) ^ 2 = w := by
  rw [sq, ← Complex.cpow_add _ _ hw]
  norm_num

private theorem cpow_half_ne_zero {w : ℂ} (hw : w ≠ 0) :
    w ^ ((1 : ℂ) / 2) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hw]
  exact Complex.exp_ne_zero _

private theorem exp_log_div_two {r : ℝ} (hr : 0 < r) :
    Real.exp (Real.log r / 2) = Real.sqrt r := by
  symm
  rw [Real.sqrt_eq_iff_eq_sq (le_of_lt hr) (le_of_lt (Real.exp_pos _)), sq, ← Real.exp_add]
  have h : Real.log r / 2 + Real.log r / 2 = Real.log r := by ring
  rw [h, Real.exp_log hr]

private theorem cpow_half_ofReal_pos {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) ^ ((1 : ℂ) / 2)) = (Real.sqrt r : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)),
    ← Complex.ofReal_log (le_of_lt hr)]
  have h : (Real.log r : ℂ) * ((1 : ℂ) / 2) = ((Real.log r / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_exp, exp_log_div_two hr]

private theorem cpow_half_ofReal_neg {r : ℝ} (hr : r < 0) :
    ((r : ℂ) ^ ((1 : ℂ) / 2)) = (Real.sqrt (-r) : ℂ) * Complex.I := by
  have hpos : 0 < -r := by linarith
  have heq : (r : ℂ) = Complex.exp ((Real.log (-r) : ℂ) + Real.pi * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast; ring
  have hlog : Complex.log (r : ℂ) = (Real.log (-r) : ℂ) + Real.pi * Complex.I := by
    rw [heq, Complex.log_exp]
    · simp; linarith [Real.pi_pos]
    · simp
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_lt hr)), hlog]
  have hmul : ((Real.log (-r) : ℂ) + Real.pi * Complex.I) * ((1 : ℂ) / 2) =
      ((Real.log (-r) / 2 : ℝ) : ℂ) + (Real.pi / 2 : ℂ) * Complex.I := by
    push_cast; ring
  rw [hmul, Complex.exp_add, Complex.exp_pi_div_two_mul_I, ← Complex.ofReal_exp,
    exp_log_div_two hpos]

/-! ### `artanh(z) = Log(√(1 + z) / √(1 - z))` (`v1.0.2` cut-exact formula) -/

/-- `artanh(z) = extEmlLn (extEmlDiv (extEmlSqrt (1 + z)) (extEmlSqrt (1 - z)))`,
    built purely from `extEml` and `.finite 1`. -/
noncomputable def extEmlArtanh (z : EmlExt) : EmlExt :=
  extEmlLn (extEmlDiv (extEmlSqrt (extEmlAddRot (.finite 1) z))
    (extEmlSqrt (extRotSub extCI (.finite 1) z)))

theorem extEmlArtanh_eq {z : ℂ} (hp : 1 + z ≠ 0) (hm : 1 - z ≠ 0) :
    extEmlArtanh (.finite z) =
      .finite (Complex.log ((1 + z) ^ ((1 : ℂ) / 2) / (1 - z) ^ ((1 : ℂ) / 2))) := by
  unfold extEmlArtanh
  rw [extEmlAddRot_eq, extCI_eq_I, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero,
    extEmlSqrt_finite hp, extEmlSqrt_finite hm,
    extEmlDiv_eq _ (cpow_half_ne_zero hm),
    extEmlLn_finite_ne_zero (div_ne_zero (cpow_half_ne_zero hp) (cpow_half_ne_zero hm))]

/-- Right-inverse identity: `tanh (artanh z) = z` for all `z ≠ ±1`. -/
theorem tanh_artanh {z : ℂ} (hp : 1 + z ≠ 0) (hm : 1 - z ≠ 0) :
    Complex.tanh (Complex.log ((1 + z) ^ ((1 : ℂ) / 2) / (1 - z) ^ ((1 : ℂ) / 2))) = z := by
  set u : ℂ := (1 + z) ^ ((1 : ℂ) / 2) / (1 - z) ^ ((1 : ℂ) / 2)
  have hu : u ≠ 0 := div_ne_zero (cpow_half_ne_zero hp) (cpow_half_ne_zero hm)
  have hu2 : u ^ 2 = (1 + z) / (1 - z) := by
    simp only [u, div_pow, cpow_half_sq hp, cpow_half_sq hm]
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh,
    Complex.exp_neg, Complex.exp_log hu]
  have hden : u + u⁻¹ ≠ 0 := by
    intro h
    have h1 : u ^ 2 + 1 = 0 := by
      have := congrArg (· * u) h
      simp only [add_mul, inv_mul_cancel₀ hu, zero_mul] at this
      linear_combination this
    rw [hu2] at h1
    have h2 : (1 + z) + (1 - z) = 0 := by
      have := congrArg (· * (1 - z)) h1
      simp only [add_mul, div_mul_cancel₀ _ hm, one_mul, zero_mul] at this
      exact this
    have h2' : (2 : ℂ) = 0 := by linear_combination h2
    exact two_ne_zero h2'
  have hstep : (u - u⁻¹) / 2 / ((u + u⁻¹) / 2) = (u ^ 2 - 1) / (u ^ 2 + 1) := by
    field_simp [hu, hden]
  rw [hstep, hu2]
  field_simp [hm]
  ring

/-- Branch-cut theorem matching `README.md` and `mpmath.atanh`:
    for any real `x > 1`, `extEmlArtanh (.finite x) = .finite ((1/2) ln((x + 1)/(x - 1)) - iπ/2)`. -/
theorem extEmlArtanh_ofReal_gt_one {x : ℝ} (hx : 1 < x) :
    extEmlArtanh (.finite (x : ℂ)) =
      .finite ((Real.log ((x + 1) / (x - 1)) / 2 : ℝ) - (Real.pi / 2 : ℂ) * Complex.I) := by
  have hp_r : 0 < 1 + x := by linarith
  have hm_r : 1 - x < 0 := by linarith
  have hp : (1 : ℂ) + (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hp_r)
  have hm : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (ne_of_lt hm_r)
  rw [extEmlArtanh_eq hp hm]
  congr 1
  have h1 : ((1 : ℂ) + (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (1 + x) : ℂ) := by
    rw [show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl]
    exact cpow_half_ofReal_pos hp_r
  have h2 : ((1 : ℂ) - (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (x - 1) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; rfl,
      cpow_half_ofReal_neg hm_r]
    rw [show -(1 - x) = x - 1 by ring]
  rw [h1, h2]
  have hr_pos : 0 < Real.sqrt (1 + x) / Real.sqrt (x - 1) :=
    div_pos (Real.sqrt_pos.mpr hp_r) (Real.sqrt_pos.mpr (by linarith))
  have hratio : (Real.sqrt (1 + x) : ℂ) / ((Real.sqrt (x - 1) : ℂ) * Complex.I) =
      Complex.exp ((Real.log (Real.sqrt (1 + x) / Real.sqrt (x - 1)) : ℂ) - (Real.pi / 2 : ℂ) * Complex.I) := by
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hr_pos, Complex.exp_pi_div_two_mul_I]
    push_cast
    rw [div_div]
  rw [hratio, Complex.log_exp]
  · congr 1
    have hsq : Real.sqrt (1 + x) / Real.sqrt (x - 1) = Real.sqrt ((x + 1) / (x - 1)) := by
      rw [Real.sqrt_div (by linarith), show 1 + x = x + 1 by ring]
    rw [hsq, Real.log_sqrt (div_nonneg (by linarith) (by linarith))]
  · have him : ((Real.log (Real.sqrt (1 + x) / Real.sqrt (x - 1)) : ℂ) -
        (Real.pi / 2 : ℂ) * Complex.I).im = -(Real.pi / 2) := by simp
    rw [him]; linarith [Real.pi_pos]
  · have him : ((Real.log (Real.sqrt (1 + x) / Real.sqrt (x - 1)) : ℂ) -
        (Real.pi / 2 : ℂ) * Complex.I).im = -(Real.pi / 2) := by simp
    rw [him]; linarith [Real.pi_pos]

/-! ### `arctan(z) = -i · artanh(i · z)` (`v1.0.2` formula) -/

/-- `arctan(z) = -i · artanh(i · z)`, built purely from `extEml` and `.finite 1`. -/
noncomputable def extEmlArctan (z : EmlExt) : EmlExt :=
  extEmlMul (extEmlNeg extCI) (extEmlArtanh (extEmlMul extCI z))

theorem extEmlArctan_eq {z : ℂ} (hp : 1 + Complex.I * z ≠ 0) (hm : 1 - Complex.I * z ≠ 0) :
    extEmlArctan (.finite z) =
      .finite (-Complex.I * Complex.log ((1 + Complex.I * z) ^ ((1 : ℂ) / 2) /
        (1 - Complex.I * z) ^ ((1 : ℂ) / 2))) := by
  unfold extEmlArctan
  rw [extCI_eq_I, extEmlNeg_eq, extEmlMul_eq Complex.I_ne_zero,
    extEmlArtanh_eq hp hm, extEmlMul_eq (neg_ne_zero.mpr Complex.I_ne_zero)]

/-- Right-inverse identity: `tan (arctan z) = z` for all `z ≠ ±i`. -/
theorem tan_arctan {z : ℂ} (hp : 1 + Complex.I * z ≠ 0) (hm : 1 - Complex.I * z ≠ 0) :
    Complex.tan (-Complex.I * Complex.log ((1 + Complex.I * z) ^ ((1 : ℂ) / 2) /
      (1 - Complex.I * z) ^ ((1 : ℂ) / 2))) = z := by
  set w : ℂ := Complex.log ((1 + Complex.I * z) ^ ((1 : ℂ) / 2) / (1 - Complex.I * z) ^ ((1 : ℂ) / 2))
  have htanh : Complex.tanh w = Complex.I * z := tanh_artanh hp hm
  rw [Complex.tan_eq_sin_div_cos, Complex.sin, Complex.cos]
  have h1 : (-Complex.I * w) * Complex.I = w := by
    calc (-Complex.I * w) * Complex.I = -(Complex.I * Complex.I) * w := by ring
      _ = w := by rw [Complex.I_mul_I]; ring
  have h2 : -(-Complex.I * w) * Complex.I = -w := by rw [neg_mul, h1]
  rw [h2, h1]
  have hcosh_ne : (Complex.exp w + Complex.exp (-w)) / 2 ≠ 0 := by
    intro h
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.cosh, h, div_zero] at htanh
    have hz0 : z = 0 := (mul_eq_zero.mp htanh.symm).resolve_left Complex.I_ne_zero
    subst hz0
    simp [w] at h
  have hstep : (Complex.exp (-w) - Complex.exp w) * Complex.I / 2 /
      ((Complex.exp w + Complex.exp (-w)) / 2) = -Complex.I * Complex.tanh w := by
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh]
    have hsum_ne : Complex.exp w + Complex.exp (-w) ≠ 0 := by
      intro h0; apply hcosh_ne; rw [h0, zero_div]
    field_simp [hsum_ne]
    ring
  rw [hstep, htanh]
  calc -Complex.I * (Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

/-- Branch-cut verification matching `README.md`:
    `extEmlArctan (.finite (-2 * i)) = .finite (-π/2 - (1/2 · ln 3) · i)`. -/
theorem extEmlArctan_neg_two_I :
    extEmlArctan (.finite (-2 * Complex.I)) =
      .finite (-(Real.pi / 2 : ℂ) - ((Real.log 3 / 2 : ℝ) : ℂ) * Complex.I) := by
  unfold extEmlArctan
  have hmul : Complex.I * (-2 * Complex.I) = (2 : ℝ) := by
    calc Complex.I * (-2 * Complex.I) = -2 * (Complex.I * Complex.I) := by ring
      _ = 2 := by rw [Complex.I_mul_I]; ring
  rw [extCI_eq_I, extEmlNeg_eq, extEmlMul_eq Complex.I_ne_zero, hmul,
    extEmlArtanh_ofReal_gt_one (by norm_num : (1 : ℝ) < 2),
    extEmlMul_eq (neg_ne_zero.mpr Complex.I_ne_zero)]
  congr 1
  have h3 : ((2 : ℝ) + 1) / (2 - 1) = 3 := by norm_num
  rw [h3]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (Real.pi / 2 : ℂ) * hI2

/-! ### `arsinh`, `arcosh`, `arcsin`, `arccos` built purely from `extEml` and `.finite 1` -/

/-- `arsinh(z) = ln(z + √(z² + 1))`. -/
noncomputable def extEmlArsinh (z : EmlExt) : EmlExt :=
  extEmlLn (extEmlAddRot z (extEmlSqrt (extEmlAddRot (extEmlMul z z) (.finite 1))))

theorem extEmlArsinh_eq {z : ℂ} (h1 : z * z + 1 ≠ 0)
    (h2 : z + (z * z + 1) ^ ((1 : ℂ) / 2) ≠ 0) :
    extEmlArsinh (.finite z) =
      .finite (Complex.log (z + (z * z + 1) ^ ((1 : ℂ) / 2))) := by
  unfold extEmlArsinh
  by_cases hz : z = 0
  · subst hz
    simp only [zero_mul] at h1 h2 ⊢
    rw [show extEmlMul (.finite 0) (.finite 0) = .finite 0 from extEmlSqr_zero,
      extEmlAddRot_eq, extEmlSqrt_finite h1, extEmlAddRot_eq, extEmlLn_finite_ne_zero h2]
  · rw [extEmlMul_eq hz, extEmlAddRot_eq, extEmlSqrt_finite h1, extEmlAddRot_eq,
      extEmlLn_finite_ne_zero h2]

theorem sinh_arsinh {z : ℂ} (h1 : z * z + 1 ≠ 0)
    (h2 : z + (z * z + 1) ^ ((1 : ℂ) / 2) ≠ 0) :
    Complex.sinh (Complex.log (z + (z * z + 1) ^ ((1 : ℂ) / 2))) = z := by
  set s : ℂ := (z * z + 1) ^ ((1 : ℂ) / 2)
  have hs2 : s ^ 2 = z * z + 1 := cpow_half_sq h1
  rw [Complex.sinh, Complex.exp_neg, Complex.exp_log h2]
  field_simp [h2]
  linear_combination hs2

/-- `arcosh(z) = ln(z + √(z - 1) · √(z + 1))`. -/
noncomputable def extEmlArcosh (z : EmlExt) : EmlExt :=
  extEmlLn (extEmlAddRot z (extEmlMul (extEmlSqrt (extRotSub extCI z (.finite 1)))
    (extEmlSqrt (extEmlAddRot z (.finite 1)))))

theorem extEmlArcosh_eq {z : ℂ} (hm : z - 1 ≠ 0) (hp : z + 1 ≠ 0)
    (hsum : z + (z - 1) ^ ((1 : ℂ) / 2) * (z + 1) ^ ((1 : ℂ) / 2) ≠ 0) :
    extEmlArcosh (.finite z) =
      .finite (Complex.log (z + (z - 1) ^ ((1 : ℂ) / 2) * (z + 1) ^ ((1 : ℂ) / 2))) := by
  unfold extEmlArcosh
  rw [extCI_eq_I, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero, extEmlAddRot_eq,
    extEmlSqrt_finite hm, extEmlSqrt_finite hp, extEmlMul_eq (cpow_half_ne_zero hm),
    extEmlAddRot_eq, extEmlLn_finite_ne_zero hsum]

theorem cosh_arcosh {z : ℂ} (hm : z - 1 ≠ 0) (hp : z + 1 ≠ 0)
    (hsum : z + (z - 1) ^ ((1 : ℂ) / 2) * (z + 1) ^ ((1 : ℂ) / 2) ≠ 0) :
    Complex.cosh (Complex.log (z + (z - 1) ^ ((1 : ℂ) / 2) * (z + 1) ^ ((1 : ℂ) / 2))) = z := by
  set a : ℂ := (z - 1) ^ ((1 : ℂ) / 2)
  set b : ℂ := (z + 1) ^ ((1 : ℂ) / 2)
  have ha2 : a ^ 2 = z - 1 := cpow_half_sq hm
  have hb2 : b ^ 2 = z + 1 := cpow_half_sq hp
  have hab2 : (a * b) ^ 2 = z ^ 2 - 1 := by rw [mul_pow, ha2, hb2]; ring
  rw [Complex.cosh, Complex.exp_neg, Complex.exp_log hsum]
  field_simp [hsum]
  linear_combination hab2

/-- `arcsin(z) = -i · ln(i · z + √(1 - z²))`. -/
noncomputable def extEmlArcsin (z : EmlExt) : EmlExt :=
  extEmlMul (extEmlNeg extCI)
    (extEmlLn (extEmlAddRot (extEmlMul extCI z)
      (extEmlSqrt (extRotSub extCI (.finite 1) (extEmlMul z z)))))

theorem extEmlArcsin_eq {z : ℂ} (h1 : 1 - z * z ≠ 0)
    (h2 : Complex.I * z + (1 - z * z) ^ ((1 : ℂ) / 2) ≠ 0) :
    extEmlArcsin (.finite z) =
      .finite (-Complex.I * Complex.log (Complex.I * z + (1 - z * z) ^ ((1 : ℂ) / 2))) := by
  unfold extEmlArcsin
  rw [extCI_eq_I, extEmlNeg_eq, extEmlMul_eq Complex.I_ne_zero]
  by_cases hz : z = 0
  · subst hz
    simp only [zero_mul] at h1 h2 ⊢
    rw [show extEmlMul (.finite 0) (.finite 0) = .finite 0 from extEmlSqr_zero,
      extRotSub_eq_sub Complex.I_re Complex.I_ne_zero, extEmlSqrt_finite h1,
      extEmlAddRot_eq, extEmlLn_finite_ne_zero h2, extEmlMul_eq (neg_ne_zero.mpr Complex.I_ne_zero)]
  · rw [extEmlMul_eq hz, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero, extEmlSqrt_finite h1,
      extEmlAddRot_eq, extEmlLn_finite_ne_zero h2, extEmlMul_eq (neg_ne_zero.mpr Complex.I_ne_zero)]

theorem sin_arcsin {z : ℂ} (h1 : 1 - z * z ≠ 0)
    (h2 : Complex.I * z + (1 - z * z) ^ ((1 : ℂ) / 2) ≠ 0) :
    Complex.sin (-Complex.I * Complex.log (Complex.I * z + (1 - z * z) ^ ((1 : ℂ) / 2))) = z := by
  set s : ℂ := (1 - z * z) ^ ((1 : ℂ) / 2)
  have hs2 : s ^ 2 = 1 - z * z := cpow_half_sq h1
  set w : ℂ := Complex.log (Complex.I * z + s)
  rw [Complex.sin]
  have hmul : (-Complex.I * w) * Complex.I = w := by
    calc (-Complex.I * w) * Complex.I = -(Complex.I * Complex.I) * w := by ring
      _ = w := by rw [Complex.I_mul_I]; ring
  rw [show -(-Complex.I * w) * Complex.I = -w by rw [neg_mul, hmul], hmul,
    Complex.exp_neg, Complex.exp_log h2]
  field_simp [h2]
  linear_combination -(Complex.I * hs2) - z * (Complex.I * z + 2 * s) * Complex.I_mul_I

/-- `arccos(z) = -i · ln(z + i · √(1 - z) · √(1 + z))` (`v1.0.3` formula). -/
noncomputable def extEmlArccos (z : EmlExt) : EmlExt :=
  extEmlMul (extEmlNeg extCI)
    (extEmlLn (extEmlAddRot z
      (extEmlMul extCI (extEmlMul (extEmlSqrt (extRotSub extCI (.finite 1) z))
        (extEmlSqrt (extEmlAddRot (.finite 1) z))))))

theorem extEmlArccos_eq {z : ℂ} (hm : 1 - z ≠ 0) (hp : 1 + z ≠ 0)
    (hsum : z + Complex.I * ((1 - z) ^ ((1 : ℂ) / 2) * (1 + z) ^ ((1 : ℂ) / 2)) ≠ 0) :
    extEmlArccos (.finite z) =
      .finite (-Complex.I * Complex.log (z + Complex.I *
        ((1 - z) ^ ((1 : ℂ) / 2) * (1 + z) ^ ((1 : ℂ) / 2)))) := by
  unfold extEmlArccos
  rw [extCI_eq_I, extEmlNeg_eq, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero, extEmlAddRot_eq,
    extEmlSqrt_finite hm, extEmlSqrt_finite hp, extEmlMul_eq (cpow_half_ne_zero hm),
    extEmlMul_eq Complex.I_ne_zero, extEmlAddRot_eq, extEmlLn_finite_ne_zero hsum,
    extEmlMul_eq (neg_ne_zero.mpr Complex.I_ne_zero)]

theorem cos_arccos {z : ℂ} (hm : 1 - z ≠ 0) (hp : 1 + z ≠ 0)
    (hsum : z + Complex.I * ((1 - z) ^ ((1 : ℂ) / 2) * (1 + z) ^ ((1 : ℂ) / 2)) ≠ 0) :
    Complex.cos (-Complex.I * Complex.log (z + Complex.I *
      ((1 - z) ^ ((1 : ℂ) / 2) * (1 + z) ^ ((1 : ℂ) / 2)))) = z := by
  set a : ℂ := (1 - z) ^ ((1 : ℂ) / 2)
  set b : ℂ := (1 + z) ^ ((1 : ℂ) / 2)
  have ha2 : a ^ 2 = 1 - z := cpow_half_sq hm
  have hb2 : b ^ 2 = 1 + z := cpow_half_sq hp
  have hab2 : (a * b) ^ 2 = 1 - z ^ 2 := by rw [mul_pow, ha2, hb2]; ring
  set w : ℂ := Complex.log (z + Complex.I * (a * b))
  rw [Complex.cos]
  have hmul : (-Complex.I * w) * Complex.I = w := by
    calc (-Complex.I * w) * Complex.I = -(Complex.I * Complex.I) * w := by ring
      _ = w := by rw [Complex.I_mul_I]; ring
  rw [show -(-Complex.I * w) * Complex.I = -w by rw [neg_mul, hmul], hmul,
    Complex.exp_neg, Complex.exp_log hsum]
  have hprod : (z + Complex.I * (a * b)) * (z - Complex.I * (a * b)) = 1 := by
    linear_combination -(a * b) ^ 2 * Complex.I_mul_I + hab2
  have hinv : (z + Complex.I * (a * b))⁻¹ = z - Complex.I * (a * b) :=
    (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv]
  ring

/-- Branch-cut verification matching `README.md`:
    `arccos(2) = +i · arcosh(2) = +i · ln(2 + √3)`. -/
theorem extEmlArccos_two :
    extEmlArccos (.finite 2) = .finite (Complex.I * (Real.log (2 + Real.sqrt 3) : ℂ)) := by
  have hm : (1 : ℂ) - 2 ≠ 0 := by norm_num
  have hp : (1 : ℂ) + 2 ≠ 0 := by norm_num
  have h1 : ((1 : ℂ) - 2) ^ ((1 : ℂ) / 2) = Complex.I := by
    rw [show (1 : ℂ) - 2 = ((-1 : ℝ) : ℂ) by norm_num, cpow_half_ofReal_neg (by norm_num)]
    simp
  have h2 : ((1 : ℂ) + 2) ^ ((1 : ℂ) / 2) = (Real.sqrt 3 : ℂ) := by
    rw [show (1 : ℂ) + 2 = ((3 : ℝ) : ℂ) by norm_num, cpow_half_ofReal_pos (by norm_num)]
  have harg : (2 : ℂ) + Complex.I * (((1 : ℂ) - 2) ^ ((1 : ℂ) / 2) * ((1 : ℂ) + 2) ^ ((1 : ℂ) / 2)) =
      ((2 - Real.sqrt 3 : ℝ) : ℂ) := by
    rw [h1, h2]
    push_cast
    linear_combination (Real.sqrt 3 : ℂ) * Complex.I_mul_I
  have hpos_sub : 0 < 2 - Real.sqrt 3 := by
    have : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have hsum : (2 : ℂ) + Complex.I * (((1 : ℂ) - 2) ^ ((1 : ℂ) / 2) * ((1 : ℂ) + 2) ^ ((1 : ℂ) / 2)) ≠ 0 := by
    rw [harg]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos_sub)
  rw [extEmlArccos_eq hm hp hsum, harg, ← Complex.ofReal_log (le_of_lt hpos_sub)]
  congr 1
  have hinv : 2 - Real.sqrt 3 = (2 + Real.sqrt 3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [hinv, Real.log_inv]
  push_cast; ring

/-! ### General branch-cut theorems across the cuts -/

/-- Branch cut of `artanh` for all real `x < -1`:
    `artanh(x) = ½ ln((1 + x)/(x - 1)) + iπ/2`, matching `mpmath.atanh`. -/
theorem extEmlArtanh_ofReal_lt_neg_one {x : ℝ} (hx : x < -1) :
    extEmlArtanh (.finite (x : ℂ)) =
      .finite ((Real.log ((1 + x) / (x - 1)) / 2 : ℝ) + (Real.pi / 2 : ℂ) * Complex.I) := by
  have hp : (1 : ℂ) + (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hm : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [extEmlArtanh_eq hp hm]
  congr 1
  have h1 : ((1 : ℂ) + (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (-(1 + x)) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; ring]
    exact cpow_half_ofReal_neg (by linarith)
  have h2 : ((1 : ℂ) - (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (1 - x) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact cpow_half_ofReal_pos (by linarith)
  rw [h1, h2]
  set r : ℝ := Real.sqrt (-(1 + x)) / Real.sqrt (1 - x)
  have hr_pos : 0 < r := div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
  have hquot : (Real.sqrt (-(1 + x)) : ℂ) * Complex.I / (Real.sqrt (1 - x) : ℂ) =
      (r : ℂ) * Complex.I := by
    simp only [r]; push_cast; ring
  rw [hquot]
  have hexp : Complex.exp ((Real.log r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) =
      (r : ℂ) * Complex.I := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr_pos, Complex.exp_pi_div_two_mul_I]
  rw [← hexp, Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]
  have hr2 : r ^ 2 = (1 + x) / (x - 1) := by
    simp only [r, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ -(1 + x) by linarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by linarith)]
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  have hlogr : Real.log r = Real.log ((1 + x) / (x - 1)) / 2 := by
    have h := Real.log_pow r 2
    rw [hr2] at h
    push_cast at h
    linarith
  rw [hlogr]

/-- Branch cut of `arctan` on the upper imaginary axis `y > 1`:
    `arctan(y·i) = π/2 + (½ ln((y + 1)/(y - 1)))·i`, matching `mpmath.atan`. -/
theorem extEmlArctan_ofImag_gt_one {y : ℝ} (hy : 1 < y) :
    extEmlArctan (.finite ((y : ℂ) * Complex.I)) =
      .finite ((Real.pi / 2 : ℂ) + ((Real.log ((y + 1) / (y - 1)) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hIy : Complex.I * ((y : ℂ) * Complex.I) = (-(y : ℝ) : ℂ) := by
    calc Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (-(y : ℝ) : ℂ) := by rw [Complex.I_mul_I]; ring
  have hp : (1 : ℂ) + Complex.I * ((y : ℂ) * Complex.I) ≠ 0 := by
    rw [hIy, show (1 : ℂ) + (-(y : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hm : (1 : ℂ) - Complex.I * ((y : ℂ) * Complex.I) ≠ 0 := by
    rw [hIy, show (1 : ℂ) - (-(y : ℝ) : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [extEmlArctan_eq hp hm]
  congr 1
  rw [hIy]
  have h1 : ((1 : ℂ) + (-(y : ℝ) : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (y - 1) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) + (-(y : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring,
      cpow_half_ofReal_neg (by linarith), show -(1 - y) = y - 1 by ring]
  have h2 : ((1 : ℂ) - (-(y : ℝ) : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (y + 1) : ℂ) := by
    rw [show (1 : ℂ) - (-(y : ℝ) : ℂ) = ((y + 1 : ℝ) : ℂ) by push_cast; ring]
    exact cpow_half_ofReal_pos (by linarith)
  rw [h1, h2]
  set r : ℝ := Real.sqrt (y - 1) / Real.sqrt (y + 1)
  have hr_pos : 0 < r := div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
  have hquot : (Real.sqrt (y - 1) : ℂ) * Complex.I / (Real.sqrt (y + 1) : ℂ) = (r : ℂ) * Complex.I := by
    simp only [r]; push_cast; ring
  rw [hquot]
  have hexp : Complex.exp ((Real.log r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) = (r : ℂ) * Complex.I := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr_pos, Complex.exp_pi_div_two_mul_I]
  rw [← hexp, Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]
  have hr2 : r ^ 2 = ((y + 1) / (y - 1))⁻¹ := by
    simp only [r, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ y - 1 by linarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ y + 1 by linarith), inv_div]
  have hlogr : Real.log r = -(Real.log ((y + 1) / (y - 1)) / 2) := by
    have h := Real.log_pow r 2
    rw [hr2, Real.log_inv] at h
    push_cast at h
    linarith
  rw [hlogr]
  push_cast
  linear_combination -(Real.pi / 2 : ℂ) * Complex.I_mul_I

/-- Branch cut of `arctan` on the lower imaginary axis `y < -1`:
    `arctan(y·i) = -π/2 - (½ ln((1 - y)/(-1 - y)))·i`, generalizing `extEmlArctan_neg_two_I`. -/
theorem extEmlArctan_ofImag_lt_neg_one {y : ℝ} (hy : y < -1) :
    extEmlArctan (.finite ((y : ℂ) * Complex.I)) =
      .finite (-(Real.pi / 2 : ℂ) - ((Real.log ((1 - y) / (-1 - y)) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hIy : Complex.I * ((y : ℂ) * Complex.I) = (-(y : ℝ) : ℂ) := by
    calc Complex.I * ((y : ℂ) * Complex.I) = (y : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (-(y : ℝ) : ℂ) := by rw [Complex.I_mul_I]; ring
  have hp : (1 : ℂ) + Complex.I * ((y : ℂ) * Complex.I) ≠ 0 := by
    rw [hIy, show (1 : ℂ) + (-(y : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hm : (1 : ℂ) - Complex.I * ((y : ℂ) * Complex.I) ≠ 0 := by
    rw [hIy, show (1 : ℂ) - (-(y : ℝ) : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [extEmlArctan_eq hp hm]
  congr 1
  rw [hIy]
  have h1 : ((1 : ℂ) + (-(y : ℝ) : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (1 - y) : ℂ) := by
    rw [show (1 : ℂ) + (-(y : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) by push_cast; ring]
    exact cpow_half_ofReal_pos (by linarith)
  have h2 : ((1 : ℂ) - (-(y : ℝ) : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (-1 - y) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) - (-(y : ℝ) : ℂ) = ((1 + y : ℝ) : ℂ) by push_cast; ring,
      cpow_half_ofReal_neg (by linarith), show -(1 + y) = -1 - y by ring]
  rw [h1, h2]
  set r : ℝ := Real.sqrt (1 - y) / Real.sqrt (-1 - y)
  have hr_pos : 0 < r := div_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
  have hquot : (Real.sqrt (1 - y) : ℂ) / ((Real.sqrt (-1 - y) : ℂ) * Complex.I) =
      -((r : ℂ) * Complex.I) := by
    have hsqrt_ne : (Real.sqrt (-1 - y) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
    simp only [r]
    rw [div_eq_iff (mul_ne_zero hsqrt_ne Complex.I_ne_zero)]
    push_cast
    calc (Real.sqrt (1 - y) : ℂ)
        = (Real.sqrt (1 - y) : ℂ) / (Real.sqrt (-1 - y) : ℂ) * (Real.sqrt (-1 - y) : ℂ) * (-(Complex.I * Complex.I)) := by
            rw [Complex.I_mul_I]; field_simp
      _ = -(↑(Real.sqrt (1 - y)) / ↑(Real.sqrt (-1 - y)) * Complex.I) * (↑(Real.sqrt (-1 - y)) * Complex.I) := by ring
  rw [hquot]
  have hexp : Complex.exp ((Real.log r : ℂ) - (Real.pi / 2 : ℂ) * Complex.I) = -((r : ℂ) * Complex.I) := by
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hr_pos, Complex.exp_pi_div_two_mul_I]
    rw [div_eq_iff Complex.I_ne_zero]
    linear_combination (r : ℂ) * Complex.I_mul_I
  rw [← hexp, Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]
  have hr2 : r ^ 2 = (1 - y) / (-1 - y) := by
    simp only [r, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by linarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ -1 - y by linarith)]
  have hlogr : Real.log r = Real.log ((1 - y) / (-1 - y)) / 2 := by
    have h := Real.log_pow r 2
    rw [hr2] at h
    push_cast at h
    linarith
  rw [hlogr]
  push_cast
  linear_combination (Real.pi / 2 : ℂ) * Complex.I_mul_I

/-- Branch cut of `arccos` for all real `x > 1`:
    `arccos(x) = +i · ln(x + √(x² - 1))`, generalizing `extEmlArccos_two`. -/
theorem extEmlArccos_ofReal_gt_one {x : ℝ} (hx : 1 < x) :
    extEmlArccos (.finite (x : ℂ)) =
      .finite (Complex.I * (Real.log (x + Real.sqrt (x * x - 1)) : ℂ)) := by
  have hm : (1 : ℂ) - (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hp : (1 : ℂ) + (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have h1 : ((1 : ℂ) - (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (x - 1) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      cpow_half_ofReal_neg (by linarith), show -(1 - x) = x - 1 by ring]
  have h2 : ((1 : ℂ) + (x : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (x + 1) : ℂ) := by
    rw [show (1 : ℂ) + (x : ℂ) = ((x + 1 : ℝ) : ℂ) by push_cast; ring]
    exact cpow_half_ofReal_pos (by linarith)
  have hsqrt_mul : Real.sqrt (x - 1) * Real.sqrt (x + 1) = Real.sqrt (x * x - 1) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  have harg : (x : ℂ) + Complex.I * (((1 : ℂ) - (x : ℂ)) ^ ((1 : ℂ) / 2) *
      ((1 : ℂ) + (x : ℂ)) ^ ((1 : ℂ) / 2)) =
      ((x - Real.sqrt (x * x - 1) : ℝ) : ℂ) := by
    rw [h1, h2]
    have hmul : (Real.sqrt (x - 1) : ℂ) * (Real.sqrt (x + 1) : ℂ) = (Real.sqrt (x * x - 1) : ℂ) := by
      exact_mod_cast hsqrt_mul
    push_cast
    calc (x : ℂ) + Complex.I * ((Real.sqrt (x - 1) : ℂ) * Complex.I * (Real.sqrt (x + 1) : ℂ))
        = (x : ℂ) + (Complex.I * Complex.I) * ((Real.sqrt (x - 1) : ℂ) * (Real.sqrt (x + 1) : ℂ)) := by ring
      _ = (x : ℂ) - (Real.sqrt (x * x - 1) : ℂ) := by rw [Complex.I_mul_I, hmul]; ring
  have hpos_sub : 0 < x - Real.sqrt (x * x - 1) := by
    have : Real.sqrt (x * x - 1) < x := by
      rw [Real.sqrt_lt' (by linarith)]; nlinarith
    linarith
  have hsum : (x : ℂ) + Complex.I * (((1 : ℂ) - (x : ℂ)) ^ ((1 : ℂ) / 2) *
      ((1 : ℂ) + (x : ℂ)) ^ ((1 : ℂ) / 2)) ≠ 0 := by
    rw [harg]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos_sub)
  rw [extEmlArccos_eq hm hp hsum, harg, ← Complex.ofReal_log (le_of_lt hpos_sub)]
  congr 1
  have hinv : x - Real.sqrt (x * x - 1) = (x + Real.sqrt (x * x - 1))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x * x - 1 by nlinarith)]
  rw [hinv, Real.log_inv]
  push_cast; ring

/-- Branch cut of `arcsin` for all real `x > 1`:
    `arcsin(x) = π/2 - i · ln(x + √(x² - 1))`, matching `mpmath.asin`. -/
theorem extEmlArcsin_ofReal_gt_one {x : ℝ} (hx : 1 < x) :
    extEmlArcsin (.finite (x : ℂ)) =
      .finite ((Real.pi / 2 : ℂ) - Complex.I * (Real.log (x + Real.sqrt (x * x - 1)) : ℂ)) := by
  have h1 : (1 : ℂ) - (x : ℂ) * (x : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (x : ℂ) * (x : ℂ) = ((1 - x * x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by nlinarith)
  have hsq : ((1 : ℂ) - (x : ℂ) * (x : ℂ)) ^ ((1 : ℂ) / 2) =
      (Real.sqrt (x * x - 1) : ℂ) * Complex.I := by
    rw [show (1 : ℂ) - (x : ℂ) * (x : ℂ) = ((1 - x * x : ℝ) : ℂ) by push_cast; ring,
      cpow_half_ofReal_neg (by nlinarith), show -(1 - x * x) = x * x - 1 by ring]
  set r : ℝ := x + Real.sqrt (x * x - 1)
  have hr_pos : 0 < r := by positivity
  have harg : Complex.I * (x : ℂ) + ((1 : ℂ) - (x : ℂ) * (x : ℂ)) ^ ((1 : ℂ) / 2) =
      (r : ℂ) * Complex.I := by
    rw [hsq]; simp only [r]; push_cast; ring
  have h2 : Complex.I * (x : ℂ) + ((1 : ℂ) - (x : ℂ) * (x : ℂ)) ^ ((1 : ℂ) / 2) ≠ 0 := by
    rw [harg]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)) Complex.I_ne_zero
  rw [extEmlArcsin_eq h1 h2, harg]
  congr 1
  have hexp : Complex.exp ((Real.log r : ℂ) + (Real.pi / 2 : ℂ) * Complex.I) = (r : ℂ) * Complex.I := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr_pos, Complex.exp_pi_div_two_mul_I]
  rw [← hexp, Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos])]
  linear_combination -(Real.pi / 2 : ℂ) * Complex.I_mul_I

end Eml.InverseTrig
