import Eml.AppOps
import Eml.InverseTrig
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Eml
open Complex Eml.InverseTrig Eml.Extended


/-- C3a: `√(1−z)·√(1+z) = √(1−z²)` for every `z` (principal roots). -/
theorem sqrt_one_sub_mul_sqrt_one_add (z : ℂ) :
    (1 - z) ^ ((1 : ℂ) / 2) * (1 + z) ^ ((1 : ℂ) / 2) = (1 - z * z) ^ ((1 : ℂ) / 2) := by
  have hhalf : (1 : ℂ) / 2 ≠ 0 := by norm_num
  by_cases h1 : 1 - z = 0
  · have : 1 - z * z = 0 := by
      have hz : z = 1 := by linear_combination -h1
      subst hz; ring
    rw [h1, this, zero_cpow hhalf, zero_mul]
  by_cases h2 : 1 + z = 0
  · have : 1 - z * z = 0 := by
      have hz : z = -1 := by linear_combination h2
      subst hz; ring
    rw [h2, this, zero_cpow hhalf, mul_zero]
  have h3 : 1 - z * z = (1 - z) * (1 + z) := by ring
  have him1 : (1 - z).im = -z.im := by simp
  have him2 : (1 + z).im = z.im := by simp
  have hre1 : (1 - z).re = 1 - z.re := by simp
  have hre2 : (1 + z).re = 1 + z.re := by simp
  have harg : arg (1 - z) + arg (1 + z) ∈ Set.Ioc (-Real.pi) Real.pi := by
    have l1 := neg_pi_lt_arg (1 - z); have l2 := neg_pi_lt_arg (1 + z)
    have u1 := arg_le_pi (1 - z); have u2 := arg_le_pi (1 + z)
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · have a2 : arg (1 + z) < 0 := arg_neg_iff.2 (by rw [him2]; exact hz)
      have a1 : 0 ≤ arg (1 - z) := arg_nonneg_iff.2 (by rw [him1]; linarith)
      constructor <;> linarith
    · have c1 : arg (1 - z) = 0 ∨ arg (1 - z) = Real.pi := by
        by_cases hr : 0 ≤ (1 - z).re
        · exact Or.inl (arg_eq_zero_iff.2 ⟨hr, by rw [him1, hz]; simp⟩)
        · exact Or.inr (arg_eq_pi_iff.2 ⟨by linarith, by rw [him1, hz]; simp⟩)
      have c2 : arg (1 + z) = 0 ∨ arg (1 + z) = Real.pi := by
        by_cases hr : 0 ≤ (1 + z).re
        · exact Or.inl (arg_eq_zero_iff.2 ⟨hr, by rw [him2, hz]⟩)
        · exact Or.inr (arg_eq_pi_iff.2 ⟨by linarith, by rw [him2, hz]⟩)
      have hpi := Real.pi_pos
      rcases c1 with e1 | e1 <;> rcases c2 with e2 | e2
      · rw [e1, e2]; constructor <;> linarith
      · rw [e1, e2]; constructor <;> linarith
      · rw [e1, e2]; constructor <;> linarith
      · exfalso
        have q1 := (arg_eq_pi_iff.1 e1).1; have q2 := (arg_eq_pi_iff.1 e2).1
        rw [hre1] at q1; rw [hre2] at q2; linarith
    · have a1 : arg (1 - z) < 0 := arg_neg_iff.2 (by rw [him1]; linarith)
      have a2 : 0 ≤ arg (1 + z) := arg_nonneg_iff.2 (by rw [him2]; linarith)
      constructor <;> linarith
  rw [h3, cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, cpow_def_of_ne_zero (mul_ne_zero h1 h2),
    ← Complex.exp_add, (log_mul_eq_add_log_iff h1 h2).2 harg]
  congr 1; ring

/-- C3b (1): `(iz + R)(R − iz) = 1`, `R = √(1 − z²)`. Uses the landed `sq_sqrt`. -/
theorem asin_arg_mul_conj (z : ℂ) :
    (I * z + (1 - z * z) ^ ((1 : ℂ) / 2)) * ((1 - z * z) ^ ((1 : ℂ) / 2) - I * z) = 1 := by
  have hR := Eml.AppOps.sq_sqrt (1 - z * z)
  linear_combination hR - z * z * Complex.I_sq

theorem sqrt_re_nonneg (u : ℂ) : 0 ≤ (u ^ ((1 : ℂ) / 2)).re := by
  rw [one_div, cpow_inv_two_re]; exact Real.sqrt_nonneg _

/-- C3b (2'): `Re (iz + √(1−z²)) ≥ 0` (stronger than `arg ≠ π`). -/
theorem asin_arg_re_nonneg (z : ℂ) : 0 ≤ (I * z + (1 - z * z) ^ ((1 : ℂ) / 2)).re := by
  set R := (1 - z * z) ^ ((1 : ℂ) / 2) with hRdef
  set w := I * z + R with hw
  have hprod : w * (R - I * z) = 1 := asin_arg_mul_conj z
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hu : R - I * z = w⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hsum : w.re + (R - I * z).re = 2 * R.re := by
    simp only [hw, Complex.add_re, Complex.sub_re]; ring
  have hR : 0 ≤ R.re := sqrt_re_nonneg _
  by_contra h
  push_neg at h
  have hinv : (w⁻¹).re < 0 := by
    rw [Complex.inv_re]; exact div_neg_of_neg_of_pos h (Complex.normSq_pos.2 hw0)
  rw [hu] at hsum
  linarith

theorem asin_arg_ne_negReal (z : ℂ) : (I * z + (1 - z * z) ^ ((1 : ℂ) / 2)).arg ≠ Real.pi := by
  intro h
  have := (arg_eq_pi_iff.1 h).1
  linarith [asin_arg_re_nonneg z]

/-- C3g, for EVERY `a` (no hypotheses): the arccos word's value `π/2 − arcsin a`
equals the InverseTrig `extEmlArccos` right-hand side. -/
theorem arccos_value_eq_ext (a : ℂ) :
    (Real.pi : ℂ) / 2 - -I * log (I * a + (1 - a * a) ^ ((1 : ℂ) / 2)) =
      -I * log (a + I * ((1 - a) ^ ((1 : ℂ) / 2) * (1 + a) ^ ((1 : ℂ) / 2))) := by
  rw [sqrt_one_sub_mul_sqrt_one_add]
  set R := (1 - a * a) ^ ((1 : ℂ) / 2) with hRdef
  set w := I * a + R with hw
  have hprod : w * (R - I * a) = 1 := asin_arg_mul_conj a
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hu : R - I * a = w⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hre : 0 ≤ w.re := asin_arg_re_nonneg a
  have hnpi : w.arg ≠ Real.pi := asin_arg_ne_negReal a
  have habs : |w.arg| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.2 hre
  have hkey : a + I * R = I * w⁻¹ := by
    rw [← hu]; linear_combination a * Complex.I_sq
  have harg : arg I + arg w⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [arg_I, arg_inv, if_neg hnpi]
    have := abs_le.1 habs
    have hpi := Real.pi_pos
    constructor <;> linarith
  rw [hkey, (log_mul_eq_add_log_iff I_ne_zero (inv_ne_zero hw0)).2 harg, log_I, log_inv w hnpi]
  linear_combination ((Real.pi : ℂ) / 2) * Complex.I_sq

/-- Corollary: where the landed `extEmlArccos_eq` applies, it is the word's value.
(`hsum` is automatic: `a + i·R = i·w⁻¹ ≠ 0`.) -/
theorem extEmlArccos_eq_word {a : ℂ} (hm : 1 - a ≠ 0) (hp : 1 + a ≠ 0) :
    extEmlArccos (.finite a) =
      .finite ((Real.pi : ℂ) / 2 - -I * log (I * a + (1 - a * a) ^ ((1 : ℂ) / 2))) := by
  have hsum : a + I * ((1 - a) ^ ((1 : ℂ) / 2) * (1 + a) ^ ((1 : ℂ) / 2)) ≠ 0 := by
    rw [sqrt_one_sub_mul_sqrt_one_add]
    have hprod := asin_arg_mul_conj a
    have hw0 := left_ne_zero_of_mul_eq_one hprod
    have hu := eq_inv_of_mul_eq_one_right hprod
    have : a + I * (1 - a * a) ^ ((1 : ℂ) / 2) = I * (I * a + (1 - a * a) ^ ((1 : ℂ) / 2))⁻¹ := by
      rw [← hu]; linear_combination a * Complex.I_sq
    rw [this]; exact mul_ne_zero I_ne_zero (inv_ne_zero hw0)
  rw [extEmlArccos_eq hm hp hsum, arccos_value_eq_ext]



end Eml
