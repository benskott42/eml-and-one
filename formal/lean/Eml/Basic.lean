/-
  Machine-checked Lean 4 + Mathlib formalization of the core EML operator
  and identities over `ℂ` on the lower branch cut (`Arg ∈ [-π, π)`).

  Every theorem is proved concretely over `ℂ` with zero `sorry` and zero
  custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Eml

/-- Predicate for the negative real axis `(-∞, 0)` (the branch cut of `log`). -/
def isNegReal (z : ℂ) : Prop :=
  z.re < 0 ∧ z.im = 0

/-- The lower-cut complex logarithm (`Arg ∈ [-π, π)`), matching the branch
    convention inside `eml` in EML and One: off the negative real axis it
    agrees with Mathlib's principal `Complex.log` (`Arg ∈ (-π, π]`), and on
    the negative real axis it takes argument `-π` instead of `+π`. -/
noncomputable def lowerLog (z : ℂ) : ℂ :=
  open Classical in
  if isNegReal z then Complex.log z - 2 * Real.pi * Complex.I else Complex.log z

theorem lowerLog_eq_log_of_not_isNegReal {z : ℂ} (hz : ¬ isNegReal z) :
    lowerLog z = Complex.log z := by
  simp [lowerLog, hz]

theorem lowerLog_eq_log_sub_of_isNegReal {z : ℂ} (hz : isNegReal z) :
    lowerLog z = Complex.log z - 2 * Real.pi * Complex.I := by
  simp [lowerLog, hz]

theorem lowerLog_one : lowerLog 1 = 0 := by
  have h : ¬ isNegReal (1 : ℂ) := by
    simp [isNegReal]
  rw [lowerLog_eq_log_of_not_isNegReal h, Complex.log_one]

theorem lowerLog_im_mem (z : ℂ) :
    -Real.pi ≤ (lowerLog z).im ∧ (lowerLog z).im < Real.pi := by
  by_cases hz : isNegReal z
  · rw [lowerLog_eq_log_sub_of_isNegReal hz]
    have harg : z.arg = Real.pi := Complex.arg_eq_pi_iff.mpr hz
    simp only [Complex.sub_im, Complex.log_im, harg, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      add_zero, sub_zero, zero_mul, Complex.re_ofNat, Complex.im_ofNat]
    constructor <;> linarith [Real.pi_pos]
  · rw [lowerLog_eq_log_of_not_isNegReal hz, Complex.log_im]
    have hmem := Complex.arg_mem_Ioc z
    have hne : z.arg ≠ Real.pi := mt Complex.arg_eq_pi_iff.mp hz
    exact ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hne⟩

theorem exp_lowerLog {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (lowerLog z) = z := by
  by_cases hneg : isNegReal z
  · rw [lowerLog_eq_log_sub_of_isNegReal hneg, Complex.exp_sub, Complex.exp_log hz,
      Complex.exp_two_pi_mul_I, div_one]
  · rw [lowerLog_eq_log_of_not_isNegReal hneg, Complex.exp_log hz]

theorem lowerLog_exp {z : ℂ} (h1 : -Real.pi ≤ z.im) (h2 : z.im < Real.pi) :
    lowerLog (Complex.exp z) = z := by
  by_cases hpi : z.im = -Real.pi
  · have hneg : isNegReal (Complex.exp z) := by
      constructor
      · rw [Complex.exp_re, hpi, Real.cos_neg, Real.cos_pi]
        linarith [Real.exp_pos z.re]
      · rw [Complex.exp_im, hpi, Real.sin_neg, Real.sin_pi, neg_zero, mul_zero]
    rw [lowerLog_eq_log_sub_of_isNegReal hneg]
    have hexp : Complex.exp z = Complex.exp (z + 2 * Real.pi * Complex.I) := by
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexp, Complex.log_exp]
    · ring
    · simp [hpi]; linarith [Real.pi_pos]
    · simp [hpi]; linarith [Real.pi_pos]
  · have h1' : -Real.pi < z.im := lt_of_le_of_ne h1 (Ne.symm hpi)
    have hnot : ¬ isNegReal (Complex.exp z) := by
      rintro ⟨hre, him⟩
      rw [Complex.exp_im] at him
      have hsin : Real.sin z.im = 0 :=
        (mul_eq_zero.mp him).resolve_left (ne_of_gt (Real.exp_pos z.re))
      rw [Real.sin_eq_zero_iff] at hsin
      rcases hsin with ⟨k, hk⟩
      have hk0 : k = 0 := by
        have hlt : (-1 : ℝ) < (k : ℝ) := by
          nlinarith [Real.pi_pos]
        have hgt : (k : ℝ) < (1 : ℝ) := by
          nlinarith [Real.pi_pos]
        have hk1 : (-1 : ℤ) < k := by exact_mod_cast hlt
        have hk2 : k < (1 : ℤ) := by exact_mod_cast hgt
        omega
      have hzim : z.im = 0 := by
        rw [← hk, hk0]; simp
      rw [Complex.exp_re, hzim, Real.cos_zero, mul_one] at hre
      linarith [Real.exp_pos z.re]
    rw [lowerLog_eq_log_of_not_isNegReal hnot, Complex.log_exp h1' (le_of_lt h2)]

/-- The lower-cut unwinding number `κ_L(z) = ⌊(Im z + π) / (2π)⌋`
    (Corless–Jeffrey, adapted to the lower branch `Arg ∈ [-π, π)`). -/
noncomputable def lowerUnwind (z : ℂ) : ℤ :=
  ⌊(z.im + Real.pi) / (2 * Real.pi)⌋

theorem lowerLog_exp_eq_sub_unwind (z : ℂ) :
    lowerLog (Complex.exp z) = z - 2 * Real.pi * Complex.I * (lowerUnwind z : ℂ) := by
  set k : ℤ := lowerUnwind z
  set w : ℂ := z - 2 * Real.pi * Complex.I * (k : ℂ)
  have hexp : Complex.exp z = Complex.exp w := by
    have hsub : z = w + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simp [w]; ring
    rw [hsub, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hle : (k : ℝ) ≤ (z.im + Real.pi) / (2 * Real.pi) := Int.floor_le _
  have hlt : (z.im + Real.pi) / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hle' : (k : ℝ) * (2 * Real.pi) ≤ z.im + Real.pi := (le_div_iff₀ hpi2).mp hle
  have hlt' : z.im + Real.pi < ((k : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ hpi2).mp hlt
  have hwim : w.im = z.im - 2 * Real.pi * (k : ℝ) := by
    simp [w]
  rw [hexp, lowerLog_exp]
  · rw [hwim]; linarith
  · rw [hwim]; linarith

theorem lowerUnwind_of_im_zero {z : ℂ} (hz : z.im = 0) : lowerUnwind z = 0 := by
  unfold lowerUnwind
  rw [hz, zero_add]
  have hdiv : Real.pi / (2 * Real.pi) = (1 : ℝ) / 2 := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [hdiv]
  rw [Int.floor_eq_iff]
  norm_num

theorem lowerUnwind_of_strip {z : ℂ} (h1 : -Real.pi ≤ z.im) (h2 : z.im < Real.pi) :
    lowerUnwind z = 0 := by
  unfold lowerUnwind
  rw [Int.floor_eq_iff]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  simp only [Int.cast_zero, zero_add]
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hpi2)
  · rw [div_lt_iff₀ hpi2]; linarith

theorem lowerLog_exp_of_im_zero {z : ℂ} (hz : z.im = 0) :
    lowerLog (Complex.exp z) = z := by
  rw [lowerLog_exp_eq_sub_unwind, lowerUnwind_of_im_zero hz]
  simp

theorem lowerLog_ofReal_pos {r : ℝ} (hr : 0 < r) :
    lowerLog (r : ℂ) = (Real.log r : ℂ) := by
  have hnot : ¬ isNegReal (r : ℂ) := by
    simp [isNegReal]; linarith
  rw [lowerLog_eq_log_of_not_isNegReal hnot, Complex.ofReal_log (le_of_lt hr)]

theorem lowerLog_ofReal_neg {r : ℝ} (hr : r < 0) :
    lowerLog (r : ℂ) = (Real.log (-r) : ℂ) - Real.pi * Complex.I := by
  have hneg : isNegReal (r : ℂ) := by
    simp [isNegReal, hr]
  rw [lowerLog_eq_log_sub_of_isNegReal hneg]
  have hpos : 0 < -r := by linarith
  have heq : (r : ℂ) = Complex.exp ((Real.log (-r) : ℂ) + Real.pi * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast; ring
  rw [heq, Complex.log_exp]
  · ring
  · simp; linarith [Real.pi_pos]
  · simp

/-- The principal-branch unwinding number `κ(z) = ⌈(Im z - π) / (2π)⌉`
    (Corless–Jeffrey, 1996). -/
noncomputable def principalUnwind (z : ℂ) : ℤ :=
  ⌈(z.im - Real.pi) / (2 * Real.pi)⌉

theorem log_exp_eq_sub_principalUnwind (z : ℂ) :
    Complex.log (Complex.exp z) = z - 2 * Real.pi * Complex.I * (principalUnwind z : ℂ) := by
  set k : ℤ := principalUnwind z
  set w : ℂ := z - 2 * Real.pi * Complex.I * (k : ℂ)
  have hexp : Complex.exp z = Complex.exp w := by
    have hsub : z = w + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simp [w]; ring
    rw [hsub, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hle : (z.im - Real.pi) / (2 * Real.pi) ≤ (k : ℝ) := Int.le_ceil _
  have hlt : (k : ℝ) - 1 < (z.im - Real.pi) / (2 * Real.pi) := by
    have h := Int.ceil_lt_add_one ((z.im - Real.pi) / (2 * Real.pi))
    change (k : ℝ) < (z.im - Real.pi) / (2 * Real.pi) + 1 at h
    linarith
  have hle' : z.im - Real.pi ≤ (k : ℝ) * (2 * Real.pi) := (div_le_iff₀ hpi2).mp hle
  have hlt' : ((k : ℝ) - 1) * (2 * Real.pi) < z.im - Real.pi := (lt_div_iff₀ hpi2).mp hlt
  have hwim : w.im = z.im - 2 * Real.pi * (k : ℝ) := by
    simp [w]
  rw [hexp, Complex.log_exp]
  · rw [hwim]; linarith
  · rw [hwim]; linarith

/-! ### The EML operator and core identities over `ℂ` -/

/-- The single binary EML operator over `ℂ` on the lower cut:
    `eml x y = exp x - lowerLog y`. -/
noncomputable def eml (x y : ℂ) : ℂ :=
  Complex.exp x - lowerLog y

/-- `e = eml 1 1` (RPN: `11E`, K = 3, hex `0x6`). -/
noncomputable def cE : ℂ := eml 1 1

theorem cE_eq_exp_one : cE = Complex.exp 1 := by
  simp [cE, eml, lowerLog_one]

/-- `0 = eml 1 (eml (eml 1 1) 1)` (RPN: `111E1EE`, K = 7, hex `0x74`). -/
noncomputable def cZero : ℂ := eml 1 (eml (eml 1 1) 1)

theorem cZero_eq_zero : cZero = 0 := by
  have he : (Complex.exp (1 : ℂ)).im = 0 := by
    rw [Complex.exp_im]; simp
  simp only [cZero, eml, lowerLog_one, sub_zero]
  rw [lowerLog_exp_of_im_zero he, sub_self]

/-- `exp x = eml x 1` (RPN: `x1E`, K = 3). -/
noncomputable def emlExp (x : ℂ) : ℂ := eml x 1

theorem emlExp_eq (x : ℂ) : emlExp x = Complex.exp x := by
  simp [emlExp, eml, lowerLog_one]

/-- The composed K = 7 logarithm word `emlLn x = eml 1 (eml (eml 1 x) 1)`
    (RPN: `11xE1EE`). Because the lower cut inside `eml` maps negative reals
    to argument `-π`, negating it in `e - lowerLog x` produces `+π`, whose
    exponential is again a negative real; the outer `lowerLog` takes `-π`
    and subtracting from `e` yields `+π`. Thus `emlLn` is unconditionally
    the *principal* logarithm `Complex.log` for all `x ≠ 0` (matching README.md). -/
noncomputable def emlLn (x : ℂ) : ℂ := eml 1 (eml (eml 1 x) 1)

theorem emlLn_eq_log (x : ℂ) : emlLn x = Complex.log x := by
  unfold emlLn eml
  rw [lowerLog_one, sub_zero]
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by
    rw [Complex.exp_im]; simp
  by_cases hneg : isNegReal x
  · rw [lowerLog_eq_log_sub_of_isNegReal hneg]
    have harg : x.arg = Real.pi := Complex.arg_eq_pi_iff.mpr hneg
    have hexp : Complex.exp (Complex.exp 1 - (Complex.log x - 2 * Real.pi * Complex.I)) =
        Complex.exp (Complex.exp 1 - Complex.log x) := by
      have h : Complex.exp 1 - (Complex.log x - 2 * Real.pi * Complex.I) =
          (Complex.exp 1 - Complex.log x) + 2 * Real.pi * Complex.I := by ring
      rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hexp, lowerLog_exp]
    · ring
    · simp [he1_im, Complex.log_im, harg]
    · simp [he1_im, Complex.log_im, harg]; linarith [Real.pi_pos]
  · rw [lowerLog_eq_log_of_not_isNegReal hneg]
    have hmem := Complex.arg_mem_Ioc x
    have hne : x.arg ≠ Real.pi := mt Complex.arg_eq_pi_iff.mp hneg
    have hlt : x.arg < Real.pi := lt_of_le_of_ne hmem.2 hne
    rw [lowerLog_exp]
    · ring
    · simp [he1_im, Complex.log_im]; linarith
    · simp [he1_im, Complex.log_im]; linarith [hmem.1]

theorem emlLn_eq_lowerLog {x : ℂ} (hx : ¬ isNegReal x) : emlLn x = lowerLog x := by
  rw [emlLn_eq_log, lowerLog_eq_log_of_not_isNegReal hx]

/-- The `0xc` binary nibble identity (`docs/binary.md`):
    appending `1100₂` (`11EE`) to any program `X` computes `eml X (eml 1 1) = exp X - 1`. -/
noncomputable def append0xc (x : ℂ) : ℂ := eml x (eml 1 1)

theorem append0xc_eq (x : ℂ) : append0xc x = Complex.exp x - 1 := by
  unfold append0xc eml
  rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp)]

/-- Raw subtraction word `11xE1EEy1EE` (K = 11): `eml (emlLn a) (emlExp b)`. -/
noncomputable def rawSub (a b : ℂ) : ℂ := eml (emlLn a) (emlExp b)

/-- Exact formula for `rawSub` for all `a ≠ 0` and any `b : ℂ`, showing the
    Corless–Jeffrey unwinding term `2πi · lowerUnwind b`. -/
theorem rawSub_eq_sub_add_unwind {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    rawSub a b = a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ) := by
  unfold rawSub eml
  rw [emlLn_eq_log, emlExp_eq, Complex.exp_log ha, lowerLog_exp_eq_sub_unwind]
  ring

/-- `rawSub a b = a - b` when `a ≠ 0` and `b` lies in the lower strip `Im b ∈ [-π, π)`. -/
theorem rawSub_eq {a b : ℂ} (ha : a ≠ 0) (h1 : -Real.pi ≤ b.im) (h2 : b.im < Real.pi) :
    rawSub a b = a - b := by
  rw [rawSub_eq_sub_add_unwind ha b, lowerUnwind_of_strip h1 h2]
  simp

/-- Direct `eml` form for `1 - x` on the lower strip `Im x ∈ [-π, π)`. -/
theorem eml_zero_exp {x : ℂ} (h1 : -Real.pi ≤ x.im) (h2 : x.im < Real.pi) :
    eml cZero (emlExp x) = 1 - x := by
  unfold eml
  rw [cZero_eq_zero, Complex.exp_zero, emlExp_eq, lowerLog_exp h1 h2]

end Eml
