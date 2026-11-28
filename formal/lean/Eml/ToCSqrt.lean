import Eml.AppOps

namespace Eml
open Eml Eml.DirectedInf Eml.AppSub Eml.AppOps
set_option maxHeartbeats 400000
theorem dirEmlSqrt_negZero' : dirEmlSqrt .negZero = .finite 0 := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have h12_ne : eml 1 2 ≠ 0 := by
    intro h
    have hsub : Complex.exp 1 = lowerLog 2 := sub_eq_zero.mp h
    have heq : (2 : ℂ) = Complex.exp (Complex.exp 1) := by
      rw [← exp_lowerLog h2_ne, ← hsub]
    have hre : (2 : ℝ) = Real.exp (Real.exp 1) := by
      have := congrArg Complex.re heq
      simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 1 < Real.exp (Real.exp 1) := by
      have := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1)); linarith
    linarith
  have h12_im : (eml 1 2).im = 0 := by
    unfold eml
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_pos (by norm_num)]
    rw [Complex.sub_im, he1_im, Complex.ofReal_im, sub_zero]
  unfold dirEmlSqrt
  rw [dirEmlLn_negZero, dirCTwo_eq_two]
  unfold dirEmlDiv
  rw [dirEml_finite h2_ne, dirEmlLn_finite_ne_zero h12_ne]
  have hstep1 : dirEml (.finite 1) (.negInf Real.pi) = .negInf (-Real.pi) := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im, Real.pi_pos]
  rw [hstep1, dirEmlExp_eq, dirEmlExp_eq]
  have hinner : dirEmlExp (.negInf (-Real.pi)) = .negZero := by
    rw [dirEmlExp_eq]; simp [dirExp]
  rw [hinner]
  have hstep3 : dirEml (.finite (Complex.log (eml 1 2))) .negZero = .posInf Real.pi := by
    have hexp_im : (Complex.exp (Complex.log (eml 1 2))).im = 0 := by
      rw [Complex.exp_log h12_ne, h12_im]
    simp [dirEml, dirExp, dirLowerLog, dirSub, hexp_im]
  rw [hstep3]
  change dirExp (.dirInf Real.pi) = .finite 0
  simp [dirExp, Real.cos_pi, Real.sin_pi]
theorem sqrt_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml sqrtToks [] = some [.finite (a ^ ((1 : ℂ) / 2))] := by
  rcases toC_eq hv with h | ⟨h, ha⟩
  · subst h; rw [sqrtToks_eval, dirEmlSqrt_all]
  · subst h; subst ha
    rw [sqrtToks_eval, dirEmlSqrt_negZero', Complex.zero_cpow (by norm_num)]

theorem sqrt_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml sqrtToks [] = some [.finite (a ^ ((1 : ℂ) / 2))] :=
  sqrt_correct_toC' hv y
end Eml
