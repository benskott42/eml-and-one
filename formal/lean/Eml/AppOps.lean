/-
  The calculator's other compiled operators, proved for all inputs.

  With variable operands the compiler emits (`lib/eml/lowering.ts`, `library.ts`):

    x + y   the `x − y` circuit with operand `(−1)·y` and scale from `y` (655 tokens)
    x · y   the stored `mul` word                 `dirEmlMul x y`
    x / y   the stored `div` word                 `dirEmlDiv x y`
    −x      `(−1)·x`                              `dirEmlMul dirCNegOne x`
    x²      `exp(2·ln x)`                         `dirEmlExp (dirEmlMul dirCTwo (dirEmlLn x))`
    2·x                                           `dirEmlMul dirCTwo x`
    1/x                                           `dirEmlDiv 1 x`
    √x      the stored `sqrt` word                `dirEmlSqrt x`
    exp x   `x1E`;   ln x   `11xE1EE`
    x − 1, x + 1, x − 2   the unscaled rotation `rotSub(x, c)` (`appRot`)
    x ^ y   `exp(y·ln x)`;  e ^ x  `exp(x·ln e)`;  x ^ 3  `exp(3·ln x)` with the `3` word
    x · 2, x / 2                                  `dirEmlMul x dirCTwo`, `dirEmlDiv x dirCTwo`

  Each token list below is the compiler's word for that operator (`APP_WORDS` in
  `lib/eml/export.ts`; check 115 and the Lean bridge compare them), and unfolds by `rfl`
  to the Lean circuit. Values, in `EmlDir`:

  * `x + y`, `2·x`, `x²`, `√x`, `exp x`, `x ± 1`, `x − 2`, `e^x`, `x·2`, `x/2`, `x³`: exactly
    the value, for all inputs.
  * `x ^ y`: exactly the principal `a ^ b` for `a ≠ 0`.
  * `x · y` and `−x`: the value up to the sign of zero (`(−1)·0 = −0`, as in IEEE).
  * `x / y` and `1/x` for a nonzero divisor, up to the sign of a zero quotient.
  * `ln x`: the principal `Complex.log x` for `x ≠ 0`, and `−∞` at `0`.

  `valueOf` reads a one-value stack as a complex number, with `−0` as `0`.

  `*_correct_toC'` (`Eml.ToCClean`, `Eml.ToCAdd`, `Eml.ToCSqrt`) is the form
  `Tok.subst` needs: the operand is whatever `toC` reads. The only `≠ −0`
  hypotheses left are the exact forms of `twoMul` and `divTwo`
  (`twoMul_negZero`, `divTwo_negZero`) and the infinite-output cases
  (`ln`, `inv`, division by `0`, `pow` at `0`). `exp` accepts `−0`
  (`dirExp .negZero = .finite 1`). `sinh_correct'` and `cosh_correct'` hold for
  every `a`.

  Composed from those words with `Tok.subst` (the token list is the compiler's word):

  * `sigma x`: `1 / (1 + exp (−x))` when the denominator is not `0`.
  * `sinh x` and `cosh x`: the value for every `x` (`sinh_correct'`, `cosh_correct'`).
    The factor `1/2` is the K 29 word; `certifyDir` decides it (`half_dir`).
  * `artanh x`: `log (√(1+x) / √(1−x))` for `x ≠ ±1`.
  * `arcosh x`: `log (x + √(x−1)·√(x+1))` for every `x` (`arcosh_arg_ne`).
  * `sin x`: `(exp(i·x) − exp(−i·x)) / (2·i)`, read by `valueOf` (a zero sine may be `−0`).
  * `cos x`: `(exp(i·x) + exp(−i·x)) / 2` for every `x`.
  * `tan x`: `−i·(1 − 2/(exp(2·i·x) + 1))` when `cos x ≠ 0`.
  * `tanh x`: `(exp(2x) − 1)/(exp(2x) + 1)` when the denominator is not `0`.
  * `arctan x`: `−i·log(√(1+i·x)/√(1−i·x))` for `x ≠ ±i`.
    `i` is `exp(iπ/2)` (K 57) and `−i` is the short minus word on it.

  Zero `sorry`, zero custom axioms.
-/
import Eml.AppSub
import Eml.CertDir

namespace Eml.AppOps

open Eml Eml.DirectedInf Eml.AppSub Eml.Cert

/-! ### Reading a result -/

/-- An `EmlDir` value as a complex number: finite values, and `−0` as `0`. -/
noncomputable def toC : EmlDir → Option ℂ
  | .finite z => some z
  | .negZero => some 0
  | _ => none

/-- A one-value stack as a complex number (`toC` of its value). -/
noncomputable def valueOf : Option (List EmlDir) → Option ℂ
  | some [v] => toC v
  | _ => none

private theorem one_not_neg : ¬ ((1 : ℝ) < 0) := by norm_num

private theorem exp_one_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp

/-! ### Multiplication -/

/-- `0 · b = +0` for `b ≠ 0`: `ln 0 = −∞`, `exp(+∞) = +∞`, `ln(+∞) = +∞`, `e − ∞ = −∞`. -/
theorem dirEmlMul_zero_left {b : ℂ} (hb : b ≠ 0) :
    dirEmlMul (.finite 0) (.finite b) = .finite 0 := by
  unfold dirEmlMul dirEmlLn
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one, exp_one_im, one_not_neg, hb]

/-- `a · 0` is `+0` or `−0` (`−0` when `Re a < 0`, as `(−1)·0` in IEEE). -/
theorem toC_dirEmlMul_zero_right (a : ℂ) : toC (dirEmlMul (.finite a) (.finite 0)) = some 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlMul_zero_zero]
    rfl
  by_cases hre : 0 ≤ a.re
  · rw [dirEmlMul_eq ha hre, mul_zero]
    rfl
  have hae : eml 1 a ≠ 0 := by
    intro h
    have hsub : Complex.exp 1 = lowerLog a := sub_eq_zero.mp h
    have ha_eq : a = Complex.exp (Complex.exp 1) := by rw [← exp_lowerLog ha, ← hsub]
    have hpos : 0 < (Complex.exp (Complex.exp 1)).re := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_re]
      exact Real.exp_pos _
    rw [ha_eq] at hre
    exact hre hpos.le
  unfold dirEmlMul
  rw [dirEml_finite ha, dirEmlLn_finite_ne_zero hae]
  by_cases hcos : Real.cos (Complex.exp (Complex.log (eml 1 a))).im < 0
  · simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, hcos, toC]
  · simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, hcos, one_not_neg, toC]

/-- The `mul` word is `a · b` for all `a b : ℂ`, up to the sign of a zero product. -/
theorem toC_dirEmlMul (a b : ℂ) : toC (dirEmlMul (.finite a) (.finite b)) = some (a * b) := by
  by_cases hb : b = 0
  · subst hb
    rw [mul_zero]
    exact toC_dirEmlMul_zero_right a
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlMul_zero_left hb, zero_mul]
    rfl
  rw [dirEmlMul_eq_of_ne_zero ha hb]
  rfl

/-- `(−1) · 0 = −0`. -/
theorem dirEmlMul_negOne_zero : dirEmlMul (.finite (-1)) (.finite 0) = .negZero := by
  have hne : eml 1 (-1) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hl : lowerLog (-1 : ℂ) = -(Real.pi * Complex.I) := by
      rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
      simp
    simp [eml, hl, exp_one_im, Real.pi_ne_zero] at him
  have him : (Complex.exp (Complex.log (eml 1 (-1)))).im = Real.pi := by
    rw [Complex.exp_log hne]
    have hl : lowerLog (-1 : ℂ) = -(Real.pi * Complex.I) := by
      rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
      simp
    simp [eml, hl, exp_one_im]
  unfold dirEmlMul
  rw [dirEml_finite (by norm_num), dirEmlLn_finite_ne_zero hne]
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, him]

/-! ### Division -/

/-- `0 / b` is `+0` or `−0` for `b ≠ 0`. -/
theorem toC_dirEmlDiv_zero_left {b : ℂ} (hb : b ≠ 0) :
    toC (dirEmlDiv (.finite 0) (.finite b)) = some 0 := by
  have h1a : dirEmlExp (dirEml (.finite 1) (.finite 0)) = .dirInf 0 := by
    simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im]
  unfold dirEmlDiv
  rw [dirEml_finite hb, h1a]
  by_cases hbe : eml 1 b = 0
  · rw [hbe, dirEmlLn_zero]
    simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, one_not_neg, toC]
  · rw [dirEmlLn_finite_ne_zero hbe]
    by_cases hcos : Real.cos (Complex.exp (Complex.log (eml 1 b))).im < 0
    · simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, hcos, one_not_neg, toC]
    · simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, hcos, one_not_neg, toC]

/-- The `div` word is `a / b` for all `a` and `b ≠ 0`, up to the sign of a zero quotient. -/
theorem toC_dirEmlDiv (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    toC (dirEmlDiv (.finite a) (.finite b)) = some (a / b) := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_div]
    exact toC_dirEmlDiv_zero_left hb
  rw [dirEmlDiv_eq_of_ne_zero ha hb]
  rfl

/-! ### One-operand words -/

theorem dirEmlTwoMul (a : ℂ) : dirEmlMul dirCTwo (.finite a) = .finite (2 * a) := by
  rw [dirCTwo_eq_two, dirEmlMul_eq two_ne_zero (by norm_num)]

/-- `2 · (−∞) = ∞·e^{iπ}` (the directed `−∞`). -/
theorem dirEmlMul_two_negInf : dirEmlMul (.finite 2) (.negInf 0) = .dirInf Real.pi := by
  have h12_ne : eml 1 2 ≠ 0 := by
    intro h
    have hsub : Complex.exp 1 = lowerLog 2 := sub_eq_zero.mp h
    have heq : (2 : ℂ) = Complex.exp (Complex.exp 1) := by
      rw [← exp_lowerLog (two_ne_zero : (2 : ℂ) ≠ 0), ← hsub]
    have hre : (2 : ℝ) = Real.exp (Real.exp 1) := by
      have := congrArg Complex.re heq
      simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 1 < Real.exp (Real.exp 1) := by
      have := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1)); linarith
    linarith
  have h12_im : (Complex.exp (Complex.log (eml 1 2))).im = 0 := by
    rw [Complex.exp_log h12_ne]
    unfold eml
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_pos (by norm_num)]
    rw [Complex.sub_im, exp_one_im, Complex.ofReal_im, sub_zero]
  unfold dirEmlMul
  rw [dirEml_finite two_ne_zero, dirEmlLn_finite_ne_zero h12_ne]
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, h12_im]

/-- The `x²` word, `exp(2 · ln x)`, is `a²` for all `a`, `0` included. -/
theorem dirEmlSq (a : ℂ) :
    dirEmlExp (dirEmlMul dirCTwo (dirEmlLn (.finite a))) = .finite (a ^ 2) := by
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlLn_zero, dirCTwo_eq_two, dirEmlMul_two_negInf, dirEmlExp_eq]
    simp [dirExp]
  rw [dirEmlLn_finite_ne_zero ha, dirEmlTwoMul, dirEmlExp_eq]
  simp only [dirExp]
  congr 1
  rw [two_mul, Complex.exp_add, Complex.exp_log ha]
  ring

/-- The `sqrt` word is the principal `a ^ (1/2)` for all `a`, `0` included. -/
theorem dirEmlSqrt_all (a : ℂ) : dirEmlSqrt (.finite a) = .finite (a ^ ((1 : ℂ) / 2)) := by
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlSqrt_zero, Complex.zero_cpow (by norm_num)]
  exact dirEmlSqrt_finite ha

/-! ### Addition -/

/-- The compiled `x + y`: the scaled rotation of `x − ((−1)·y)`, scale from `y`. -/
noncomputable def appAdd (x y : EmlDir) : EmlDir := appSubGen x y (dirEmlMul dirCNegOne y)

theorem dirRawSub_negZero (w : ℂ) : dirRawSub (.finite w) .negZero = .finite w := by
  unfold dirRawSub
  rw [dirEmlExp_eq]
  unfold dirEml
  rw [dirExp_dirEmlLn_finite]
  simp [dirExp, dirLowerLog, dirSub, lowerLog_one]

theorem shortSub_negZero {H : EmlDir} (hH : dirExp H = .negZero) :
    shortSub H .negZero = .negZero := by
  unfold shortSub dirEml
  rw [hH, dirEmlExp_eq]
  simp [dirExp, dirLowerLog, dirSub, lowerLog_one]

/-- `(−0) / 1 = −0`. -/
theorem dirEmlDiv_negZero_one : dirEmlDiv .negZero (.finite 1) = .negZero := by
  have he : dirEml (.finite 1) (.finite 1) = .finite (Complex.exp 1) := by
    rw [dirEml_finite one_ne_zero]; congr 1; exact cE_eq_exp_one
  have hlog : Complex.log (Complex.exp 1) = 1 := by
    rw [Complex.log_exp]
    · simp [Real.pi_pos]
    · simp [Real.pi_pos.le]
  unfold dirEmlDiv
  rw [he, dirEmlLn_finite_ne_zero (Complex.exp_ne_zero _), hlog]
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im]

/-- `(iπ) · (−0) = +0`. -/
theorem dirEmlMul_ipi_negZero : dirEmlMul (.finite (Real.pi * Complex.I)) .negZero = .finite 0 := by
  have hc_ne : (Real.pi : ℂ) * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hlog : lowerLog ((Real.pi : ℂ) * Complex.I) =
      (Real.log Real.pi : ℂ) + (Real.pi / 2 : ℝ) * Complex.I := by
    have hnot : ¬ isNegReal ((Real.pi : ℂ) * Complex.I) := by
      simp [isNegReal, Real.pi_ne_zero]
    rw [lowerLog_eq_log_of_not_isNegReal hnot]
    apply Complex.ext
    · simp [Complex.log_re, abs_of_pos Real.pi_pos]
    · simp only [Complex.log_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
      rw [Complex.arg_real_mul _ Real.pi_pos, Complex.arg_I]
      ring
  have hce : eml 1 ((Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [eml, hlog, exp_one_im, Real.pi_ne_zero] at him
  have him : (Complex.exp (Complex.log (eml 1 ((Real.pi : ℂ) * Complex.I)))).im = -(Real.pi / 2) := by
    rw [Complex.exp_log hce]
    simp [eml, hlog, exp_one_im]
  unfold dirEmlMul
  rw [dirEml_finite hc_ne, dirEmlLn_finite_ne_zero hce]
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, him, one_not_neg]

/-- `x + 0`: the operand `(−1)·0` is `−0`, and the circuit still returns `a`. -/
theorem appSubGen_negZero (a : ℂ) : appSubGen (.finite a) (.finite 0) .negZero = .finite a := by
  set c : ℂ := Real.pi * Complex.I with hc
  have hc_re : c.re = 0 := by simp [c]
  have hc_ne : c ≠ 0 := by simp [c, Real.pi_ne_zero, Complex.I_ne_zero]
  have hk1 : shortSub (sqrtBody (dirEmlSqr (.finite 0))) dirCNegOne = .finite 1 := by
    have hs0 : dirEmlSqrt (dirEmlSqr (.finite 0)) = .finite 0 := by
      unfold dirEmlSqr; rw [dirEmlMul_zero_zero, dirEmlSqrt_zero]
    have hH : dirExp (sqrtBody (dirEmlSqr (.finite 0))) = .finite 0 := by
      rw [← dirEmlExp_eq]; exact hs0
    rw [shortSub_eq hH, dirEmlExp_eq, hH, dirCNegOne_eq_negOne, dirRawSub_eq,
      lowerUnwind_of_im_zero (by simp)]
    congr 1
    push_cast
    ring
  unfold appSubGen
  dsimp only
  rw [hk1, dirCIpi_eq, dirEmlDiv_negZero_one]
  have hx : dirExp (divBody (.finite a) (.finite 1)) = .finite (a / 1) := by
    rw [← dirEmlExp_eq]; exact dirEmlDiv_eq a one_ne_zero (by norm_num)
  have hdx : dirEmlExp (divBody (.finite a) (.finite 1)) = .finite (a / 1) :=
    dirEmlDiv_eq a one_ne_zero (by norm_num)
  have hy : dirExp (divBody .negZero (.finite 1)) = .negZero := by
    rw [← dirEmlExp_eq]; exact dirEmlDiv_negZero_one
  rw [shortSub_eq hx, hdx, dirRawSub_negZero, shortSub_negZero hy, dirEmlMul_ipi_negZero]
  have hm : dirExp (mulBody (.finite c) (.finite (a / 1))) = .finite (c * (a / 1)) := by
    rw [← dirEmlExp_eq]; exact dirEmlMul_eq hc_ne (le_of_eq hc_re.symm) (a / 1)
  have hdm : dirEmlExp (mulBody (.finite c) (.finite (a / 1))) = .finite (c * (a / 1)) :=
    dirEmlMul_eq hc_ne (le_of_eq hc_re.symm) (a / 1)
  rw [shortSub_eq hm, hdm, dirRawSub_eq, lowerUnwind_of_im_zero (by simp),
    dirEmlDiv_eq _ hc_ne (le_of_eq hc_re.symm), dirEmlMul_eq one_ne_zero (by norm_num)]
  congr 1
  field_simp
  push_cast
  ring

/-- The compiled `x + y` is exactly `a + b`, for all `a b : ℂ`. -/
theorem appAdd_finite (a b : ℂ) : appAdd (.finite a) (.finite b) = .finite (a + b) := by
  unfold appAdd
  rw [dirCNegOne_eq_negOne]
  by_cases hb : b = 0
  · subst hb
    rw [dirEmlMul_negOne_zero, appSubGen_negZero, add_zero]
  rw [dirEmlMul_eq_of_ne_zero (by norm_num) hb, appSubGen_finite]
  congr 1
  ring

/-! ### `x − c` for a constant `c`: the unscaled rotation -/

/-- The compiler's `x − b` for a constant `b` inside the float strip (`rotSub`, no scale):
    `(c·(x − b) − c·(b − b)) / c`, with the `subOfExp` shortcut on the outer subtraction. -/
noncomputable def appRot (x b : EmlDir) : EmlDir :=
  dirEmlDiv (shortSub (mulBody dirCIpi (dirRawSub x b)) (dirEmlMul dirCIpi (dirRawSub b b)))
    dirCIpi

/-- The unscaled rotation is `a − v` for all finite `a`, `v`. -/
theorem appRot_finite (a v : ℂ) : appRot (.finite a) (.finite v) = .finite (a - v) := by
  set c : ℂ := Real.pi * Complex.I with hc
  have hc_re : c.re = 0 := by simp [c]
  have hc_ne : c ≠ 0 := by simp [c, Real.pi_ne_zero, Complex.I_ne_zero]
  unfold appRot
  rw [dirCIpi_eq]
  have hm : dirExp (mulBody (.finite c) (dirRawSub (.finite a) (.finite v))) =
      .finite (c * (a - v + 2 * Real.pi * Complex.I * (lowerUnwind v : ℂ))) := by
    rw [← dirEmlExp_eq]
    show dirEmlMul (.finite c) (dirRawSub (.finite a) (.finite v)) = _
    rw [dirRawSub_eq, dirEmlMul_eq hc_ne (le_of_eq hc_re.symm)]
  rw [shortSub_eq hm]
  exact dirRotSub_eq_sub hc_re hc_ne a v

/-! ### Powers, `e^x`, and scaling by `2` -/

theorem dirExp_of_toC {z : EmlDir} {w : ℂ} (h : toC z = some w) :
    dirExp z = .finite (Complex.exp w) := by
  cases z with
  | finite u =>
    simp only [toC, Option.some.injEq] at h
    subst h
    rfl
  | negZero =>
    simp only [toC, Option.some.injEq] at h
    subst h
    simp [dirExp]
  | posInf _ => simp [toC] at h
  | negInf _ => simp [toC] at h
  | dirInf _ => simp [toC] at h
  | nan => simp [toC] at h

/-- `x ^ y`, compiled as `exp(y · ln x)`, is exactly the principal `a ^ b` for `a ≠ 0`. -/
theorem dirEmlPow {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    dirEmlExp (dirEmlMul (.finite b) (dirEmlLn (.finite a))) = .finite (a ^ b) := by
  rw [dirEmlLn_finite_ne_zero ha, dirEmlExp_eq, dirExp_of_toC (toC_dirEmlMul b (Complex.log a)),
    Complex.cpow_def_of_ne_zero ha, mul_comm]

/-- `r · (−∞) = ∞·e^{iπ}` for a positive real `r ≠ e^e`. -/
theorem dirEmlMul_pos_negInf {r : ℝ} (hr : 0 < r) (hre : r ≠ Real.exp (Real.exp 1)) :
    dirEmlMul (.finite (r : ℂ)) (.negInf 0) = .dirInf Real.pi := by
  have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hne : eml 1 (r : ℂ) ≠ 0 := by
    intro h
    have hsub : Complex.exp 1 = lowerLog (r : ℂ) := sub_eq_zero.mp h
    rw [lowerLog_ofReal_pos hr] at hsub
    have hre' : Real.exp 1 = Real.log r := by
      have := congrArg Complex.re hsub
      simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
    apply hre
    rw [hre', Real.exp_log hr]
  have him : (Complex.exp (Complex.log (eml 1 (r : ℂ)))).im = 0 := by
    rw [Complex.exp_log hne]
    unfold eml
    rw [lowerLog_ofReal_pos hr, Complex.sub_im, exp_one_im, Complex.ofReal_im, sub_zero]
  unfold dirEmlMul
  rw [dirEml_finite hr_ne, dirEmlLn_finite_ne_zero hne]
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, him]

/-- `x ^ r` for a positive real constant `r ≠ e^e` is exactly `a ^ r`, `0` included. -/
theorem dirEmlPowReal {r : ℝ} (hr : 0 < r) (hre : r ≠ Real.exp (Real.exp 1)) (a : ℂ) :
    dirEmlExp (dirEmlMul (.finite (r : ℂ)) (dirEmlLn (.finite a))) = .finite (a ^ (r : ℂ)) := by
  by_cases ha : a = 0
  · subst ha
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [dirEmlLn_zero, dirEmlMul_pos_negInf hr hre, dirEmlExp_eq, Complex.zero_cpow hr0]
    simp [dirExp]
  exact dirEmlPow ha (r : ℂ)

/-- `e^x`, compiled as `exp(x · ln e)`, is exactly `exp a`. -/
theorem dirEmlExpE (a : ℂ) :
    dirEmlExp (dirEmlMul (.finite a) (dirEmlLn (dirEml (.finite 1) (.finite 1)))) =
      .finite (Complex.exp a) := by
  have he : dirEml (.finite 1) (.finite 1) = .finite (Complex.exp 1) := by
    rw [dirEml_finite one_ne_zero]; congr 1; exact cE_eq_exp_one
  have hlog : Complex.log (Complex.exp 1) = 1 := by
    rw [Complex.log_exp]
    · simp [Real.pi_pos]
    · simp [Real.pi_pos.le]
  rw [he, dirEmlLn_finite_ne_zero (Complex.exp_ne_zero _), hlog, dirEmlExp_eq,
    dirExp_of_toC (toC_dirEmlMul a 1), mul_one]

theorem dirEmlMulTwo (a : ℂ) : dirEmlMul (.finite a) dirCTwo = .finite (a * 2) := by
  rw [dirCTwo_eq_two]
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlMul_zero_left two_ne_zero, zero_mul]
  · exact dirEmlMul_eq_of_ne_zero ha two_ne_zero

theorem dirEmlDivTwo (a : ℂ) : dirEmlDiv (.finite a) dirCTwo = .finite (a / 2) := by
  rw [dirCTwo_eq_two]
  exact dirEmlDiv_eq a two_ne_zero (by norm_num)

/-- The stored `3` word, in `EmlDir`, by its certificate (`certify_sound_dir`). -/
theorem dirConst_three : dirConst Eml.Records.bits_three = .finite ((3 : ℝ) : ℂ) := by
  rw [dirConst_eq (s := .int 3) (by decide)]
  simp [Sym.denote]

theorem three_ne_exp_exp : (3 : ℝ) ≠ Real.exp (Real.exp 1) := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (Real.exp 1)
  intro h
  linarith

/-! ### The compiled words, token for token -/

/-- `x+y` (655 tokens): `1111111111111EEE1EE11EE1EEEE…EE1E1EEE1EE1E1EEE1EE1EE1EE1E`. -/
def addToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one,
    .gate, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .y, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one,
    .one, .y, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate,
    .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .x, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .one, .one, .one, .one, .one, .y, .gate, .gate, .one, .gate, .gate,
    .y, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .one, .one, .one, .one, .one, .gate, .one,
    .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate, .gate, .one, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .one, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .one, .one, .one, .one, .one, .one, .y, .gate, .gate, .one,
    .gate, .gate, .y, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .gate, .one, .one, .one, .one, .one,
    .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .gate, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .y, .gate, .gate, .one, .gate,
    .gate, .y, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .one, .one, .one, .one, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate,
    .gate, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate, .gate, .one,
    .gate, .gate, .one, .gate, .gate, .one, .gate, .one, .gate, .gate, .gate, .one,
    .gate, .gate, .one, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .gate, .one, .gate, .gate, .one, .gate]

set_option maxRecDepth 100000 in
theorem addToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml addToks [] = some [appAdd x y] := by
  rfl

/-- `x*y` (17 tokens): `1111xEE1EEyE1EE1E`. -/
def mulToks : List Tok :=
  [.one, .one, .one, .one, .x, .gate, .gate, .one, .gate, .gate, .y, .gate,
    .one, .gate, .gate, .one, .gate]

theorem mulToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml mulToks [] = some [dirEmlMul x y] := by
  rfl

/-- `x/y` (17 tokens): `111yEE1EE1xE1EE1E`. -/
def divToks : List Tok :=
  [.one, .one, .one, .y, .gate, .gate, .one, .gate, .gate, .one, .x, .gate,
    .one, .gate, .gate, .one, .gate]

theorem divToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml divToks [] = some [dirEmlDiv x y] := by
  rfl

/-- `-x` (31 tokens): `111111111E1EEEE11EEEE1EExE1EE1E`. -/
def negToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .x, .gate, .one, .gate, .gate, .one, .gate]

theorem negToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml negToks [] = some [dirEmlMul dirCNegOne x] := by
  rfl

/-- `x^2` (43 tokens): `1111111111EEE1EE11EE1EEEE1EE11xE1EEE1EE1E1E`. -/
def sqToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .x, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .one, .gate]

theorem sqToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml sqToks [] = some [dirEmlExp (dirEmlMul dirCTwo (dirEmlLn x))] := by
  rfl

/-- `2*x` (35 tokens): `1111111111EEE1EE11EE1EEEE1EExE1EE1E`. -/
def twoMulToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .x, .gate, .one, .gate, .gate, .one, .gate]

theorem twoMulToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml twoMulToks [] = some [dirEmlMul dirCTwo x] := by
  rfl

/-- `1/x` (17 tokens): `111xEE1EE11E1EE1E`. -/
def invToks : List Tok :=
  [.one, .one, .one, .x, .gate, .gate, .one, .gate, .gate, .one, .one, .gate,
    .one, .gate, .gate, .one, .gate]

theorem invToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml invToks [] = some [dirEmlDiv (.finite 1) x] := by
  rfl

/-- `sqrt(x)` (43 tokens): `111111111EEE1EE11EE1EEEE1EE111xE1EEE1EE1E1E`. -/
def sqrtToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .x, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .one, .gate]

theorem sqrtToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml sqrtToks [] = some [dirEmlSqrt x] := by
  rfl

/-- `exp(x)` (3 tokens): `x1E`. -/
def expToks : List Tok :=
  [.x, .one, .gate]

theorem expToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml expToks [] = some [dirEmlExp x] := by
  rfl

/-- `ln(x)` (7 tokens): `11xE1EE`. -/
def lnToks : List Tok :=
  [.one, .one, .x, .gate, .one, .gate, .gate]

theorem lnToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml lnToks [] = some [dirEmlLn x] := by
  rfl

/-- `x-1` (131 tokens): `111111111E1EEEE11E1E1EEEEE1E…EE111E1EE11EEE1EE1E1EEE1EE1E`. -/
def subOneToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .x, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one,
    .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate]

set_option maxRecDepth 100000 in
theorem subOneToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml subOneToks [] = some [appRot x (.finite 1)] := by
  rfl

/-- `x+1` (173 tokens): `111111111E1EEEE11E1E1EEEEE1E…E1EEEE11EE1EEE1EE1E1EEE1EE1E`. -/
def addOneToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .x, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate]

set_option maxRecDepth 100000 in
theorem addOneToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml addOneToks [] = some [appRot x dirCNegOne] := by
  rfl

/-- `x-2` (185 tokens): `111111111E1EEEE11E1E1EEEEE1E…1EE11EE1EE1EEE1EE1E1EEE1EE1E`. -/
def subTwoToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .x, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one,
    .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate]

set_option maxRecDepth 100000 in
theorem subTwoToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml subTwoToks [] = some [appRot x dirCTwo] := by
  rfl

/-- `x^y` (25 tokens): `1111yEE1EE11xE1EEE1EE1E1E`. -/
def powToks : List Tok :=
  [.one, .one, .one, .one, .y, .gate, .gate, .one, .gate, .gate, .one, .one,
    .x, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate, .one,
    .gate]

theorem powToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml powToks [] = some [dirEmlExp (dirEmlMul y (dirEmlLn x))] := by
  rfl

/-- `e^x` (27 tokens): `1111xEE1EE1111EE1EEE1EE1E1E`. -/
def expEToks : List Tok :=
  [.one, .one, .one, .one, .x, .gate, .gate, .one, .gate, .gate, .one, .one,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .one, .gate]

theorem expEToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml expEToks [] = some [dirEmlExp (dirEmlMul x (dirEmlLn (dirEml (.finite 1) (.finite 1))))] := by
  rfl

/-- `x*2` (35 tokens): `1111xEE1EE111111EEE1EE11EE1EEE1EE1E`. -/
def mulTwoToks : List Tok :=
  [.one, .one, .one, .one, .x, .gate, .gate, .one, .gate, .gate, .one, .one,
    .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one,
    .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate]

theorem mulTwoToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml mulTwoToks [] = some [dirEmlMul x dirCTwo] := by
  rfl

/-- `x/2` (35 tokens): `111111111EEE1EE11EE1EEEE1EE1xE1EE1E`. -/
def divTwoToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .x, .gate, .one, .gate, .gate, .one, .gate]

theorem divTwoToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml divTwoToks [] = some [dirEmlDiv x dirCTwo] := by
  rfl

/-- `x^3` (53 tokens): `111111111111EEE1EE11EEE1EE11EE1EEEE1EE11xE1EEE1EE1E1E`. -/
def cubeToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .gate, .one,
    .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .gate, .gate, .one, .one, .x, .gate, .one, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .gate, .one, .gate]

theorem cubeToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml cubeToks [] = some [dirEmlExp (dirEmlMul (dirConst Eml.Records.bits_three) (dirEmlLn x))] := by
  rfl

/-! ### What each compiled word computes -/

/-- **`x + y`** is exactly `a + b`. -/
theorem add_correct (a b : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite b) dirEml addToks [] = some [.finite (a + b)] := by
  rw [addToks_eval, appAdd_finite]

/-- **`x · y`** is `a · b`, up to the sign of zero. -/
theorem mul_correct (a b : ℂ) :
    valueOf (evalTok (.finite 1) (.finite a) (.finite b) dirEml mulToks []) = some (a * b) := by
  rw [mulToks_eval]
  exact toC_dirEmlMul a b

/-- **`x / y`** is `a / b` for `b ≠ 0`, up to the sign of zero. -/
theorem div_correct (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    valueOf (evalTok (.finite 1) (.finite a) (.finite b) dirEml divToks []) = some (a / b) := by
  rw [divToks_eval]
  exact toC_dirEmlDiv a hb

/-- **`−x`** is `−a`, up to the sign of zero. -/
theorem neg_correct (a y : ℂ) :
    valueOf (evalTok (.finite 1) (.finite a) (.finite y) dirEml negToks []) = some (-a) := by
  rw [negToks_eval, dirCNegOne_eq_negOne]
  show toC _ = _
  rw [toC_dirEmlMul]
  simp

/-- **`x²`** is exactly `a²`. -/
theorem sq_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml sqToks [] = some [.finite (a ^ 2)] := by
  rw [sqToks_eval, dirEmlSq]

/-- **`2·x`** is exactly `2a`. -/
theorem twoMul_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml twoMulToks [] = some [.finite (2 * a)] := by
  rw [twoMulToks_eval, dirEmlTwoMul]

/-- **`1/x`** is `1/a` for `a ≠ 0`. -/
theorem inv_correct {a : ℂ} (ha : a ≠ 0) (y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml invToks [] = some [.finite (1 / a)] := by
  rw [invToks_eval, dirEmlDiv_eq_of_ne_zero one_ne_zero ha]

/-- **`√x`** is exactly the principal `a ^ (1/2)`. -/
theorem sqrt_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml sqrtToks [] =
      some [.finite (a ^ ((1 : ℂ) / 2))] := by
  rw [sqrtToks_eval, dirEmlSqrt_all]

/-- **`exp x`** is exactly `exp a`. -/
theorem exp_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml expToks [] =
      some [.finite (Complex.exp a)] := by
  rw [expToks_eval, dirEmlExp_eq]
  rfl

/-- **`ln x`** is the principal `Complex.log a` for `a ≠ 0`. -/
theorem ln_correct {a : ℂ} (ha : a ≠ 0) (y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml lnToks [] =
      some [.finite (Complex.log a)] := by
  rw [lnToks_eval, dirEmlLn_finite_ne_zero ha]

/-- **`ln 0`** is `−∞`. -/
theorem ln_zero_correct (y : ℂ) :
    evalTok (.finite 1) (.finite 0) (.finite y) dirEml lnToks [] = some [.negInf 0] := by
  rw [lnToks_eval, dirEmlLn_zero]

/-- **`x − 1`** is exactly `a − 1`. -/
theorem subOne_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml subOneToks [] = some [.finite (a - 1)] := by
  rw [subOneToks_eval, appRot_finite]

/-- **`x + 1`** is exactly `a + 1`. -/
theorem addOne_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml addOneToks [] = some [.finite (a + 1)] := by
  rw [addOneToks_eval, dirCNegOne_eq_negOne, appRot_finite, sub_neg_eq_add]

/-- **`x − 2`** is exactly `a − 2`. -/
theorem subTwo_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml subTwoToks [] = some [.finite (a - 2)] := by
  rw [subTwoToks_eval, dirCTwo_eq_two, appRot_finite]

/-- **`x ^ y`** is exactly the principal `a ^ b` for `a ≠ 0`. -/
theorem pow_correct {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite b) dirEml powToks [] = some [.finite (a ^ b)] := by
  rw [powToks_eval, dirEmlPow ha]

/-- **`e ^ x`** is exactly `exp a`. -/
theorem expE_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml expEToks [] =
      some [.finite (Complex.exp a)] := by
  rw [expEToks_eval, dirEmlExpE]

/-- **`x · 2`** is exactly `2a`. -/
theorem mulTwo_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml mulTwoToks [] = some [.finite (a * 2)] := by
  rw [mulTwoToks_eval, dirEmlMulTwo]

/-- **`x / 2`** is exactly `a / 2`. -/
theorem divTwo_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml divTwoToks [] = some [.finite (a / 2)] := by
  rw [divTwoToks_eval, dirEmlDivTwo]

/-- **`x ^ 3`** is exactly `a³`, `0` included (the `3` word by its certificate). -/
theorem cube_correct (a y : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite y) dirEml cubeToks [] = some [.finite (a ^ 3)] := by
  rw [cubeToks_eval, dirConst_three, dirEmlPowReal (by norm_num) three_ne_exp_exp,
    show ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

/-! ### Operands up to the sign of zero

`toC` identifies `.finite 0` with `.negZero`. The circuits do not, at five slots
whose exact `EmlDir` output differs: mul's `y`, div's `x`, neg, `twoMul`, and
`divTwo`. The `valueOf` forms agree at `±0` whenever the output is finite.
`twoMul_correct_toC` and `divTwo_correct_toC` keep `≠ −0` because the exact output
is `−0`. The other `*_correct_toC` statements do not. -/

theorem toC_eq {v : EmlDir} {a : ℂ} (h : toC v = some a) :
    v = .finite a ∨ v = .negZero ∧ a = 0 := by
  cases v with
  | finite z =>
      simp only [toC, Option.some.injEq] at h
      subst h
      exact Or.inl rfl
  | negZero =>
      simp only [toC, Option.some.injEq] at h
      subst h
      exact Or.inr ⟨rfl, rfl⟩
  | posInf _ => simp [toC] at h
  | negInf _ => simp [toC] at h
  | dirInf _ => simp [toC] at h
  | nan => simp [toC] at h

theorem toC_finite {v : EmlDir} {a : ℂ} (h : toC v = some a) (hv : v ≠ .negZero) :
    v = .finite a := by
  rcases toC_eq h with hv' | ⟨hv', _⟩
  · exact hv'
  · exact absurd hv' hv

theorem toC_of_ne_zero {v : EmlDir} {a : ℂ} (h : toC v = some a) (ha : a ≠ 0) :
    v = .finite a := by
  rcases toC_eq h with hv | ⟨_, ha0⟩
  · exact hv
  · exact absurd ha0 ha

/-- `eml(1, 0) = +∞`. -/
theorem dirEml_one_zero : dirEml (.finite 1) (.finite 0) = .posInf 0 := by
  simp [dirEml, dirExp, dirLowerLog, dirSub, exp_one_im]

/-- `eml(1, −0) = +∞ + iπ`. `ln(−0)` is this phase, not the phase of `ln 0`. -/
theorem dirEml_one_negZero : dirEml (.finite 1) .negZero = .posInf Real.pi := by
  simp [dirEml, dirExp, dirLowerLog, dirSub, exp_one_im]

theorem dirEml_one_zero_ne_negZero :
    dirEml (.finite 1) (.finite 0) ≠ dirEml (.finite 1) .negZero := by
  rw [dirEml_one_zero, dirEml_one_negZero]
  intro h
  injection h with h
  exact Real.pi_ne_zero h.symm

theorem dirEmlLn_negZero : dirEmlLn .negZero = .negInf Real.pi := by
  have h1 : dirEml (.finite 1) .negZero = .posInf Real.pi := dirEml_one_negZero
  have h2 : dirEml (.posInf Real.pi) (.finite 1) = .dirInf Real.pi := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]
  have h3 : dirEml (.finite 1) (.dirInf Real.pi) = .negInf Real.pi := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, exp_one_im, Real.cos_pi]
  simp [dirEmlLn, h1, h2, h3]

/-- `ln(−0) = −∞ + iπ`, not `ln 0 = −∞`. -/
theorem dirEmlLn_negZero_ne_zero : dirEmlLn .negZero ≠ dirEmlLn (.finite 0) := by
  rw [dirEmlLn_negZero, dirEmlLn_zero]
  intro h
  injection h with h
  exact Real.pi_ne_zero h

/-- Exact form. `twoMul(−0) = −0` (`twoMul_negZero`), so this hypothesis stays.
The `valueOf` form `twoMul_correct_toC'` does not need it. -/
theorem twoMul_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (hv0 : v ≠ .negZero)
    (y : EmlDir) :
    evalTok (.finite 1) v y dirEml twoMulToks [] = some [.finite (2 * a)] := by
  rw [toC_finite hv hv0, twoMulToks_eval, dirEmlTwoMul]

theorem inv_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (ha : a ≠ 0) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml invToks [] = some [.finite (1 / a)] := by
  rw [toC_of_ne_zero hv ha, invToks_eval, dirEmlDiv_eq_of_ne_zero one_ne_zero ha]

/-- `exp` is the operator that does accept `−0`: `exp(−0) = 1 = exp 0`. -/
theorem exp_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml expToks [] = some [.finite (Complex.exp a)] := by
  rw [expToks_eval, dirEmlExp_eq, dirExp_of_toC hv]

theorem ln_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (ha : a ≠ 0) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml lnToks [] = some [.finite (Complex.log a)] := by
  rw [toC_of_ne_zero hv ha, lnToks_eval, dirEmlLn_finite_ne_zero ha]

/-- Exact form. `(−0)/2 = −0` (`divTwo_negZero`), so this hypothesis stays.
The `valueOf` form `divTwo_correct_toC'` does not need it. -/
theorem divTwo_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (hv0 : v ≠ .negZero)
    (y : EmlDir) :
    evalTok (.finite 1) v y dirEml divTwoToks [] = some [.finite (a / 2)] := by
  rw [toC_finite hv hv0, divTwoToks_eval, dirEmlDivTwo]

/-- Finite operand. `cube_correct_toC'` drops `≠ −0` by reducing `−0` to this case. -/
theorem cube_correct_finite {v : EmlDir} {a : ℂ} (hv : toC v = some a) (hv0 : v ≠ .negZero)
    (y : EmlDir) :
    evalTok (.finite 1) v y dirEml cubeToks [] = some [.finite (a ^ 3)] := by
  rw [toC_finite hv hv0, cubeToks_eval, dirConst_three, dirEmlPowReal (by norm_num) three_ne_exp_exp,
    show ((3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

/-! ### Composed words

A trigonometric word is a template with its `x` and `y` slots filled by sub-words
(`Tok.subst`). The variable and the constant `1` evaluate on their own. -/

theorem evalTok_x (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml [.x] [] = some [x] := rfl

theorem evalTok_oneTok (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml [.one] [] = some [.finite 1] := rfl

theorem evalAt {X Y T : List Tok} {vx vy x y : EmlDir}
    (hX : evalTok (.finite 1) x y dirEml X [] = some [vx])
    (hY : evalTok (.finite 1) x y dirEml Y [] = some [vy]) :
    evalTok (.finite 1) x y dirEml (Tok.subst X Y T) [] =
      evalTok (.finite 1) vx vy dirEml T [] :=
  evalTok_subst (.finite 1) x y dirEml X Y T hX hY []

/-- The K 29 word for `1/2`, through `ln 0`. -/
def halfToks : List Tok :=
  [.one, .one, .one, .gate, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .one, .gate, .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate]

noncomputable def dirCHalf : EmlDir :=
  dirEml
    (dirEml (.finite 1)
      (dirEml (dirEml (.finite 1) (.finite 1))
        (dirEml
          (dirEml
            (dirEml (.finite 1)
              (dirEml (.finite 1)
                (dirEml (.finite 1) (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)))))
            (dirEml (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1)))
          (.finite 1))))
    (.finite 1)

theorem halfToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml halfToks [] = some [dirCHalf] := by
  rfl

theorem dirCHalf_eq : dirCHalf = .finite ((1 : ℂ) / 2) := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have h0 : dirEml (.finite 1) (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) =
      .finite 0 := by
    rw [dirEml_finite one_ne_zero, dirEml_finite one_ne_zero,
      dirEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
    congr 1; exact cZero_eq_zero
  have hnegInf : dirEml (.finite 1) (dirEml (.finite 1) (.finite 0)) = .negInf 0 := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im]
  have htree : dirEml (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1) =
      .finite (Complex.exp (Complex.exp (Complex.exp 1))) := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]
  have he : dirEml (.finite 1) (.finite 1) = .finite (Complex.exp 1) := by
    rw [dirEml_finite one_ne_zero]; congr 1; exact cE_eq_exp_one
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hinner : dirEml (.negInf 0) (.finite (Complex.exp (Complex.exp (Complex.exp 1)))) =
      .finite (-Complex.exp (Complex.exp 1)) := by
    have h10 : ¬ ((1 : ℝ) < 0) := by norm_num
    simp [dirEml, dirExp, dirLowerLog, dirSub, Complex.exp_ne_zero,
      lowerLog_exp_of_im_zero hee_im, h10]
  unfold dirCHalf
  rw [h0, hnegInf, htree, hinner, he]
  have h1 : dirEml (.finite (-Complex.exp (Complex.exp 1))) (.finite 1) =
      .finite (Complex.exp (-Complex.exp (Complex.exp 1))) := by
    rw [dirEml_finite one_ne_zero]
    congr 1
    unfold eml
    rw [lowerLog_one, sub_zero]
  rw [h1]
  have hneg_ee_im : (-Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by simp [hee_im]
  have h2 : dirEml (.finite (Complex.exp 1))
      (.finite (Complex.exp (-Complex.exp (Complex.exp 1)))) =
      .finite (2 * Complex.exp (Complex.exp 1)) := by
    rw [dirEml_finite (Complex.exp_ne_zero _)]
    congr 1
    unfold eml
    rw [lowerLog_exp_of_im_zero hneg_ee_im]
    ring
  rw [h2]
  have h2ee_pos : (0 : ℝ) < 2 * Real.exp (Real.exp 1) := by positivity
  have h2ee_cast : (2 : ℂ) * Complex.exp (Complex.exp 1) =
      ((2 * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  have h2ee_ne : (2 : ℂ) * Complex.exp (Complex.exp 1) ≠ 0 := by
    rw [h2ee_cast]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt h2ee_pos)
  rw [dirEml_finite h2ee_ne, dirEml_finite one_ne_zero]
  congr 1
  unfold eml
  rw [lowerLog_one, sub_zero, h2ee_cast, lowerLog_ofReal_pos h2ee_pos,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - ((Real.log 2 + Real.exp 1 : ℝ) : ℂ) =
      ((-Real.log 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  push_cast; ring

/-- `σ(x) = 1 / (1 + exp(−x))`, the compiler's word: `div(1, add(1, exp(neg x)))`. -/
def sigmaToks : List Tok :=
  Tok.subst [.one]
    (Tok.subst [.one] (Tok.subst (Tok.subst [.x] [.one] negToks) [.one] expToks) addToks)
    divToks

theorem neg_at (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] negToks) [] =
      some [dirEmlMul dirCNegOne (.finite a)] := by
  rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), negToks_eval]

theorem toC_neg_finite (a : ℂ) :
    toC (dirEmlMul dirCNegOne (.finite a)) = some (-a) := by
  have h := neg_correct a 0
  rw [negToks_eval] at h
  exact h

/-- **`σ(x)`** is `1 / (1 + exp(−a))` when that denominator is not `0`. -/
theorem sigma_correct {a : ℂ} (hden : (1 : ℂ) + Complex.exp (-a) ≠ 0) (y : EmlDir) :
    valueOf (evalTok (.finite 1) (.finite a) y dirEml sigmaToks []) =
      some (1 / (1 + Complex.exp (-a))) := by
  have hneg := neg_at a y
  have hexp : evalTok (.finite 1) (.finite a) y dirEml
      (Tok.subst (Tok.subst [.x] [.one] negToks) [.one] expToks) [] =
      some [.finite (Complex.exp (-a))] := by
    rw [evalAt hneg (evalTok_oneTok _ _), exp_correct_toC (toC_neg_finite a)]
  have hadd : evalTok (.finite 1) (.finite a) y dirEml
      (Tok.subst [.one] (Tok.subst (Tok.subst [.x] [.one] negToks) [.one] expToks) addToks) [] =
      some [.finite (1 + Complex.exp (-a))] := by
    rw [evalAt (evalTok_oneTok _ _) hexp, addToks_eval, appAdd_finite]
  rw [sigmaToks, evalAt (evalTok_oneTok _ _) hadd, divToks_eval]
  exact toC_dirEmlDiv 1 hden

theorem sinh_formula (a : ℂ) :
    Complex.exp a * (1 - Complex.exp (-(a + a))) * ((1 : ℂ) / 2) = Complex.sinh a := by
  have hsum : -(a + a) = -a + -a := by ring
  have hmul : Complex.exp a * Complex.exp (-(a + a)) = Complex.exp (-a) := by
    rw [← Complex.exp_add, hsum]
    congr 1
    ring
  rw [Complex.sinh, mul_sub, mul_one, hmul]
  ring

/-- `exp(a) / 2 · (1 − exp(−2a))`. The factor `1/2` is the K 29 word. -/
def sinhTwoX : List Tok := Tok.subst [.x] [.x] addToks

def sinhEm2 : List Tok :=
  Tok.subst (Tok.subst sinhTwoX [.one] negToks) [.one] expToks

def sinhGap : List Tok := Tok.subst [.one] sinhEm2 appSubToks

def sinhProd : List Tok :=
  Tok.subst (Tok.subst [.x] [.one] expToks) sinhGap mulToks

def sinhToks : List Tok := Tok.subst sinhProd halfToks mulToks

/-- **`sinh`** is `Complex.sinh a` when that value is not `0`
(the zero values pass through a signed zero). -/
theorem sinh_correct {a : ℂ} (hs : Complex.sinh a ≠ 0) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml sinhToks [] = some [.finite (Complex.sinh a)] := by
  have ha : a ≠ 0 := by
    intro ha0
    apply hs
    simp [ha0, Complex.sinh_zero]
  have hsum_ne : a + a ≠ 0 := by
    rw [show a + a = (2 : ℂ) * a by ring]
    exact mul_ne_zero two_ne_zero ha
  have htwo : evalTok (.finite 1) (.finite a) y dirEml sinhTwoX [] = some [.finite (a + a)] := by
    rw [sinhTwoX, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hneg : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst sinhTwoX [.one] negToks) [] =
      some [.finite (-(a + a))] := by
    rw [evalAt htwo (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne,
      dirEmlMul_eq_of_ne_zero (by norm_num) hsum_ne, neg_one_mul]
  have hexp : evalTok (.finite 1) (.finite a) y dirEml sinhEm2 [] =
      some [.finite (Complex.exp (-(a + a)))] := by
    rw [sinhEm2, evalAt hneg (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
    rfl
  have hgap : evalTok (.finite 1) (.finite a) y dirEml sinhGap [] =
      some [.finite (1 - Complex.exp (-(a + a)))] := by
    rw [sinhGap, evalAt (evalTok_oneTok _ _) hexp, appSubToks_eval, appSub_finite]
  have hpos : Complex.exp a ≠ 0 := Complex.exp_ne_zero _
  have hdiff : 1 - Complex.exp (-(a + a)) ≠ 0 := by
    intro h0
    apply hs
    rw [← sinh_formula]
    rw [h0, mul_zero, zero_mul]
  have hprod : evalTok (.finite 1) (.finite a) y dirEml sinhProd [] =
      some [.finite (Complex.exp a * (1 - Complex.exp (-(a + a))))] := by
    have hexpa : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] expToks) [] =
        some [.finite (Complex.exp a)] := by
      rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
      rfl
    rw [sinhProd, evalAt hexpa hgap, mulToks_eval,
      dirEmlMul_eq_of_ne_zero hpos hdiff]
  have hprod_ne : Complex.exp a * (1 - Complex.exp (-(a + a))) ≠ 0 :=
    mul_ne_zero hpos hdiff
  have hhalf_ne : (1 : ℂ) / 2 ≠ 0 := by norm_num
  rw [sinhToks, evalAt hprod (halfToks_eval _ _), mulToks_eval, dirCHalf_eq,
    dirEmlMul_eq_of_ne_zero hprod_ne hhalf_ne, sinh_formula]

theorem cosh_formula (a : ℂ) :
    Complex.exp a * (1 - -Complex.exp (-(a + a))) * ((1 : ℂ) / 2) = Complex.cosh a := by
  have hmul : Complex.exp a * Complex.exp (-(a + a)) = Complex.exp (-a) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hleft : Complex.exp a * (1 - -Complex.exp (-(a + a))) =
      Complex.exp a + Complex.exp (-a) := by
    rw [mul_sub, mul_one, mul_neg, hmul, sub_neg_eq_add]
  rw [Complex.cosh, hleft]
  ring

/-- `exp(a) / 2 · (1 + exp(−2a))`. -/
def coshEm2 : List Tok := sinhEm2

def coshNeg : List Tok := Tok.subst coshEm2 [.one] negToks

def coshGap : List Tok := Tok.subst [.one] coshNeg appSubToks

def coshProd : List Tok :=
  Tok.subst (Tok.subst [.x] [.one] expToks) coshGap mulToks

def coshToks : List Tok := Tok.subst coshProd halfToks mulToks

/-- **`cosh`** is `Complex.cosh a` when that value is not `0`. -/
theorem cosh_correct {a : ℂ} (hc : Complex.cosh a ≠ 0) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml coshToks [] = some [.finite (Complex.cosh a)] := by
  -- `a = 0` makes `a + a = 0`, so the negation is `−0`. `exp` accepts it, and `cosh 0 = 1`.
  by_cases ha : a = 0
  · subst ha
    have htwo0 : evalTok (.finite 1) (.finite 0) y dirEml sinhTwoX [] = some [.finite 0] := by
      rw [sinhTwoX, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
      simp
    have hneg0 : evalTok (.finite 1) (.finite 0) y dirEml (Tok.subst sinhTwoX [.one] negToks) [] =
        some [.negZero] := by
      rw [evalAt htwo0 (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne, dirEmlMul_negOne_zero]
    have hexp0 : evalTok (.finite 1) (.finite 0) y dirEml coshEm2 [] = some [.finite 1] := by
      rw [coshEm2, sinhEm2, evalAt hneg0 (evalTok_oneTok _ _),
        exp_correct_toC (by rfl : toC .negZero = some 0)]
      simp [Complex.exp_zero]
    have hneg1 : evalTok (.finite 1) (.finite 0) y dirEml coshNeg [] = some [.finite (-1)] := by
      rw [coshNeg, evalAt hexp0 (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne,
        dirEmlMul_eq_of_ne_zero (by norm_num) one_ne_zero, neg_one_mul]
    have hgap0 : evalTok (.finite 1) (.finite 0) y dirEml coshGap [] = some [.finite (1 - -1)] := by
      rw [coshGap, evalAt (evalTok_oneTok _ _) hneg1, appSubToks_eval, appSub_finite]
    have hexpa : evalTok (.finite 1) (.finite 0) y dirEml (Tok.subst [.x] [.one] expToks) [] =
        some [.finite 1] := by
      rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
      simp [dirExp, Complex.exp_zero]
    have hprod0 : evalTok (.finite 1) (.finite 0) y dirEml coshProd [] =
        some [.finite (1 * (1 - -1))] := by
      rw [coshProd, evalAt hexpa hgap0, mulToks_eval,
        dirEmlMul_eq_of_ne_zero one_ne_zero (by norm_num : (1 - -1 : ℂ) ≠ 0)]
    rw [coshToks, evalAt hprod0 (halfToks_eval _ _), mulToks_eval, dirCHalf_eq,
      dirEmlMul_eq_of_ne_zero (by norm_num) (by norm_num), Complex.cosh_zero]
    norm_num
  have hsum_ne : a + a ≠ 0 := by
    rw [show a + a = (2 : ℂ) * a by ring]
    exact mul_ne_zero two_ne_zero ha
  have htwo : evalTok (.finite 1) (.finite a) y dirEml sinhTwoX [] = some [.finite (a + a)] := by
    rw [sinhTwoX, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hneg2 : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst sinhTwoX [.one] negToks) [] =
      some [.finite (-(a + a))] := by
    rw [evalAt htwo (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne,
      dirEmlMul_eq_of_ne_zero (by norm_num) hsum_ne, neg_one_mul]
  have hexp : evalTok (.finite 1) (.finite a) y dirEml coshEm2 [] =
      some [.finite (Complex.exp (-(a + a)))] := by
    rw [coshEm2, sinhEm2, evalAt hneg2 (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
    rfl
  have hneg : evalTok (.finite 1) (.finite a) y dirEml coshNeg [] =
      some [.finite (-Complex.exp (-(a + a)))] := by
    rw [coshNeg, evalAt hexp (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne,
      dirEmlMul_eq_of_ne_zero (by norm_num) (Complex.exp_ne_zero _), neg_one_mul]
  have hgap : evalTok (.finite 1) (.finite a) y dirEml coshGap [] =
      some [.finite (1 - -Complex.exp (-(a + a)))] := by
    rw [coshGap, evalAt (evalTok_oneTok _ _) hneg, appSubToks_eval, appSub_finite]
  have hpos : Complex.exp a ≠ 0 := Complex.exp_ne_zero _
  have hdiff : 1 - -Complex.exp (-(a + a)) ≠ 0 := by
    intro h0
    apply hc
    rw [← cosh_formula, h0, mul_zero, zero_mul]
  have hprod : evalTok (.finite 1) (.finite a) y dirEml coshProd [] =
      some [.finite (Complex.exp a * (1 - -Complex.exp (-(a + a))))] := by
    have hexpa : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] expToks) [] =
        some [.finite (Complex.exp a)] := by
      rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
      rfl
    rw [coshProd, evalAt hexpa hgap, mulToks_eval, dirEmlMul_eq_of_ne_zero hpos hdiff]
  have hprod_ne : Complex.exp a * (1 - -Complex.exp (-(a + a))) ≠ 0 :=
    mul_ne_zero hpos hdiff
  rw [coshToks, evalAt hprod (halfToks_eval _ _), mulToks_eval, dirCHalf_eq,
    dirEmlMul_eq_of_ne_zero hprod_ne (by norm_num : (1 : ℂ) / 2 ≠ 0), cosh_formula]

/-- `(√z)² = z`, principal square root. -/
theorem sq_sqrt (z : ℂ) : (z ^ ((1 : ℂ) / 2)) ^ 2 = z := by
  by_cases hz : z = 0
  · subst hz
    simp
  · rw [Complex.cpow_def_of_ne_zero hz, sq, ← Complex.exp_add]
    have hcoef : Complex.log z * (1 / 2) + Complex.log z * (1 / 2) = Complex.log z := by ring
    rw [hcoef, Complex.exp_log hz]

theorem sqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : z ^ ((1 : ℂ) / 2) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hz]
  exact Complex.exp_ne_zero _

/-- The argument of `arcosh` is never `0`. -/
theorem arcosh_arg_ne (a : ℂ) :
    a + (a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2) ≠ 0 := by
  intro h
  have hmul : (a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2) = -a := by
    apply eq_neg_of_add_eq_zero_left
    rw [add_comm]
    exact h
  have hsq : ((a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2)) ^ 2 = a ^ 2 := by
    rw [hmul]
    ring
  rw [mul_pow, sq_sqrt, sq_sqrt] at hsq
  have : (a - 1) * (a + 1) = a * a := by
    simpa [sq] using hsq
  have : a * a - 1 = a * a := by
    linear_combination this
  norm_num at this

/-- `ln(√(1 + x) / √(1 − x))`. -/
def artanhAdd : List Tok := Tok.subst [.one] [.x] addToks

def artanhSub : List Tok := Tok.subst [.one] [.x] appSubToks

def artanhNum : List Tok := Tok.subst artanhAdd [.one] sqrtToks

def artanhDen : List Tok := Tok.subst artanhSub [.one] sqrtToks

def artanhQuot : List Tok := Tok.subst artanhNum artanhDen divToks

def artanhToks : List Tok := Tok.subst artanhQuot [.one] lnToks

/-- **`artanh`** is `log(√(1+a) / √(1−a))` for `a ≠ ±1`. -/
theorem artanh_correct {a : ℂ} (hp : a ≠ 1) (hm : a ≠ -1) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml artanhToks [] =
      some [.finite (Complex.log (((1 + a) ^ ((1 : ℂ) / 2)) / ((1 - a) ^ ((1 : ℂ) / 2))))] := by
  have hadd_ne : 1 + a ≠ 0 := by
    intro h
    apply hm
    calc a = (1 + a) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by ring
  have hsub_ne : 1 - a ≠ 0 := by
    intro h
    apply hp
    calc a = 1 - (1 - a) := by ring
      _ = 1 - 0 := by rw [h]
      _ = 1 := by ring
  have hadd : evalTok (.finite 1) (.finite a) y dirEml artanhAdd [] = some [.finite (1 + a)] := by
    rw [artanhAdd, evalAt (evalTok_oneTok _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hsub : evalTok (.finite 1) (.finite a) y dirEml artanhSub [] = some [.finite (1 - a)] := by
    rw [artanhSub, evalAt (evalTok_oneTok _ _) (evalTok_x _ _), appSubToks_eval, appSub_finite]
  have hnum : evalTok (.finite 1) (.finite a) y dirEml artanhNum [] =
      some [.finite ((1 + a) ^ ((1 : ℂ) / 2))] := by
    rw [artanhNum, evalAt hadd (evalTok_oneTok _ _), sqrtToks_eval, dirEmlSqrt_all]
  have hden : evalTok (.finite 1) (.finite a) y dirEml artanhDen [] =
      some [.finite ((1 - a) ^ ((1 : ℂ) / 2))] := by
    rw [artanhDen, evalAt hsub (evalTok_oneTok _ _), sqrtToks_eval, dirEmlSqrt_all]
  have hnum_ne := sqrt_ne_zero hadd_ne
  have hden_ne := sqrt_ne_zero hsub_ne
  have hquot_val : (1 + a) ^ ((1 : ℂ) / 2) / (1 - a) ^ ((1 : ℂ) / 2) ≠ 0 :=
    div_ne_zero hnum_ne hden_ne
  have hquot : evalTok (.finite 1) (.finite a) y dirEml artanhQuot [] =
      some [dirEmlDiv (.finite ((1 + a) ^ ((1 : ℂ) / 2)))
        (.finite ((1 - a) ^ ((1 : ℂ) / 2)))] := by
    rw [artanhQuot, evalAt hnum hden, divToks_eval]
  have hto : toC (dirEmlDiv (.finite ((1 + a) ^ ((1 : ℂ) / 2)))
      (.finite ((1 - a) ^ ((1 : ℂ) / 2)))) =
      some (((1 + a) ^ ((1 : ℂ) / 2)) / ((1 - a) ^ ((1 : ℂ) / 2))) :=
    toC_dirEmlDiv _ hden_ne
  have hfin := toC_of_ne_zero hto hquot_val
  rw [artanhToks, evalAt hquot (evalTok_oneTok _ _), lnToks_eval, hfin, dirEmlLn_finite_ne_zero hquot_val]

/-- `ln(x + √(x − 1) · √(x + 1))`. -/
def arcoshRad : List Tok :=
  Tok.subst (Tok.subst (Tok.subst [.x] [.one] subOneToks) [.one] sqrtToks)
    (Tok.subst (Tok.subst [.x] [.one] addOneToks) [.one] sqrtToks) mulToks

def arcoshSum : List Tok := Tok.subst [.x] arcoshRad addToks

def arcoshToks : List Tok := Tok.subst arcoshSum [.one] lnToks

/-- `√(−2) = √2 · i`, so its real part is `0`. -/
theorem sqrt_neg_two : ((-2 : ℂ) ^ ((1 : ℂ) / 2)) = (Real.sqrt 2 : ℂ) * Complex.I := by
  have hne : (-2 : ℂ) ≠ 0 := by norm_num
  rw [Complex.cpow_def_of_ne_zero hne, show (-2 : ℂ) = (2 : ℝ) * (-1) by norm_num,
    Complex.log_ofReal_mul (by norm_num) (by norm_num), Complex.log_neg_one]
  have hsplit : ((Real.log 2 : ℂ) + Real.pi * Complex.I) * ((1 : ℂ) / 2) =
      (Real.log 2 / 2 : ℂ) + (Real.pi / 2) * Complex.I := by
    ring
  rw [hsplit, Complex.exp_add]
  have hexp : Complex.exp ((Real.log 2 : ℂ) / 2) = (Real.sqrt 2 : ℂ) := by
    rw [show (Real.log 2 : ℂ) / 2 = ((Real.log 2 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    have hx : (Real.exp (Real.log 2 / 2)) ^ 2 = 2 := by
      rw [sq, ← Real.exp_add]
      have : Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 := by ring
      rw [this, Real.exp_log (by norm_num)]
    rw [← Real.sqrt_sq (Real.exp_nonneg _), hx]
  rw [hexp, Complex.exp_pi_div_two_mul_I]

/-- **`arcosh`** is `log(a + √(a−1) · √(a+1))` for every `a`. The sum is never `0`. -/
theorem arcosh_correct (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml arcoshToks [] =
      some [.finite (Complex.log (a + (a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2)))] := by
  have hsub : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] subOneToks) [] =
      some [.finite (a - 1)] := by
    rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), subOneToks_eval, appRot_finite]
  have hadd1 : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] addOneToks) [] =
      some [.finite (a + 1)] := by
    rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), addOneToks_eval, dirCNegOne_eq_negOne,
      appRot_finite, sub_neg_eq_add]
  have hs1 : evalTok (.finite 1) (.finite a) y dirEml
      (Tok.subst (Tok.subst [.x] [.one] subOneToks) [.one] sqrtToks) [] =
      some [.finite ((a - 1) ^ ((1 : ℂ) / 2))] := by
    rw [evalAt hsub (evalTok_oneTok _ _), sqrtToks_eval, dirEmlSqrt_all]
  have hs2 : evalTok (.finite 1) (.finite a) y dirEml
      (Tok.subst (Tok.subst [.x] [.one] addOneToks) [.one] sqrtToks) [] =
      some [.finite ((a + 1) ^ ((1 : ℂ) / 2))] := by
    rw [evalAt hadd1 (evalTok_oneTok _ _), sqrtToks_eval, dirEmlSqrt_all]
  by_cases h1 : a = 1
  · subst h1
    have hleft : ((1 : ℂ) - 1) ^ ((1 : ℂ) / 2) = 0 := by simp
    have hright_ne : ((1 : ℂ) + 1) ^ ((1 : ℂ) / 2) ≠ 0 :=
      sqrt_ne_zero (by norm_num : (1 : ℂ) + 1 ≠ 0)
    have hmul : evalTok (.finite 1) (.finite 1) y dirEml arcoshRad [] = some [.finite 0] := by
      rw [arcoshRad, evalAt hs1 hs2, mulToks_eval, hleft, dirEmlMul_zero_left hright_ne]
    have hsum : evalTok (.finite 1) (.finite 1) y dirEml arcoshSum [] = some [.finite 1] := by
      rw [arcoshSum, evalAt (evalTok_x _ _) hmul, addToks_eval, appAdd_finite]
      simp
    rw [arcoshToks, evalAt hsum (evalTok_oneTok _ _), lnToks_eval,
      dirEmlLn_finite_ne_zero (by norm_num : (1 : ℂ) ≠ 0)]
    simp [Complex.log_one]
  · by_cases hm : a = -1
    · subst hm
      have hleft : ((-1 : ℂ) - 1) ^ ((1 : ℂ) / 2) = (Real.sqrt 2 : ℂ) * Complex.I := by
        rw [show ((-1 : ℂ) - 1) = -2 by norm_num]
        exact sqrt_neg_two
      have hleft_ne : (Real.sqrt 2 : ℂ) * Complex.I ≠ 0 := by
        refine mul_ne_zero ?_ Complex.I_ne_zero
        exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
      have hre : 0 ≤ ((Real.sqrt 2 : ℂ) * Complex.I).re := by simp
      have hright : ((-1 : ℂ) + 1) ^ ((1 : ℂ) / 2) = 0 := by simp
      have hmul : evalTok (.finite 1) (.finite (-1)) y dirEml arcoshRad [] = some [.finite 0] := by
        rw [arcoshRad, evalAt hs1 hs2, mulToks_eval, hleft, hright,
          dirEmlMul_eq hleft_ne hre, mul_zero]
      have hsum : evalTok (.finite 1) (.finite (-1)) y dirEml arcoshSum [] =
          some [.finite (-1)] := by
        rw [arcoshSum, evalAt (evalTok_x _ _) hmul, addToks_eval, appAdd_finite]
        simp
      rw [arcoshToks, evalAt hsum (evalTok_oneTok _ _), lnToks_eval,
        dirEmlLn_finite_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)]
      simp [Complex.log_neg_one]
    · have hleft_ne : (a - 1) ^ ((1 : ℂ) / 2) ≠ 0 := by
        apply sqrt_ne_zero
        intro h
        apply h1
        calc a = (a - 1) + 1 := by ring
          _ = 0 + 1 := by rw [h]
          _ = 1 := by ring
      have hright_ne : (a + 1) ^ ((1 : ℂ) / 2) ≠ 0 := by
        apply sqrt_ne_zero
        intro h
        apply hm
        calc a = (a + 1) - 1 := by ring
          _ = 0 - 1 := by rw [h]
          _ = -1 := by ring
      have hmul : evalTok (.finite 1) (.finite a) y dirEml arcoshRad [] =
          some [.finite ((a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2))] := by
        rw [arcoshRad, evalAt hs1 hs2, mulToks_eval, dirEmlMul_eq_of_ne_zero hleft_ne hright_ne]
      set p : ℂ := (a - 1) ^ ((1 : ℂ) / 2) * (a + 1) ^ ((1 : ℂ) / 2)
      have hsum : evalTok (.finite 1) (.finite a) y dirEml arcoshSum [] = some [.finite (a + p)] := by
        rw [arcoshSum, evalAt (evalTok_x _ _) hmul, addToks_eval, appAdd_finite]
      have harg := arcosh_arg_ne a
      rw [arcoshToks, evalAt hsum (evalTok_oneTok _ _), lnToks_eval, dirEmlLn_finite_ne_zero harg]


/-! ### `i`, `−i`, and the exponential shortcuts -/

def twoToks : List Tok := [
    .one, .one, .one, .one, .one, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .one, .gate, .gate,
    .one, .gate, .gate
  ]

def iToks : List Tok := [
    .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .one, .gate, .one, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .gate, .one,
    .gate
  ]

def negIToks : List Tok := [
    .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .gate, .gate, .one,
    .gate, .gate, .one, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one,
    .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .gate, .one, .gate, .one, .gate, .gate
  ]

def expMinusOneToks : List Tok := [
    .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .one, .one,
    .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .x, .one, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .one, .one, .gate,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .gate, .one,
    .gate, .gate, .one, .one, .gate, .gate, .gate, .one,
    .gate, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate
  ]

def expPlusOneToks : List Tok := [
    .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .one, .one,
    .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .x, .one, .one, .one,
    .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .one, .one, .one, .one, .one, .one,
    .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one,
    .one, .one, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .gate
  ]



set_option maxRecDepth 100000 in
theorem twoToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml twoToks [] = some [dirCTwo] := by rfl

noncomputable def dirCI : EmlDir := dirEmlExp (dirEmlDiv dirCIpi dirCTwo)

set_option maxRecDepth 100000 in
theorem iToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml iToks [] = some [dirCI] := by rfl

theorem dirCI_eq_I : dirCI = .finite Complex.I := by
  unfold dirCI
  rw [dirCIpi_eq, dirCTwo_eq_two]
  have hne : (Real.pi : ℂ) * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [dirEmlDiv_eq_of_ne_zero hne two_ne_zero, dirEmlExp_eq]
  simp only [dirExp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I / 2 = (Real.pi / 2) * Complex.I by ring,
    Complex.exp_pi_div_two_mul_I]

noncomputable def dirNegInfWord : EmlDir :=
  dirEml (.finite 1) (dirEml (.finite 1) (dirEml (.finite 1)
    (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1))))

theorem dirNegInfWord_eq : dirNegInfWord = .negInf 0 := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have h0 : dirEml (.finite 1) (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) =
      .finite 0 := by
    rw [dirEml_finite one_ne_zero, dirEml_finite one_ne_zero,
      dirEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
    congr 1; exact cZero_eq_zero
  have hnegInf : dirEml (.finite 1) (dirEml (.finite 1) (.finite 0)) = .negInf 0 := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im]
  unfold dirNegInfWord
  rw [h0, hnegInf]

set_option maxRecDepth 100000 in
theorem negIToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml negIToks [] =
      some [dirEml dirNegInfWord (dirEmlExp dirCI)] := by rfl

theorem dirCNegI_eq :
    dirEml dirNegInfWord (dirEmlExp dirCI) = .finite (-Complex.I) := by
  rw [dirNegInfWord_eq, dirCI_eq_I, dirEmlExp_eq]
  have h10 : ¬ ((1 : ℝ) < 0) := by norm_num
  have hlog : lowerLog (Complex.exp Complex.I) = Complex.I := by
    apply lowerLog_exp
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_gt_three]
  simp [dirEml, dirExp, dirLowerLog, dirSub, h10, hlog, Complex.exp_ne_zero]

def twoIToks : List Tok := Tok.subst twoToks iToks mulToks

theorem twoI_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml twoIToks [] = some [.finite (2 * Complex.I)] := by
  rw [twoIToks, evalAt (twoToks_eval x y) (iToks_eval x y), mulToks_eval,
    dirCTwo_eq_two, dirCI_eq_I, dirEmlMul_eq two_ne_zero (by norm_num)]

/-- `exp(H) − b` when the minuend is an exponential: the unscaled rotation with `subOfExp`. -/
noncomputable def appRotExp (H b : EmlDir) : EmlDir :=
  dirEmlDiv (shortSub (mulBody dirCIpi (shortSub H b)) (dirEmlMul dirCIpi (dirRawSub b b))) dirCIpi

theorem appRotExp_finite {H : EmlDir} {w v : ℂ} (hH : dirExp H = .finite w) :
    appRotExp H (.finite v) = .finite (w - v) := by
  have hE : dirEmlExp H = .finite w := by rw [dirEmlExp_eq, hH]
  have hshort : shortSub H (.finite v) = dirRawSub (.finite w) (.finite v) := by
    rw [shortSub_eq hH, hE]
  unfold appRotExp
  rw [hshort]
  exact appRot_finite w v

theorem appRotExp_negOne {H : EmlDir} {w : ℂ} (hH : dirExp H = .finite w) :
    appRotExp H dirCNegOne = .finite (w + 1) := by
  rw [dirCNegOne_eq_negOne, appRotExp_finite hH, sub_neg_eq_add]

set_option maxRecDepth 100000 in
theorem expMinusOne_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml expMinusOneToks [] = some [appRotExp x (.finite 1)] := by rfl

set_option maxRecDepth 100000 in
theorem expPlusOne_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml expPlusOneToks [] = some [appRotExp x dirCNegOne] := by rfl

theorem sin_exp_formula (a : ℂ) :
    Complex.sin a =
      (Complex.exp (Complex.I * a) - Complex.exp (-(Complex.I * a))) / (2 * Complex.I) := by
  rw [Complex.sin]
  have h1 : -a * Complex.I = -(Complex.I * a) := by ring
  have h2 : a * Complex.I = Complex.I * a := by ring
  rw [h1, h2]
  set d : ℂ := Complex.exp (Complex.I * a) - Complex.exp (-(Complex.I * a))
  have hneg : Complex.exp (-(Complex.I * a)) - Complex.exp (Complex.I * a) = -d := by
    simp [d, neg_sub]
  have hinv : (1 : ℂ) / (2 * Complex.I) = -Complex.I / 2 := by
    field_simp [Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  have hre : -d * Complex.I / 2 = d * (-Complex.I * ((1 : ℂ) / 2)) := by
    rw [neg_mul, ← mul_neg, div_eq_mul_one_div, mul_assoc]
  have hback : -Complex.I * ((1 : ℂ) / 2) = (1 : ℂ) / (2 * Complex.I) := by
    rw [← div_eq_mul_one_div, ← hinv]
  rw [hneg, hre, hback]
  exact (div_eq_mul_one_div _ _).symm

theorem cos_exp_formula (a : ℂ) :
    Complex.cos a =
      (Complex.exp (Complex.I * a) + Complex.exp (-(Complex.I * a))) * ((1 : ℂ) / 2) := by
  rw [Complex.cos]
  have h1 : a * Complex.I = Complex.I * a := by ring
  have h2 : -a * Complex.I = -(Complex.I * a) := by ring
  rw [h1, h2, div_eq_mul_one_div]

theorem exp_ix_sum (a : ℂ) :
    Complex.exp (Complex.I * a) + Complex.exp (-(Complex.I * a)) =
      Complex.exp (-(Complex.I * a)) * (Complex.exp (2 * Complex.I * a) + 1) := by
  have hexp : Complex.exp (Complex.I * a) =
      Complex.exp (-(Complex.I * a)) * Complex.exp (2 * Complex.I * a) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp, mul_add, mul_one]

theorem exp_two_I_ne_neg_one_of_cos_ne {a : ℂ} (h : Complex.cos a ≠ 0) :
    Complex.exp (2 * Complex.I * a) + 1 ≠ 0 := by
  intro h0
  apply h
  rw [cos_exp_formula, exp_ix_sum, h0, mul_zero, zero_mul]

theorem tan_exp_formula {a : ℂ} (h : Complex.exp (2 * Complex.I * a) + 1 ≠ 0) :
    Complex.tan a = -Complex.I * (1 - 2 / (Complex.exp (2 * Complex.I * a) + 1)) := by
  rw [Complex.tan_eq_sin_div_cos, sin_exp_formula, cos_exp_formula, exp_ix_sum]
  set u : ℂ := Complex.exp (-(Complex.I * a))
  set w : ℂ := Complex.exp (2 * Complex.I * a)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hia : Complex.exp (Complex.I * a) = u * w := by
    dsimp only [u, w]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hia]
  field_simp [hu, h, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring_nf

def rotIx : List Tok := Tok.subst iToks [.x] mulToks
def rotNeg : List Tok := Tok.subst rotIx [.one] negToks
def rotExp : List Tok := Tok.subst rotIx [.one] expToks
def rotExpNeg : List Tok := Tok.subst rotNeg [.one] expToks
def sinToks : List Tok := Tok.subst (Tok.subst rotExp rotExpNeg appSubToks) twoIToks divToks
def cosToks : List Tok := Tok.subst (Tok.subst rotExp rotExpNeg addToks) halfToks mulToks

theorem rotIx_eval (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml rotIx [] = some [.finite (Complex.I * a)] := by
  rw [rotIx, evalAt (iToks_eval _ _) (evalTok_x _ _), mulToks_eval, dirCI_eq_I,
    dirEmlMul_eq Complex.I_ne_zero (by simp : (0 : ℝ) ≤ Complex.I.re)]

theorem rotExp_eval (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml rotExp [] =
      some [.finite (Complex.exp (Complex.I * a))] := by
  rw [rotExp, evalAt (rotIx_eval a y) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
  simp [dirExp]

theorem rotNeg_eval (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml rotNeg [] =
      some [dirEmlMul dirCNegOne (.finite (Complex.I * a))] := by
  rw [rotNeg, evalAt (rotIx_eval a y) (evalTok_oneTok _ _), negToks_eval]

theorem rotExpNeg_eval (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml rotExpNeg [] =
      some [.finite (Complex.exp (-(Complex.I * a)))] := by
  rw [rotExpNeg, evalAt (rotNeg_eval a y) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
  by_cases ha : a = 0
  · rw [ha, dirCNegOne_eq_negOne, show (Complex.I * (0 : ℂ)) = 0 by ring, dirEmlMul_negOne_zero]
    simp [dirExp, Complex.exp_zero]
  · have hne : Complex.I * a ≠ 0 := mul_ne_zero Complex.I_ne_zero ha
    rw [dirCNegOne_eq_negOne, dirEmlMul_eq_of_ne_zero (by norm_num) hne]
    simp [dirExp]

theorem sin_correct (a : ℂ) (y : EmlDir) :
    valueOf (evalTok (.finite 1) (.finite a) y dirEml sinToks []) = some (Complex.sin a) := by
  have hnum : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst rotExp rotExpNeg appSubToks) [] =
      some [.finite (Complex.exp (Complex.I * a) - Complex.exp (-(Complex.I * a)))] := by
    rw [evalAt (rotExp_eval a y) (rotExpNeg_eval a y), appSubToks_eval, appSub_finite]
  have hden := twoI_eval (.finite a) y
  rw [sinToks, evalAt hnum hden, divToks_eval]
  simp only [valueOf]
  rw [toC_dirEmlDiv _ (mul_ne_zero two_ne_zero Complex.I_ne_zero), ← sin_exp_formula]

theorem cos_correct (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml cosToks [] = some [.finite (Complex.cos a)] := by
  have hsum : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst rotExp rotExpNeg addToks) [] =
      some [.finite (Complex.exp (Complex.I * a) + Complex.exp (-(Complex.I * a)))] := by
    rw [evalAt (rotExp_eval a y) (rotExpNeg_eval a y), addToks_eval, appAdd_finite]
  rw [cosToks, evalAt hsum (halfToks_eval _ _), mulToks_eval, dirCHalf_eq]
  set s : ℂ := Complex.exp (Complex.I * a) + Complex.exp (-(Complex.I * a))
  have hhalf : ((1 : ℂ) / 2) ≠ 0 := by norm_num
  by_cases h0 : s = 0
  · rw [h0, dirEmlMul_zero_left hhalf, cos_exp_formula,
      show Complex.exp (Complex.I * a) + Complex.exp (-(Complex.I * a)) = s from rfl, h0, zero_mul]
  · rw [dirEmlMul_eq_of_ne_zero h0 hhalf, cos_exp_formula]

def tanH : List Tok := Tok.subst twoToks rotIx mulToks
def tanSum : List Tok := Tok.subst tanH [.one] expPlusOneToks
def tanQuot : List Tok := Tok.subst twoToks tanSum divToks
def tanGap : List Tok := Tok.subst [.one] tanQuot appSubToks
def tanToks : List Tok := Tok.subst negIToks tanGap mulToks

theorem tan_correct {a : ℂ} (hc : Complex.cos a ≠ 0) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml tanToks [] = some [.finite (Complex.tan a)] := by
  have hpole : Complex.exp (2 * Complex.I * a) + 1 ≠ 0 := exp_two_I_ne_neg_one_of_cos_ne hc
  have hH : evalTok (.finite 1) (.finite a) y dirEml tanH [] =
      some [.finite (2 * (Complex.I * a))] := by
    rw [tanH, evalAt (twoToks_eval _ _) (rotIx_eval a y), mulToks_eval, dirCTwo_eq_two,
      dirEmlMul_eq two_ne_zero (by norm_num)]
  have hexp : dirExp (.finite (2 * (Complex.I * a))) =
      .finite (Complex.exp (2 * (Complex.I * a))) := by simp [dirExp]
  have hsum : evalTok (.finite 1) (.finite a) y dirEml tanSum [] =
      some [.finite (Complex.exp (2 * (Complex.I * a)) + 1)] := by
    rw [tanSum, evalAt hH (evalTok_oneTok _ _), expPlusOne_eval, appRotExp_negOne hexp]
  have hassoc : (2 : ℂ) * (Complex.I * a) = 2 * Complex.I * a := by ring_nf
  have hquot : evalTok (.finite 1) (.finite a) y dirEml tanQuot [] =
      some [.finite (2 / (Complex.exp (2 * Complex.I * a) + 1))] := by
    rw [tanQuot, evalAt (twoToks_eval _ _) hsum, divToks_eval, dirCTwo_eq_two, hassoc,
      dirEmlDiv_eq_of_ne_zero two_ne_zero hpole]
  have hgap : evalTok (.finite 1) (.finite a) y dirEml tanGap [] =
      some [.finite (1 - 2 / (Complex.exp (2 * Complex.I * a) + 1))] := by
    rw [tanGap, evalAt (evalTok_oneTok _ _) hquot, appSubToks_eval, appSub_finite]
  have hneg := negIToks_eval (.finite a) y
  rw [tanToks, evalAt hneg hgap, mulToks_eval, dirCNegI_eq,
    dirEmlMul_eq (by simp [Complex.I_ne_zero]) (by simp : (0 : ℝ) ≤ (-Complex.I).re),
    tan_exp_formula hpole]

theorem tanh_exp_formula {a : ℂ} (h : Complex.exp (a + a) + 1 ≠ 0) :
    (Complex.exp (a + a) - 1) / (Complex.exp (a + a) + 1) = Complex.tanh a := by
  have _hden := h
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh]
  have he : Complex.exp a ≠ 0 := Complex.exp_ne_zero _
  have hsq : Complex.exp (a + a) = Complex.exp a * Complex.exp a := by
    rw [← Complex.exp_add]
  have hneg : Complex.exp a * Complex.exp (-a) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hnum : Complex.exp (a + a) - 1 = Complex.exp a * (Complex.exp a - Complex.exp (-a)) := by
    rw [hsq, mul_sub, hneg]
  have hden : Complex.exp (a + a) + 1 = Complex.exp a * (Complex.exp a + Complex.exp (-a)) := by
    rw [hsq, mul_add, hneg]
  rw [hnum, hden, mul_div_mul_left _ _ he, div_div_eq_mul_div,
    div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)]

def tanhTwo : List Tok := Tok.subst [.x] [.x] addToks
def tanhNum : List Tok := Tok.subst tanhTwo [.one] expMinusOneToks
def tanhDen : List Tok := Tok.subst tanhTwo [.one] expPlusOneToks
def tanhToks : List Tok := Tok.subst tanhNum tanhDen divToks

theorem tanh_correct {a : ℂ} (h : Complex.exp (a + a) + 1 ≠ 0) (y : EmlDir) :
    valueOf (evalTok (.finite 1) (.finite a) y dirEml tanhToks []) = some (Complex.tanh a) := by
  have htwo : evalTok (.finite 1) (.finite a) y dirEml tanhTwo [] = some [.finite (a + a)] := by
    rw [tanhTwo, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hexp : dirExp (.finite (a + a)) = .finite (Complex.exp (a + a)) := by simp [dirExp]
  have hnum : evalTok (.finite 1) (.finite a) y dirEml tanhNum [] =
      some [.finite (Complex.exp (a + a) - 1)] := by
    rw [tanhNum, evalAt htwo (evalTok_oneTok _ _), expMinusOne_eval, appRotExp_finite hexp]
  have hden : evalTok (.finite 1) (.finite a) y dirEml tanhDen [] =
      some [.finite (Complex.exp (a + a) + 1)] := by
    rw [tanhDen, evalAt htwo (evalTok_oneTok _ _), expPlusOne_eval, appRotExp_negOne hexp]
  rw [tanhToks, evalAt hnum hden, divToks_eval]
  simp only [valueOf]
  rw [toC_dirEmlDiv _ h, tanh_exp_formula h]

def arctanInner : List Tok := Tok.subst rotIx [.one] artanhToks
def arctanToks : List Tok := Tok.subst negIToks arctanInner mulToks

set_option maxRecDepth 1000000 in
theorem arctan_correct {a : ℂ} (hp : a ≠ Complex.I) (hm : a ≠ -Complex.I) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml arctanToks [] =
      some [.finite (-Complex.I * Complex.log
        (((1 + Complex.I * a) ^ ((1 : ℂ) / 2)) / ((1 - Complex.I * a) ^ ((1 : ℂ) / 2))))] := by
  have hnotI : Complex.I * a ≠ -1 := by
    intro h
    apply hp
    calc a = -Complex.I * (Complex.I * a) := by rw [← mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, one_mul]
      _ = -Complex.I * -1 := by rw [h]
      _ = Complex.I := by rw [mul_neg, mul_one, neg_neg]
  have hnotNeg : Complex.I * a ≠ 1 := by
    intro h
    apply hm
    calc a = -Complex.I * (Complex.I * a) := by rw [← mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, one_mul]
      _ = -Complex.I * 1 := by rw [h]
      _ = -Complex.I := by rw [mul_one]
  have hart : evalTok (.finite 1) (.finite a) y dirEml arctanInner [] =
      some [.finite (Complex.log (((1 + Complex.I * a) ^ ((1 : ℂ) / 2)) /
        ((1 - Complex.I * a) ^ ((1 : ℂ) / 2))))] := by
    rw [arctanInner, evalAt (rotIx_eval a y) (evalTok_oneTok _ _)]
    exact artanh_correct hnotNeg hnotI y
  rw [arctanToks, evalAt (negIToks_eval _ _) hart, mulToks_eval, dirCNegI_eq,
    dirEmlMul_eq (by simp [Complex.I_ne_zero]) (by simp : (0 : ℝ) ≤ (-Complex.I).re)]

end Eml.AppOps
