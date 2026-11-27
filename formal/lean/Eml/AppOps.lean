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

  Each token list below is the compiler's word for that operator (`APP_WORDS` in
  `lib/eml/export.ts`; check 115 and the Lean bridge compare them), and unfolds by `rfl`
  to the Lean circuit. Values, in `EmlDir`:

  * `x + y`, `2·x`, `x²`, `√x`, `exp x`: exactly the value, for all inputs.
  * `x · y` and `−x`: the value up to the sign of zero (`(−1)·0 = −0`, as in IEEE).
  * `x / y` and `1/x` for a nonzero divisor, up to the sign of a zero quotient.
  * `ln x`: the principal `Complex.log x` for `x ≠ 0`, and `−∞` at `0`.

  `valueOf` reads a one-value stack as a complex number, with `−0` as `0`.

  Zero `sorry`, zero custom axioms.
-/
import Eml.AppSub

namespace Eml.AppOps

open Eml Eml.DirectedInf Eml.AppSub

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

end Eml.AppOps
