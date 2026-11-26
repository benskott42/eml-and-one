/-
  Machine-checked Lean 4 + Mathlib proofs of transcendental, circular,
  hyperbolic, and logistic functions built genuinely as `eml` words:

  Part 1 (Pure `ℂ`, no `ln 0`):
    - `emlPow_eq`:     `x ^ y`
    - `emlSqrt_eq`:    `x ^ (1/2)`
    - `emlLogBase_eq`: `log x / log b`

  Part 2 (Extended `EmlExt`, built purely from `extEml`, `1`, `extCTwo` (K 19),
          and `extCI` (K 57), covering ALL `x : ℂ` with zero strip restrictions):
    - `extEmlNeg_eq`:   `-x`
    - `extEmlAddRot_eq`: `a + b` (unconditional on `ℂ` via rotated subtraction!)
    - `extEmlCosh_eq`:  `Complex.cosh x`
    - `extEmlSinh_eq`:  `Complex.sinh x`
    - `extEmlTanh_eq`:  `Complex.tanh x` (for `cosh x ≠ 0`)
    - `extEmlSigma_eq`: `(1 + Complex.exp (-x))⁻¹` (for `1 + exp(-x) ≠ 0`)
    - `extEmlCos_eq`:   `Complex.cos x`
    - `extEmlSin_eq`:   `Complex.sin x`
    - `extEmlTan_eq`:   `Complex.tan x` (for `cos x ≠ 0`)
    - `extEmlPow_eq`:   `x ^ y` (for all `x ≠ 0`, `y ≠ 0`, lifting the `y ≠ e^e` and `log x ≠ 0` restrictions)
    - `extEmlLogBase_eq`: `log x / log b` (for all `x ≠ 0`, `b ≠ 0`, `log b ≠ 0`)

  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Eml.Basic
import Eml.Arithmetic
import Eml.Records
import Eml.Extended

namespace Eml.Transcendental

open Eml
open Eml.Arithmetic
open Eml.Records
open Eml.Extended

/-! ### Part 1: Pure `ℂ` (`ln 0`-free) transcendental `eml` words -/

/-- Complex power `x ^ y` built from `eml` and `1`:
    `emlExp (emlMul y (emlLn x))`. -/
noncomputable def emlPow (x y : ℂ) : ℂ :=
  emlExp (emlMul y (emlLn x))

/-- `emlPow x y = x ^ y` (principal branch `Complex.cpow`) for `x ≠ 0`, `x ≠ 1`
    (so `log x ≠ 0`), `y ≠ 0`, and `y ≠ exp(exp 1)`. -/
theorem emlPow_eq {x y : ℂ} (hx : x ≠ 0) (hlogx : Complex.log x ≠ 0)
    (hy : y ≠ 0) (hye : y ≠ Complex.exp (Complex.exp 1)) :
    emlPow x y = x ^ y := by
  unfold emlPow
  rw [emlLn_eq_log, emlExp_eq, emlMul_eq hy hlogx hye, Complex.cpow_def_of_ne_zero hx, mul_comm]

/-- Principal square root `x ^ (1/2)` built from `eml` and `1` using the K = 19
    word `cTwo` for `2`: `emlExp (emlDiv (emlLn x) cTwo)`. -/
noncomputable def emlSqrt (x : ℂ) : ℂ :=
  emlExp (emlDiv (emlLn x) cTwo)

private theorem two_ne_exp_exp_one : (2 : ℂ) ≠ Complex.exp (Complex.exp 1) := by
  intro h
  have hre : (2 : ℝ) = Real.exp (Real.exp 1) := by
    have := congrArg Complex.re h
    simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
  have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : Real.exp 1 < Real.exp (Real.exp 1) := by
    have := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1))
    linarith
  linarith

/-- `emlSqrt x = x ^ ((1 : ℂ) / 2)` for `x ≠ 0` and `Complex.log x ≠ 0` (`x ≠ 1`). -/
theorem emlSqrt_eq {x : ℂ} (hx : x ≠ 0) (hlogx : Complex.log x ≠ 0) :
    emlSqrt x = x ^ ((1 : ℂ) / 2) := by
  unfold emlSqrt
  rw [emlLn_eq_log, cTwo_eq_two, emlExp_eq,
    emlDiv_eq hlogx two_ne_zero two_ne_exp_exp_one,
    Complex.cpow_def_of_ne_zero hx]
  congr 1
  ring

/-- Base-`b` logarithm built from `eml` and `1`:
    `emlDiv (emlLn x) (emlLn b)`. -/
noncomputable def emlLogBase (b x : ℂ) : ℂ :=
  emlDiv (emlLn x) (emlLn b)

/-- `emlLogBase b x = Complex.log x / Complex.log b` whenever `log x ≠ 0`,
    `log b ≠ 0`, and `log b ≠ exp(exp 1)`. -/
theorem emlLogBase_eq {b x : ℂ} (hlogx : Complex.log x ≠ 0) (hlogb : Complex.log b ≠ 0)
    (hlogbe : Complex.log b ≠ Complex.exp (Complex.exp 1)) :
    emlLogBase b x = Complex.log x / Complex.log b := by
  unfold emlLogBase
  rw [emlLn_eq_log, emlLn_eq_log, emlDiv_eq hlogx hlogb hlogbe]

/-! ### Part 2: Extended (`EmlExt`) circular, hyperbolic, logistic, and power `eml` words -/

/-- `0` as the K = 7 `eml` word on `EmlExt`. -/
noncomputable def extCZero : EmlExt :=
  extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1))

theorem extCZero_eq_zero : extCZero = .finite 0 := by
  unfold extCZero
  rw [extEml_finite one_ne_zero, extEml_finite one_ne_zero,
    extEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
  congr 1
  exact cZero_eq_zero

/-- Unconditional negation `-x = extRotSub extCI extCZero x` on `EmlExt`. -/
noncomputable def extEmlNeg (x : EmlExt) : EmlExt :=
  extRotSub extCI extCZero x

theorem extEmlNeg_eq (x : ℂ) : extEmlNeg (.finite x) = .finite (-x) := by
  unfold extEmlNeg
  rw [extCI_eq_I, extCZero_eq_zero, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero]
  simp

/-- Unconditional addition `a + b = extRotSub extCI a (extEmlNeg b)` on `EmlExt`
    (no strip restriction on `a + b`!). -/
noncomputable def extEmlAddRot (a b : EmlExt) : EmlExt :=
  extRotSub extCI a (extEmlNeg b)

theorem extEmlAddRot_eq (a b : ℂ) :
    extEmlAddRot (.finite a) (.finite b) = .finite (a + b) := by
  unfold extEmlAddRot
  rw [extEmlNeg_eq, extCI_eq_I, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero]
  simp

/-- `cosh x = (exp(x) + exp(-x)) / 2` built purely from `extEml` and `1`. -/
noncomputable def extEmlCosh (x : EmlExt) : EmlExt :=
  extEmlDiv (extEmlAddRot (extEmlExp x) (extEmlExp (extEmlNeg x))) extCTwo

theorem extEmlCosh_eq (x : ℂ) : extEmlCosh (.finite x) = .finite (Complex.cosh x) := by
  unfold extEmlCosh
  rw [extEmlNeg_eq, extEmlExp_eq, extEmlExp_eq]
  simp only [extExp]
  rw [extEmlAddRot_eq, extCTwo_eq_two, extEmlDiv_eq _ two_ne_zero, Complex.cosh]

/-- `sinh x = (exp(x) - exp(-x)) / 2` built purely from `extEml` and `1`. -/
noncomputable def extEmlSinh (x : EmlExt) : EmlExt :=
  extEmlDiv (extRotSub extCI (extEmlExp x) (extEmlExp (extEmlNeg x))) extCTwo

theorem extEmlSinh_eq (x : ℂ) : extEmlSinh (.finite x) = .finite (Complex.sinh x) := by
  unfold extEmlSinh
  rw [extEmlNeg_eq, extEmlExp_eq, extEmlExp_eq]
  simp only [extExp]
  rw [extCI_eq_I, extRotSub_eq_sub Complex.I_re Complex.I_ne_zero,
    extCTwo_eq_two, extEmlDiv_eq _ two_ne_zero, Complex.sinh]

/-- `tanh x = sinh x / cosh x` built purely from `extEml` and `1`. -/
noncomputable def extEmlTanh (x : EmlExt) : EmlExt :=
  extEmlDiv (extEmlSinh x) (extEmlCosh x)

theorem extEmlTanh_eq {x : ℂ} (h : Complex.cosh x ≠ 0) :
    extEmlTanh (.finite x) = .finite (Complex.tanh x) := by
  unfold extEmlTanh
  rw [extEmlSinh_eq, extEmlCosh_eq, extEmlDiv_eq _ h, Complex.tanh_eq_sinh_div_cosh]

/-- Logistic sigmoid `σ(x) = 1 / (1 + exp(-x))` built purely from `extEml` and `1`. -/
noncomputable def extEmlSigma (x : EmlExt) : EmlExt :=
  extEmlDiv (.finite 1) (extEmlAddRot (.finite 1) (extEmlExp (extEmlNeg x)))

theorem extEmlSigma_eq {x : ℂ} (h : 1 + Complex.exp (-x) ≠ 0) :
    extEmlSigma (.finite x) = .finite ((1 + Complex.exp (-x))⁻¹) := by
  unfold extEmlSigma
  rw [extEmlNeg_eq, extEmlExp_eq]
  simp only [extExp]
  rw [extEmlAddRot_eq, extEmlDiv_eq _ h, one_div]

/-- `cos x = (exp(x * i) + exp(-(x * i))) / 2` built purely from `extEml` and `1`
    using the K = 57 word `extCI` for `i` and K = 19 word `extCTwo` for `2`. -/
noncomputable def extEmlCos (x : EmlExt) : EmlExt :=
  let ix := extEmlMul extCI x
  extEmlDiv (extEmlAddRot (extEmlExp ix) (extEmlExp (extEmlNeg ix))) extCTwo

theorem extEmlCos_eq (x : ℂ) : extEmlCos (.finite x) = .finite (Complex.cos x) := by
  unfold extEmlCos
  dsimp only
  rw [extCI_eq_I, extEmlMul_eq Complex.I_ne_zero, extEmlNeg_eq, extEmlExp_eq, extEmlExp_eq]
  simp only [extExp]
  rw [extEmlAddRot_eq, extCTwo_eq_two, extEmlDiv_eq _ two_ne_zero]
  congr 1
  rw [Complex.cos]
  ring_nf

/-- `sin x = (exp(-(x * i)) - exp(x * i)) * i / 2` (equivalently `(exp(i*x) - exp(-i*x)) / (2*i)`)
    built purely from `extEml` and `1`. -/
noncomputable def extEmlSin (x : EmlExt) : EmlExt :=
  let ix := extEmlMul extCI x
  extEmlDiv (extRotSub extCI (extEmlExp ix) (extEmlExp (extEmlNeg ix))) (extEmlMul extCTwo extCI)

theorem extEmlSin_eq (x : ℂ) : extEmlSin (.finite x) = .finite (Complex.sin x) := by
  unfold extEmlSin
  dsimp only
  rw [extCI_eq_I, extEmlMul_eq Complex.I_ne_zero, extEmlNeg_eq, extEmlExp_eq, extEmlExp_eq]
  simp only [extExp]
  rw [extRotSub_eq_sub Complex.I_re Complex.I_ne_zero, extCTwo_eq_two,
    extEmlMul_eq two_ne_zero]
  have h2i : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [extEmlDiv_eq _ h2i]
  congr 1
  rw [Complex.sin, mul_comm Complex.I x]
  field_simp [Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- `tan x = sin x / cos x` built purely from `extEml` and `1`. -/
noncomputable def extEmlTan (x : EmlExt) : EmlExt :=
  extEmlDiv (extEmlSin x) (extEmlCos x)

theorem extEmlTan_eq {x : ℂ} (h : Complex.cos x ≠ 0) :
    extEmlTan (.finite x) = .finite (Complex.tan x) := by
  unfold extEmlTan
  rw [extEmlSin_eq, extEmlCos_eq, extEmlDiv_eq _ h, Complex.tan_eq_sin_div_cos]

/-- Extended complex power `x ^ y` on `EmlExt` (works for ALL `x ≠ 0` and ALL `y ≠ 0`,
    including `x = 1` and `y = e^e`). -/
noncomputable def extEmlPow (x y : EmlExt) : EmlExt :=
  extEmlExp (extEmlMul y (extEmlLn x))

theorem extEmlPow_eq {x : ℂ} (hx : x ≠ 0) {y : ℂ} (hy : y ≠ 0) :
    extEmlPow (.finite x) (.finite y) = .finite (x ^ y) := by
  unfold extEmlPow
  rw [extEmlLn_finite_ne_zero hx, extEmlMul_eq hy, extEmlExp_eq]
  simp only [extExp]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hx, mul_comm]

/-- Extended base-`b` logarithm on `EmlExt` (works for ALL `x ≠ 0`, `b ≠ 0`, `log b ≠ 0`,
    including `x = 1` and `log b = e^e`). -/
noncomputable def extEmlLogBase (b x : EmlExt) : EmlExt :=
  extEmlDiv (extEmlLn x) (extEmlLn b)

theorem extEmlLogBase_eq {b x : ℂ} (hb : b ≠ 0) (hx : x ≠ 0) (hlogb : Complex.log b ≠ 0) :
    extEmlLogBase (.finite b) (.finite x) = .finite (Complex.log x / Complex.log b) := by
  unfold extEmlLogBase
  rw [extEmlLn_finite_ne_zero hx, extEmlLn_finite_ne_zero hb, extEmlDiv_eq _ hlogb]

end Eml.Transcendental
