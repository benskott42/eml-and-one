/-
  Machine-checked Lean 4 + Mathlib proofs of transcendental operations
  (`x ^ y`, `x ^ (1/2)`, `log_b x`) built genuinely as `eml` words over `ℂ`
  (zero `ln 0`, zero `sorry`, zero custom axioms).

  Note: Earlier circular/hyperbolic theorems (`cos`, `sin`, `cosh`, `sinh`)
  from the axiomatic version were dropped because they were not expressed
  as `eml` words (and in `best-known.json`, `i` uses `ln 0`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Eml.Basic
import Eml.Arithmetic
import Eml.Records

namespace Eml.Transcendental

open Eml
open Eml.Arithmetic
open Eml.Records

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

end Eml.Transcendental
