/-
  Machine-checked Lean 4 + Mathlib proofs of elementary arithmetic (`*`, `/`, `1/x`, `+`, `x²`)
  constructed genuinely as `eml` words over `ℂ` (`docs/rotsub.md`, `lib/eml/best-known.json`).

  Every operation is built solely from `eml` and `1` (no `ln 0`).
  Zero `sorry`, zero custom axioms.
-/
import Eml.Basic

namespace Eml.Arithmetic

open Eml

/-- Multiplication word `1111xEE1EEyE1EE1E` (K = 17, `docs/rotsub.md`):
    `emlExp (eml 1 (emlExp (eml (emlLn (eml 1 a)) b)))`. -/
noncomputable def emlMul (a b : ℂ) : ℂ :=
  emlExp (eml 1 (emlExp (eml (emlLn (eml 1 a)) b)))

/-- `emlMul a b = a * b` for all `a ≠ 0`, `b ≠ 0`, `a ≠ exp(exp 1)` (the `a = e^e`
    and `b = 0` cases pass through `ln 0` and are handled in `Eml.Extended`).
    No strip condition on `a` or `b` is needed. -/
theorem emlMul_eq {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hae : a ≠ Complex.exp (Complex.exp 1)) :
    emlMul a b = a * b := by
  have h1a : eml 1 a ≠ 0 := by
    intro h
    unfold eml at h
    have heq : Complex.exp 1 = lowerLog a := sub_eq_zero.mp h
    apply hae
    rw [← exp_lowerLog ha, ← heq]
  unfold emlMul
  rw [emlExp_eq, emlExp_eq, emlLn_eq_log]
  unfold eml at h1a ⊢
  rw [Complex.exp_log h1a, lowerLog_exp_eq_sub_unwind]
  set u : ℂ := Complex.exp 1 - lowerLog a - lowerLog b
  have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
      (lowerLog a + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [u]; ring
  rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
    exp_lowerLog ha, exp_lowerLog hb]

/-- Division word `111yEE1EE1xE1EE1E` (K = 17, `docs/rotsub.md`):
    `emlExp (eml (emlLn (eml 1 b)) (emlExp (eml 1 a)))`. -/
noncomputable def emlDiv (a b : ℂ) : ℂ :=
  emlExp (eml (emlLn (eml 1 b)) (emlExp (eml 1 a)))

/-- `emlDiv a b = a / b` for all `a ≠ 0`, `b ≠ 0`, `b ≠ exp(exp 1)`.
    No strip condition on `a` or `b` is needed. -/
theorem emlDiv_eq {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hbe : b ≠ Complex.exp (Complex.exp 1)) :
    emlDiv a b = a / b := by
  have h1b : eml 1 b ≠ 0 := by
    intro h
    unfold eml at h
    have heq : Complex.exp 1 = lowerLog b := sub_eq_zero.mp h
    apply hbe
    rw [← exp_lowerLog hb, ← heq]
  unfold emlDiv
  rw [emlExp_eq, emlExp_eq, emlLn_eq_log]
  unfold eml at h1b ⊢
  rw [Complex.exp_log h1b, lowerLog_exp_eq_sub_unwind]
  set u : ℂ := Complex.exp 1 - lowerLog a
  have hrew : Complex.exp 1 - lowerLog b - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
      (lowerLog a - lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [u]; ring
  rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub,
    exp_lowerLog ha, exp_lowerLog hb]

/-- Reciprocal `1 / x` without `ln 0`: `emlDiv 1 x`. -/
noncomputable def emlInv (x : ℂ) : ℂ :=
  emlDiv 1 x

theorem emlInv_eq {x : ℂ} (hx : x ≠ 0) (hxe : x ≠ Complex.exp (Complex.exp 1)) :
    emlInv x = x⁻¹ := by
  rw [emlInv, emlDiv_eq one_ne_zero hx hxe, one_div]

/-- Squaring word `1111xEE1EExE1EE1E` (K = 17, `lib/eml/best-known.json`): `emlMul x x`. -/
noncomputable def emlSqr (x : ℂ) : ℂ :=
  emlMul x x

theorem emlSqr_eq {x : ℂ} (hx : x ≠ 0) (hxe : x ≠ Complex.exp (Complex.exp 1)) :
    emlSqr x = x ^ 2 := by
  rw [emlSqr, emlMul_eq hx hx hxe, sq]

/-- Addition word `1111y1EEE1EEx1EE1EE` (K = 19, `lib/eml/best-known.json`):
    `eml 1 (emlExp (eml (emlLn (eml 1 (emlExp b))) (emlExp a)))`. -/
noncomputable def emlAdd (a b : ℂ) : ℂ :=
  eml 1 (emlExp (eml (emlLn (eml 1 (emlExp b))) (emlExp a)))

/-- `emlAdd a b = a + b` whenever `Im(a + b) ∈ (-π, π]` (matching `best-known.json`)
    and `eml 1 (emlExp b) ≠ 0` (i.e. `lowerLog (exp b) ≠ e`). -/
theorem emlAdd_eq {a b : ℂ} (hb : eml 1 (emlExp b) ≠ 0)
    (h1 : -Real.pi < (a + b).im) (h2 : (a + b).im ≤ Real.pi) :
    emlAdd a b = a + b := by
  unfold emlAdd
  rw [emlLn_eq_log, emlExp_eq, emlExp_eq, emlExp_eq]
  unfold eml
  have hb' : Complex.exp 1 - lowerLog (Complex.exp b) ≠ 0 := by
    simpa [eml, emlExp, lowerLog_one] using hb
  rw [Complex.exp_log hb']
  rw [lowerLog_exp_eq_sub_unwind b, lowerLog_exp_eq_sub_unwind a]
  set k : ℤ := lowerUnwind b + lowerUnwind a
  have hexp : Complex.exp (Complex.exp 1 - (b - 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) -
        (a - 2 * Real.pi * Complex.I * (lowerUnwind a : ℂ))) =
      Complex.exp (Complex.exp 1 - (a + b)) := by
    have hrew : Complex.exp 1 - (b - 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) -
          (a - 2 * Real.pi * Complex.I * (lowerUnwind a : ℂ)) =
        (Complex.exp 1 - (a + b)) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [k, Int.cast_add]; ring
    rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp, lowerLog_exp]
  · ring
  · have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
    simp only [Complex.add_im] at h2
    simp [he1_im]; linarith
  · have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
    simp only [Complex.add_im] at h1
    simp [he1_im]; linarith

end Eml.Arithmetic
