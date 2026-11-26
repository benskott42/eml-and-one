/-
  Machine-checked Lean 4 + Mathlib formalization of rotated subtraction
  (`docs/rotsub.md`) over `ℂ`:

    rotSub c a b = emlDiv (rawSub (emlMul c (rawSub a b)) (emlMul c (rawSub b b))) c

  Key mechanism (Corless–Jeffrey unwinding number + imaginary rotation):
  - `rawSub a b = a - b + 2πi · κ_L(b)`
  - `rawSub b b = 2πi · κ_L(b)`
  - Multiplying `rawSub b b` by a nonzero purely imaginary `c` (`c.re = 0`)
    rotates `2πi · κ_L(b)` onto the real axis (`Im(c · 2πi · κ_L(b)) = 0`),
    which lies strictly inside the lower strip `[-π, π)`.
  - Therefore the outer `rawSub` has zero unwinding and cancels `c · 2πi · κ_L(b)`
    identically, leaving `c · (a - b)`, and dividing by `c` recovers `a - b`.

  This file proves the pure-`ℂ` (no `ln 0`) theorem with explicit nonzero
  hypotheses. The extended-domain theorem handling `κ_L(b) = 0`, `a = 0`, `a = b`,
  etc. via `ln 0 = -∞` is proved in `Eml.Extended`.

  Zero `sorry`, zero custom axioms.
-/
import Eml.Basic
import Eml.Arithmetic

namespace Eml.RotSub

open Eml
open Eml.Arithmetic

/-- Rotated subtraction constructed genuinely as an `eml` word (`docs/rotsub.md`):
    `rotSub c a b = emlDiv (rawSub (emlMul c (rawSub a b)) (emlMul c (rawSub b b))) c`. -/
noncomputable def rotSub (c a b : ℂ) : ℂ :=
  emlDiv (rawSub (emlMul c (rawSub a b)) (emlMul c (rawSub b b))) c

/-- `rawSub b b` equals the pure unwinding jump `2πi · κ_L(b)` for any `b ≠ 0`. -/
theorem rawSub_self_eq_unwind {b : ℂ} (hb : b ≠ 0) :
    rawSub b b = 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ) := by
  rw [rawSub_eq_sub_add_unwind hb b, sub_self, zero_add]

/-- The rotation lemma: multiplying a purely imaginary unwinding term `2πi · k`
    by any purely imaginary `c` (`c.re = 0`) produces a real number (`Im = 0`),
    which therefore lies in the lower strip `[-π, π)`. -/
theorem mul_unwind_im_zero {c : ℂ} (hc_re : c.re = 0) (k : ℤ) :
    (c * (2 * Real.pi * Complex.I * (k : ℂ))).im = 0 := by
  simp [hc_re]

/-- Any purely imaginary number `c` (`c.re = 0`) is distinct from `exp(exp 1)`. -/
theorem ne_exp_exp_one_of_re_zero {c : ℂ} (hc_re : c.re = 0) :
    c ≠ Complex.exp (Complex.exp 1) := by
  intro h
  have hre : (Complex.exp (Complex.exp (1 : ℂ))).re = Real.exp (Real.exp 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_re]
  have h0 : (0 : ℝ) = Real.exp (Real.exp 1) := by
    rw [← hc_re, h, hre]
  linarith [Real.exp_pos (Real.exp 1)]

/-- Pure-`ℂ` (no `ln 0`) rotated subtraction theorem:
    for any nonzero purely imaginary `c` and any `a, b : ℂ` whose intermediate
    arguments avoid `0`, `rotSub c a b = a - b` regardless of how large `|Im b|` is.
    (The degenerate cases `lowerUnwind b = 0`, `a = 0`, `a = b`, or `rawSub a b = 0`
    pass through `ln 0` and are proved in `Eml.Extended.extRotSub_eq_sub`.) -/
theorem rotSub_eq_sub {c a b : ℂ}
    (hc_re : c.re = 0) (hc_ne : c ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b)
    (hk : lowerUnwind b ≠ 0)
    (hr1 : a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ) ≠ 0) :
    rotSub c a b = a - b := by
  have hce : c ≠ Complex.exp (Complex.exp 1) := ne_exp_exp_one_of_re_zero hc_re
  have hr1_eq : rawSub a b = a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ) :=
    rawSub_eq_sub_add_unwind ha b
  have hr2_eq : rawSub b b = 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ) :=
    rawSub_self_eq_unwind hb
  have hr2_ne : rawSub b b ≠ 0 := by
    rw [hr2_eq]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    · exact Int.cast_ne_zero.mpr hk
  have hr1_ne : rawSub a b ≠ 0 := by rwa [hr1_eq]
  have hm1 : emlMul c (rawSub a b) = c * rawSub a b := emlMul_eq hc_ne hr1_ne hce
  have hm2 : emlMul c (rawSub b b) = c * rawSub b b := emlMul_eq hc_ne hr2_ne hce
  have hm1_ne : c * rawSub a b ≠ 0 := mul_ne_zero hc_ne hr1_ne
  have hm2_im : (c * rawSub b b).im = 0 := by
    rw [hr2_eq]
    exact mul_unwind_im_zero hc_re (lowerUnwind b)
  have hraw : rawSub (c * rawSub a b) (c * rawSub b b) = c * (a - b) := by
    rw [rawSub_eq hm1_ne]
    · rw [hr1_eq, hr2_eq]; ring
    · rw [hm2_im]; linarith [Real.pi_pos]
    · rw [hm2_im]; exact Real.pi_pos
  have hcab_ne : c * (a - b) ≠ 0 := mul_ne_zero hc_ne (sub_ne_zero.mpr hab)
  unfold rotSub
  rw [hm1, hm2, hraw, emlDiv_eq hcab_ne hc_ne hce, mul_div_cancel_left₀ _ hc_ne]

end Eml.RotSub
