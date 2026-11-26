/-
  Machine-checked unconditional proof of the minimality of `0` at K = 7
  (`111E1EE`, `0x74`): NO valid binary EML program of length `K ≤ 5` evaluates
  to `0`, over either `ℂ` (`eml`) or `EmlExt` (`extEml`).

  Zero external tools, zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Eml.Basic
import Eml.Binary
import Eml.TreeBijection
import Eml.Extended

namespace Eml.MinimalityZero

open Eml
open Eml.Binary
open Eml.TreeBijection
open Eml.Extended

/-- Every `EmlTree` with `t.gates ≤ 2` is one of the 4 Catalan trees of K ≤ 5:
    `1` (K=1), `e` (K=3), `e^e` (K=5), or `e - 1` (K=5). -/
theorem tree_gates_le_two_cases (t : EmlTree) (h : t.gates ≤ 2) :
    t = .one ∨
    t = .eml .one .one ∨
    t = .eml (.eml .one .one) .one ∨
    t = .eml .one (.eml .one .one) := by
  match t with
  | .one => exact Or.inl rfl
  | .eml a b =>
    simp only [EmlTree.gates] at h
    match a, b with
    | .one, .one => exact Or.inr (Or.inl rfl)
    | .eml a1 a2, .one =>
      simp only [EmlTree.gates] at h
      match a1, a2 with
      | .one, .one => exact Or.inr (Or.inr (Or.inl rfl))
      | .eml _ _, _ => simp [EmlTree.gates] at h; omega
      | _, .eml _ _ => simp [EmlTree.gates] at h; omega
    | .one, .eml b1 b2 =>
      simp only [EmlTree.gates] at h
      match b1, b2 with
      | .one, .one => exact Or.inr (Or.inr (Or.inr rfl))
      | .eml _ _, _ => simp [EmlTree.gates] at h; omega
      | _, .eml _ _ => simp [EmlTree.gates] at h; omega
    | .eml _ _, .eml _ _ =>
      simp [EmlTree.gates] at h; omega

private theorem exp_one_sub_one_ne_zero : Complex.exp (1 : ℂ) - 1 ≠ 0 := by
  intro h
  have hre : Real.exp 1 - 1 = 0 := by
    have := congrArg Complex.re h
    simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
  linarith [Real.exp_one_gt_d9]

/-- No `EmlTree` with `≤ 2` gates evaluates to `0` over `ℂ`. -/
theorem eval_ne_zero_of_gates_le_two (t : EmlTree) (h : t.gates ≤ 2) :
    t.eval (1 : ℂ) eml ≠ 0 := by
  rcases tree_gates_le_two_cases t h with rfl | rfl | rfl | rfl
  · exact one_ne_zero
  · change cE ≠ 0
    rw [cE_eq_exp_one]
    exact Complex.exp_ne_zero 1
  · simp only [EmlTree.eval, eml, lowerLog_one, sub_zero]
    exact Complex.exp_ne_zero _
  · change append0xc 1 ≠ 0
    rw [append0xc_eq]
    exact exp_one_sub_one_ne_zero

/-- Unconditional minimality of `0` at K = 7 over `ℂ`:
    every valid binary EML program of length `K ≤ 5` evaluates to a nonzero value. -/
theorem zero_minimal_k7 (p : List Bool) (hp : IsValidProgram p) (hlen : p.length ≤ 5) :
    evalRpn (1 : ℂ) eml p [] ≠ some [0] := by
  rw [evalRpn_eq_eval_fromRpn (1 : ℂ) eml p hp]
  intro h
  injection h with hcons
  injection hcons with hval
  have hgates : (fromRpn p hp).gates ≤ 2 := by
    have hl := toRpn_length (fromRpn p hp)
    rw [toRpn_fromRpn p hp] at hl
    omega
  exact eval_ne_zero_of_gates_le_two (fromRpn p hp) hgates hval

/-- Unconditional minimality of `0` at K = 7 over `EmlExt` (including `ln 0 = -∞`):
    every valid binary EML program of length `K ≤ 5` does not evaluate to `.finite 0`. -/
theorem ext_zero_minimal_k7 (p : List Bool) (hp : IsValidProgram p) (hlen : p.length ≤ 5) :
    evalRpn (EmlExt.finite 1) extEml p [] ≠ some [.finite 0] := by
  rw [evalRpn_eq_eval_fromRpn (EmlExt.finite 1) extEml p hp]
  intro h
  injection h with hcons
  injection hcons with hval
  have hgates : (fromRpn p hp).gates ≤ 2 := by
    have hl := toRpn_length (fromRpn p hp)
    rw [toRpn_fromRpn p hp] at hl
    omega
  rcases tree_gates_le_two_cases (fromRpn p hp) hgates with ht | ht | ht | ht
  · rw [ht] at hval; simp [EmlTree.eval] at hval
  · rw [ht] at hval
    simp only [EmlTree.eval] at hval
    rw [extEml_finite one_ne_zero] at hval
    injection hval with hz
    rw [show eml 1 1 = Complex.exp 1 from cE_eq_exp_one] at hz
    exact Complex.exp_ne_zero 1 hz
  · rw [ht] at hval
    simp only [EmlTree.eval] at hval
    rw [extEml_finite one_ne_zero, show eml 1 1 = Complex.exp 1 from cE_eq_exp_one,
      extEml_finite one_ne_zero] at hval
    injection hval with hz
    simp only [eml, lowerLog_one, sub_zero] at hz
    exact Complex.exp_ne_zero _ hz
  · rw [ht] at hval
    simp only [EmlTree.eval] at hval
    rw [extEml_finite one_ne_zero, show eml 1 1 = Complex.exp 1 from cE_eq_exp_one,
      extEml_finite (Complex.exp_ne_zero 1)] at hval
    injection hval with hz
    have : eml 1 (Complex.exp 1) = Complex.exp 1 - 1 := by
      unfold eml; rw [lowerLog_exp_of_im_zero (by simp)]
    rw [this] at hz
    exact exp_one_sub_one_ne_zero hz

end Eml.MinimalityZero
