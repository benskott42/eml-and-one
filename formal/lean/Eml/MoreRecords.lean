/-
  Machine-checked proofs for the constant words added to `lib/eml/best-known.json`
  with constant substitution (search words from `docs/search-k41.md`).

  Without `ln 0` (over `ℂ`, `evalRpn (1 : ℂ) eml`):
    - `111111EEE1EE11EE1EE1E`                       (K = 21) → `e²`
    - `11111EEE1EE11E1EE1E`                         (K = 19) → `1/e`
    - `1111E11E1EEE1EE11E1E1EE`                     (K = 23) → `-e`
    - `111E1EE1111111EEE1EE11E1EEE11E1E1EEE1E1EE`   (K = 41) → `3/2`
    - `1111111EEE1EE11E1EEE11E1E1EEE11EE`           (K = 33) → `-3/2`

  With `ln 0 = -∞` (over `EmlExt`, `evalRpn (EmlExt.finite 1) extEml`):
    - `11111E1EEEE11EE1E`                           (K = 17) → `1/e`
    - `11111E1EEEE11E1EE`                           (K = 17) → `-e`
    - `111E1EE1111111E1EEEE11EEE11E1E1EEE1E1EE`     (K = 39) → `3/2`
    - `1111111E1EEEE11EEE11E1E1EEE11EE`             (K = 31) → `-3/2`
    - `111E1EE1111111E1EEEE11EEE11E1E1EEE11EE1EE`   (K = 41) → `5/2`
    - `111111111E1EEEE11EEE11E1E1EEE11EEE1EE11EE`   (K = 41) → `-5/2`

  Each word is built from proved sub-words with `nd p q = p ++ q ++ [false]`
  (one `eml` gate), and `evalRpn_nd` evaluates it from its parts.
  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Eml.Basic
import Eml.Binary
import Eml.RpnSoundness
import Eml.Records
import Eml.Extended

namespace Eml.MoreRecords

open Eml Eml.Binary Eml.Records Eml.Extended Eml.RpnSoundness

/-! ### Evaluating a gate from its two sub-programs -/

/-- A run on a longer stack leaves the extra cells untouched. -/
theorem evalRpn_stack {α : Type} (one : α) (op : α → α → α) :
    ∀ (xs : List Bool) (st st' extra : List α),
      evalRpn one op xs st = some st' → evalRpn one op xs (st ++ extra) = some (st' ++ extra)
  | [], st, st', extra, h => by
      have hs : st = st' := Option.some.inj h
      subst hs; rfl
  | true :: rest, st, st', extra, h =>
      evalRpn_stack one op rest (one :: st) st' extra h
  | false :: rest, y :: x :: st, st', extra, h =>
      evalRpn_stack one op rest (op x y :: st) st' extra h
  | false :: _, [], _, _, h => by simp [evalRpn] at h
  | false :: _, [_], _, _, h => by simp [evalRpn] at h

/-- One gate: the program `p`, then `q`, then the EML press. -/
def nd (p q : List Bool) : List Bool := p ++ q ++ [false]

/-- The single press `1`. -/
def leaf : List Bool := [true]

theorem evalRpn_leaf {α : Type} (one : α) (op : α → α → α) :
    evalRpn one op leaf [] = some [one] := rfl

theorem evalRpn_nd {α : Type} (one : α) (op : α → α → α) {p q : List Bool} {a b : α}
    (hp : evalRpn one op p [] = some [a]) (hq : evalRpn one op q [] = some [b]) :
    evalRpn one op (nd p q) [] = some [op a b] := by
  have hq' : evalRpn one op q [a] = some [b, a] := evalRpn_stack one op q [] [b] [a] hq
  unfold nd
  rw [evalRpn_append, evalRpn_append, hp]
  dsimp only
  rw [hq']
  rfl

/-! ### Shared sub-words -/

/-- `11E` (`e`). -/
def bE : List Bool := nd leaf leaf
/-- `11E1E` (`exp e`). -/
def bExpE : List Bool := nd bE leaf
/-- `11E1E1E` (`exp (exp e)`). -/
def bExpExpE : List Bool := nd bExpE leaf
/-- `111E1EE` (`0`). -/
def bZero : List Bool := [true, true, true, false, true, false, false]
/-- The `ln` word `11 u E1EE`. -/
def bLn (u : List Bool) : List Bool := nd leaf (nd (nd leaf u) leaf)
/-- `11 x E 11E1E1E E` (`eml 1 (eml (eml 1 x) (exp (exp e)))`), the shared head of `-1/2` and `-3/2`. -/
def bHalfHead (x : List Bool) : List Bool := nd leaf (nd (nd leaf x) bExpExpE)

/-! ### Facts over `ℂ` -/

theorem eml_right_one (z : ℂ) : eml z 1 = Complex.exp z := by
  simp [eml, lowerLog_one]

private theorem exp_exp_one_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]

private theorem exp_one_im : (Complex.exp (1 : ℂ)).im = 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp, Complex.ofReal_im]

/-- `eml 1 (-1) = e + iπ` on the lower cut. -/
theorem eml_one_negOne : eml 1 (-1) = Complex.exp 1 + Real.pi * Complex.I := by
  unfold eml
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
  simp

/-- `eml (e + iπ) (exp (exp e)) = -2 e^e`. -/
theorem eml_mid : eml (Complex.exp 1 + Real.pi * Complex.I) (Complex.exp (Complex.exp (Complex.exp 1))) =
    -(2 * Complex.exp (Complex.exp 1)) := by
  unfold eml
  rw [Complex.exp_add, Complex.exp_pi_mul_I, lowerLog_exp_of_im_zero exp_exp_one_im]
  ring

/-- `eml 1 (-2 e^e) = -ln 2 + iπ`. -/
theorem eml_one_negTwoEE : eml 1 (-(2 * Complex.exp (Complex.exp 1))) =
    ((-Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I := by
  have hneg : -(2 * Real.exp (Real.exp 1)) < 0 := by linarith [Real.exp_pos (Real.exp 1)]
  have hcast : -(2 * Complex.exp (Complex.exp 1)) = ((-(2 * Real.exp (Real.exp 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [hcast, lowerLog_ofReal_neg hneg, neg_neg,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_exp]
  push_cast; ring

/-- The head of `-1/2` and `-3/2` evaluated: `-ln 2 + iπ`. -/
theorem halfHead_value : eml 1 (eml (eml 1 (-1)) (Complex.exp (Complex.exp (Complex.exp 1)))) =
    ((-Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I := by
  rw [eml_one_negOne, eml_mid, eml_one_negTwoEE]

theorem exp_halfHead : Complex.exp (((-Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I) = -(1 : ℂ) / 2 := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by norm_num)]
  push_cast; ring

/-- `eml v e = exp v - 1`. -/
theorem eml_right_e (v : ℂ) : eml v (Complex.exp 1) = Complex.exp v - 1 := by
  unfold eml
  rw [lowerLog_exp_of_im_zero (by simp)]

/-- `eml 0 (exp v) = 1 - v` for a real `v`. -/
theorem eml_zero_exp_real {v : ℂ} (hv : v.im = 0) : eml 0 (Complex.exp v) = 1 - v := by
  unfold eml
  rw [lowerLog_exp_of_im_zero hv, Complex.exp_zero]

/-! ### Words without `ln 0` (over `ℂ`) -/

/-- K = 21 `111111EEE1EE11EE1EE1E` → `e²`. -/
def bits_eSq : List Bool := nd bits_two leaf

theorem evalRpn_eSq : evalRpn (1 : ℂ) eml bits_eSq [] = some [Complex.exp 2] := by
  rw [bits_eSq, evalRpn_nd 1 eml evalRpn_two (evalRpn_leaf _ _), eml_right_one]

/-- K = 19 `11111EEE1EE11E1EE1E` → `1/e`. -/
def bits_invE_strict : List Bool := nd bits_negOne_strict leaf

theorem evalRpn_invE_strict :
    evalRpn (1 : ℂ) eml bits_invE_strict [] = some [Complex.exp (-1)] := by
  rw [bits_invE_strict, evalRpn_nd 1 eml evalRpn_negOne_strict (evalRpn_leaf _ _), eml_right_one]

/-- K = 23 `1111E11E1EEE1EE11E1E1EE` → `-e`. -/
def bits_negE_strict : List Bool := nd (bLn (nd bE bExpE)) bExpExpE

theorem evalRpn_negE_strict :
    evalRpn (1 : ℂ) eml bits_negE_strict [] = some [-Complex.exp 1] := by
  have hl := evalRpn_leaf (1 : ℂ) eml
  have he := evalRpn_nd 1 eml hl hl
  have hee := evalRpn_nd 1 eml he hl
  have heee := evalRpn_nd 1 eml hee hl
  have hu := evalRpn_nd 1 eml he hee
  have hln := evalRpn_nd 1 eml hl (evalRpn_nd 1 eml (evalRpn_nd 1 eml hl hu) hl)
  rw [bits_negE_strict, bLn, bExpExpE, bExpE, bE, evalRpn_nd 1 eml hln heee]
  simp only [eml_right_one]
  -- u = e^e − e, a positive real.
  have hu_val : eml (Complex.exp 1) (Complex.exp (Complex.exp 1)) =
      Complex.exp (Complex.exp 1) - Complex.exp 1 := by
    unfold eml; rw [lowerLog_exp_of_im_zero exp_one_im]
  have hlt : Real.exp 1 < Real.exp (Real.exp 1) := by
    have h := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1)); linarith
  have hpos : 0 < Real.exp (Real.exp 1) - Real.exp 1 := by linarith
  have hcast : Complex.exp (Complex.exp 1) - Complex.exp 1 =
      ((Real.exp (Real.exp 1) - Real.exp 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  rw [hu_val, hcast]
  -- eml 1 (exp (eml 1 u)) = lowerLog u = log u, a real number.
  have hlogu : lowerLog ((Real.exp (Real.exp 1) - Real.exp 1 : ℝ) : ℂ) =
      (Real.log (Real.exp (Real.exp 1) - Real.exp 1) : ℂ) := lowerLog_ofReal_pos hpos
  have hinner : eml 1 ((Real.exp (Real.exp 1) - Real.exp 1 : ℝ) : ℂ) =
      ((Real.exp 1 - Real.log (Real.exp (Real.exp 1) - Real.exp 1) : ℝ) : ℂ) := by
    unfold eml; rw [hlogu, ← Complex.ofReal_one, ← Complex.ofReal_exp]; push_cast; ring
  rw [hinner]
  have hln_val : eml 1 (Complex.exp ((Real.exp 1 - Real.log (Real.exp (Real.exp 1) - Real.exp 1) : ℝ) : ℂ)) =
      (Real.log (Real.exp (Real.exp 1) - Real.exp 1) : ℂ) := by
    unfold eml
    rw [lowerLog_exp_of_im_zero (Complex.ofReal_im _), ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hln_val]
  unfold eml
  rw [← Complex.ofReal_exp, Real.exp_log hpos, lowerLog_exp_of_im_zero exp_exp_one_im,
    ← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast; ring_nf

/-- K = 41 `111E1EE1111111EEE1EE11E1EEE11E1E1EEE1E1EE` → `3/2`. -/
def bits_threeHalves_strict : List Bool := nd bZero (nd bits_negHalf_strict leaf)

theorem evalRpn_threeHalves_strict :
    evalRpn (1 : ℂ) eml bits_threeHalves_strict [] = some [(3 : ℂ) / 2] := by
  rw [bits_threeHalves_strict, bZero, evalRpn_nd 1 eml evalRpn_0x74
    (evalRpn_nd 1 eml evalRpn_negHalf_strict (evalRpn_leaf _ _)), eml_right_one,
    eml_zero_exp_real (by simp)]
  norm_num

/-- K = 33 `1111111EEE1EE11E1EEE11E1E1EEE11EE` → `-3/2`. -/
def bits_negThreeHalves_strict : List Bool := nd (bHalfHead bits_negOne_strict) bE

theorem evalRpn_negThreeHalves_strict :
    evalRpn (1 : ℂ) eml bits_negThreeHalves_strict [] = some [-(3 : ℂ) / 2] := by
  have hl := evalRpn_leaf (1 : ℂ) eml
  have he := evalRpn_nd 1 eml hl hl
  have heee := evalRpn_nd 1 eml (evalRpn_nd 1 eml he hl) hl
  have hhead := evalRpn_nd 1 eml hl (evalRpn_nd 1 eml (evalRpn_nd 1 eml hl evalRpn_negOne_strict) heee)
  rw [bits_negThreeHalves_strict, bHalfHead, bExpExpE, bExpE, bE, evalRpn_nd 1 eml hhead he]
  simp only [eml_right_one]
  rw [halfHead_value, eml_right_e, exp_halfHead]
  congr 2; ring

/-! ### Facts over `EmlExt` -/

theorem extEml_right_one (z : ℂ) : extEml (.finite z) (.finite 1) = .finite (Complex.exp z) := by
  rw [extEml_finite one_ne_zero, eml_right_one]

/-! ### Words with `ln 0 = -∞` (over `EmlExt`) -/

/-- K = 17 `11111E1EEEE11EE1E` → `1/e`. -/
def bits_invE : List Bool := nd bits_0x7d0c leaf

theorem evalRpn_invE :
    evalRpn (EmlExt.finite 1) extEml bits_invE [] = some [.finite (Complex.exp (-1))] := by
  rw [bits_invE, evalRpn_nd _ extEml evalRpn_0x7d0c (evalRpn_leaf _ _), extEml_right_one]

/-- K = 17 `11111E1EEEE11E1EE` → `-e`. -/
def bits_negE : List Bool := nd bits_0x7d0 bExpE

theorem evalRpn_negE :
    evalRpn (EmlExt.finite 1) extEml bits_negE [] = some [.finite (-Complex.exp 1)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have he := evalRpn_nd _ extEml hl hl
  rw [bits_negE, bExpE, bE, evalRpn_nd _ extEml evalRpn_0x7d0 (evalRpn_nd _ extEml he hl)]
  simp only [extEml_right_one]
  simp [extEml, extExp, extLowerLog, extSub, Complex.exp_ne_zero,
    lowerLog_exp_of_im_zero exp_one_im]

/-- K = 39 `111E1EE1111111E1EEEE11EEE11E1E1EEE1E1EE` → `3/2`. -/
def bits_threeHalves : List Bool := nd bZero (nd bits_negHalf leaf)

theorem evalRpn_threeHalves :
    evalRpn (EmlExt.finite 1) extEml bits_threeHalves [] = some [.finite ((3 : ℂ) / 2)] := by
  rw [bits_threeHalves, bZero, evalRpn_nd _ extEml evalRpn_ext_0x74
    (evalRpn_nd _ extEml evalRpn_negHalf (evalRpn_leaf _ _)), extEml_right_one,
    extEml_finite (Complex.exp_ne_zero _), eml_zero_exp_real (by simp)]
  norm_num

/-- The head `11 (-1) E 11E1E1E E` with `ln 0`, evaluated: `-ln 2 + iπ`. -/
theorem ext_halfHead :
    evalRpn (EmlExt.finite 1) extEml (bHalfHead bits_0x7d0c) [] =
      some [.finite (((-Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have he := evalRpn_nd _ extEml hl hl
  have heee := evalRpn_nd _ extEml (evalRpn_nd _ extEml he hl) hl
  rw [bHalfHead, bExpExpE, bExpE, bE,
    evalRpn_nd _ extEml hl (evalRpn_nd _ extEml (evalRpn_nd _ extEml hl evalRpn_0x7d0c) heee)]
  simp only [extEml_right_one]
  rw [extEml_finite (by norm_num : (-1 : ℂ) ≠ 0), eml_one_negOne,
    extEml_finite (Complex.exp_ne_zero _), eml_mid,
    extEml_finite (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))),
    eml_one_negTwoEE]

/-- K = 31 `1111111E1EEEE11EEE11E1E1EEE11EE` → `-3/2`. -/
def bits_negThreeHalves : List Bool := nd (bHalfHead bits_0x7d0c) bE

theorem evalRpn_negThreeHalves :
    evalRpn (EmlExt.finite 1) extEml bits_negThreeHalves [] = some [.finite (-(3 : ℂ) / 2)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  rw [bits_negThreeHalves, bE, evalRpn_nd _ extEml ext_halfHead (evalRpn_nd _ extEml hl hl),
    extEml_right_one, extEml_finite (Complex.exp_ne_zero _), eml_right_e, exp_halfHead]
  congr 2; ring_nf

/-- K = 41 `111E1EE1111111E1EEEE11EEE11E1E1EEE11EE1EE` → `5/2`. -/
def bits_fiveHalves : List Bool := nd bZero (nd bits_negThreeHalves leaf)

theorem evalRpn_fiveHalves :
    evalRpn (EmlExt.finite 1) extEml bits_fiveHalves [] = some [.finite ((5 : ℂ) / 2)] := by
  rw [bits_fiveHalves, bZero, evalRpn_nd _ extEml evalRpn_ext_0x74
    (evalRpn_nd _ extEml evalRpn_negThreeHalves (evalRpn_leaf _ _)), extEml_right_one,
    extEml_finite (Complex.exp_ne_zero _), eml_zero_exp_real (by simp)]
  norm_num

/-- K = 41 `111111111E1EEEE11EEE11E1E1EEE11EEE1EE11EE` → `-5/2`. -/
def bits_negFiveHalves : List Bool := nd (bLn bits_negThreeHalves) bE

theorem evalRpn_negFiveHalves :
    evalRpn (EmlExt.finite 1) extEml bits_negFiveHalves [] = some [.finite (-(5 : ℂ) / 2)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have hln := evalRpn_nd _ extEml hl
    (evalRpn_nd _ extEml (evalRpn_nd _ extEml hl evalRpn_negThreeHalves) hl)
  rw [bits_negFiveHalves, bLn, bE, evalRpn_nd _ extEml hln (evalRpn_nd _ extEml hl hl)]
  have hne : (-(3 : ℂ) / 2) ≠ 0 := by norm_num
  -- The ln word on a nonzero finite value is the principal log (`extEmlLn_finite_ne_zero`).
  have hlnv : extEml (.finite 1) (extEml (extEml (.finite 1) (.finite (-(3 : ℂ) / 2))) (.finite 1)) =
      .finite (Complex.log (-(3 : ℂ) / 2)) := extEmlLn_finite_ne_zero hne
  rw [hlnv, extEml_right_one, extEml_finite (Complex.exp_ne_zero _), eml_right_e,
    Complex.exp_log hne]
  congr 2; ring_nf

end Eml.MoreRecords
