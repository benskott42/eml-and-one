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

/-! ### `±2πi` without `ln 0` (K = 31)

Both words pass through `P = x + iπ` with `x = e − ln(e^e − e)`, and through
`R = exp(e − log P) = e^e / P`.
- `+2πi`: `eml (eml 1 R) (exp P) = P − lowerLog (exp P) = 2πi`, since `exp P`
  lies on the negative real axis and the lower cut sends it to `P − 2πi`.
- `−2πi`: `eml Q (exp R) = R − lowerLog (exp R) = 2πi · κ_L(R)` with
  `Im R = −e^e π / (x² + π²) ∈ [−3π, −π)`, so the unwinding number is `−1`.
-/

/-- `x = e − ln(e^e − e)`, the real part of `P`. -/
noncomputable def twoPiX : ℝ := Real.exp 1 - Real.log (Real.exp (Real.exp 1) - Real.exp 1)

/-- `P = x + iπ`. -/
noncomputable def twoPiP : ℂ := (twoPiX : ℂ) + Real.pi * Complex.I

private theorem e_lt_three : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]

private theorem e_gt : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]

/-- `e^e > 11`: `e^e > e^{2.5} = e² · e^{0.5} ≥ e² · 1.5`. -/
private theorem ee_gt_eleven : (11 : ℝ) < Real.exp (Real.exp 1) := by
  have h25 : Real.exp 2.5 < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr (by linarith [e_gt])
  have hsplit : Real.exp 2.5 = Real.exp 1 * Real.exp 1 * Real.exp 0.5 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hhalf : (1.5 : ℝ) ≤ Real.exp 0.5 := by
    have := Real.add_one_le_exp (0.5 : ℝ); linarith
  have he2 : (7.38 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith [e_gt]
  have : (11 : ℝ) < Real.exp 2.5 := by
    rw [hsplit]; nlinarith [Real.exp_pos 0.5]
  linarith

/-- `e^e < 20.1`: `e^e < e³ < 2.7183³`. -/
private theorem ee_lt : Real.exp (Real.exp 1) < 20.1 := by
  have h3 : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr e_lt_three
  have hsplit : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hlt : Real.exp 1 < 2.7183 := by linarith [Real.exp_one_lt_d9]
  have : Real.exp 3 < 20.1 := by
    rw [hsplit]; nlinarith [Real.exp_pos 1]
  linarith

private theorem twoPiX_bounds : -0.29 < twoPiX ∧ twoPiX < 0.72 := by
  have hpos : 0 < Real.exp (Real.exp 1) - Real.exp 1 := by linarith [ee_gt_eleven, e_lt_three]
  have hlog_gt : 2 < Real.log (Real.exp (Real.exp 1) - Real.exp 1) := by
    rw [Real.lt_log_iff_exp_lt hpos]
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have hlt : Real.exp 1 < 2.7183 := by linarith [Real.exp_one_lt_d9]
    rw [hsplit]; nlinarith [ee_gt_eleven, Real.exp_pos 1]
  have hlog_lt : Real.log (Real.exp (Real.exp 1) - Real.exp 1) < 3 := by
    rw [Real.log_lt_iff_lt_exp hpos]
    have : Real.exp (Real.exp 1) < Real.exp 3 := Real.exp_lt_exp.mpr e_lt_three
    linarith [Real.exp_pos 1]
  unfold twoPiX
  constructor <;> linarith [e_gt, e_lt_three, Real.exp_one_lt_d9]

private theorem twoPiP_im : twoPiP.im = Real.pi := by simp [twoPiP]

private theorem twoPiP_re : twoPiP.re = twoPiX := by simp [twoPiP]

private theorem twoPiP_ne : twoPiP ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [twoPiP_im, Complex.zero_im] at this
  exact Real.pi_ne_zero this

/-- `eml 1 (exp (exp e)) = e − e^e`, a negative real. -/
private theorem twoPi_v1 :
    eml 1 (Complex.exp (Complex.exp (Complex.exp 1))) =
      ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) := by
  unfold eml
  rw [lowerLog_exp_of_im_zero exp_exp_one_im, ← Complex.ofReal_one, ← Complex.ofReal_exp,
    ← Complex.ofReal_exp]
  push_cast; ring

/-- `eml 1 (e − e^e) = P`. -/
private theorem twoPi_P :
    eml 1 ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) = twoPiP := by
  have hneg : Real.exp 1 - Real.exp (Real.exp 1) < 0 := by linarith [ee_gt_eleven, e_lt_three]
  unfold eml
  rw [lowerLog_ofReal_neg hneg, ← Complex.ofReal_one, ← Complex.ofReal_exp]
  unfold twoPiP twoPiX
  push_cast; ring_nf

/-- `eml 1 P = e − log P` (`P` is off the negative real axis). -/
private theorem twoPi_Q : eml 1 twoPiP = Complex.exp 1 - Complex.log twoPiP := by
  unfold eml
  rw [lowerLog_eq_log_of_not_isNegReal (fun h => by
    have := h.2; rw [twoPiP_im] at this; exact Real.pi_ne_zero this)]

/-- `R = exp (e − log P) = e^e / P`. -/
private theorem twoPi_R :
    Complex.exp (Complex.exp 1 - Complex.log twoPiP) = Complex.exp (Complex.exp 1) / twoPiP := by
  rw [Complex.exp_sub, Complex.exp_log twoPiP_ne]

private theorem twoPi_R_im :
    (Complex.exp (Complex.exp 1) / twoPiP).im =
      -(Real.exp (Real.exp 1) * Real.pi) / (twoPiX ^ 2 + Real.pi ^ 2) := by
  have hee : Complex.exp (Complex.exp (1 : ℂ)) = ((Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  rw [hee, Complex.div_im, Complex.normSq_apply, twoPiP_re, twoPiP_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  rw [neg_div, ← sq, ← sq]
  ring

/-- `Im R ∈ [−3π, −π)`. -/
private theorem twoPi_R_im_bounds :
    -3 * Real.pi ≤ (Complex.exp (Complex.exp 1) / twoPiP).im ∧
      (Complex.exp (Complex.exp 1) / twoPiP).im < -Real.pi := by
  rw [twoPi_R_im]
  obtain ⟨hx1, hx2⟩ := twoPiX_bounds
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hD : 0 < twoPiX ^ 2 + Real.pi ^ 2 := by positivity
  have hx2sq : twoPiX ^ 2 < 0.53 := by nlinarith
  have hee1 := ee_gt_eleven
  have hee2 := ee_lt
  constructor
  · rw [le_div_iff₀ hD]; nlinarith
  · rw [div_lt_iff₀ hD]; nlinarith

private theorem lowerUnwind_eq_neg_one {z : ℂ} (h1 : -3 * Real.pi ≤ z.im) (h2 : z.im < -Real.pi) :
    lowerUnwind z = -1 := by
  unfold lowerUnwind
  rw [Int.floor_eq_iff]
  have hpi2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  constructor
  · rw [le_div_iff₀ hpi2]; push_cast; linarith
  · rw [div_lt_iff₀ hpi2]; push_cast; linarith

private theorem lowerUnwind_twoPiP : lowerUnwind twoPiP = 1 := by
  unfold lowerUnwind
  rw [twoPiP_im, Int.floor_eq_iff]
  have hpi := Real.pi_pos
  have hdiv : (Real.pi + Real.pi) / (2 * Real.pi) = 1 := by field_simp; ring
  rw [hdiv]; norm_num

/-- `11E1E1E` (`exp (exp e)`), then `111E1E1EE`, `P`, `Q`, `R`. -/
def bV1 : List Bool := nd leaf bExpExpE
def bP : List Bool := nd leaf bV1
def bQ : List Bool := nd leaf bP
def bR : List Bool := nd bQ leaf

/-- K = 31 `111111E1E1EEEE1EE1111E1E1EEE1EE` → `+2πi` (lower cut, no `ln 0`). -/
def bits_twoPiI : List Bool := nd (nd leaf bR) (nd bP leaf)

/-- K = 31 `11111E1E1EEEE11111E1E1EEEE1E1EE` → `−2πi` (lower cut, no `ln 0`). -/
def bits_negTwoPiI : List Bool := nd bQ (nd bR leaf)

/-- The shared chain: `P`, `Q = eml 1 P`, and `R = eml Q 1` as evaluated values. -/
private theorem twoPi_chain :
    evalRpn (1 : ℂ) eml bP [] = some [twoPiP] ∧
      evalRpn (1 : ℂ) eml bQ [] = some [Complex.exp 1 - Complex.log twoPiP] ∧
      evalRpn (1 : ℂ) eml bR [] = some [Complex.exp (Complex.exp 1) / twoPiP] := by
  have hl := evalRpn_leaf (1 : ℂ) eml
  have he := evalRpn_nd 1 eml hl hl
  have heee := evalRpn_nd 1 eml (evalRpn_nd 1 eml he hl) hl
  have hv1 := evalRpn_nd 1 eml hl heee
  have hp := evalRpn_nd 1 eml hl hv1
  simp only [eml_right_one] at hp
  rw [twoPi_v1, twoPi_P] at hp
  have hq := evalRpn_nd 1 eml hl hp
  rw [twoPi_Q] at hq
  have hr := evalRpn_nd 1 eml hq hl
  rw [eml_right_one, twoPi_R] at hr
  refine ⟨?_, ?_, ?_⟩
  · rw [bP, bV1, bExpExpE, bExpE, bE]; exact hp
  · rw [bQ, bP, bV1, bExpExpE, bExpE, bE]; exact hq
  · rw [bR, bQ, bP, bV1, bExpExpE, bExpE, bE]; exact hr

theorem evalRpn_twoPiI :
    evalRpn (1 : ℂ) eml bits_twoPiI [] = some [2 * Real.pi * Complex.I] := by
  obtain ⟨hp, -, hr⟩ := twoPi_chain
  rw [bits_twoPiI, evalRpn_nd 1 eml (evalRpn_nd 1 eml (evalRpn_leaf _ _) hr)
    (evalRpn_nd 1 eml hp (evalRpn_leaf _ _)), eml_right_one]
  obtain ⟨hb1, hb2⟩ := twoPi_R_im_bounds
  -- log R = Q, since Im Q = −arg P ∈ (−π, 0).
  have hR : Complex.exp (Complex.exp 1) / twoPiP = Complex.exp (Complex.exp 1 - Complex.log twoPiP) :=
    twoPi_R.symm
  have hQim : (Complex.exp 1 - Complex.log twoPiP).im = -Complex.arg twoPiP := by
    simp [Complex.log_im, Complex.exp_im]
  have harg_lt : Complex.arg twoPiP < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr (by rw [twoPiP_im]; exact Real.pi_ne_zero))
  have harg_gt : -Real.pi < Complex.arg twoPiP := Complex.neg_pi_lt_arg _
  have hlogR : lowerLog (Complex.exp (Complex.exp 1) / twoPiP) = Complex.exp 1 - Complex.log twoPiP := by
    rw [lowerLog_eq_log_of_not_isNegReal (fun h => by linarith [h.2, Real.pi_pos]), hR,
      Complex.log_exp (by rw [hQim]; linarith) (by rw [hQim]; linarith)]
  have hinner : eml 1 (Complex.exp (Complex.exp 1) / twoPiP) = Complex.log twoPiP := by
    unfold eml; rw [hlogR]; ring
  rw [hinner]
  unfold eml
  rw [Complex.exp_log twoPiP_ne, lowerLog_exp_eq_sub_unwind, lowerUnwind_twoPiP]
  congr 2; push_cast; ring

theorem evalRpn_negTwoPiI :
    evalRpn (1 : ℂ) eml bits_negTwoPiI [] = some [-(2 * Real.pi * Complex.I)] := by
  obtain ⟨-, hq, hr⟩ := twoPi_chain
  rw [bits_negTwoPiI, evalRpn_nd 1 eml hq (evalRpn_nd 1 eml hr (evalRpn_leaf _ _)), eml_right_one]
  obtain ⟨hb1, hb2⟩ := twoPi_R_im_bounds
  unfold eml
  rw [twoPi_R, lowerLog_exp_eq_sub_unwind, lowerUnwind_eq_neg_one hb1 hb2]
  congr 2; push_cast; ring

/-! ### `−ln 2`, `−2/3`, `−5/3`

These words scale `e^e` by a real `c > 0` and take `eml 1` of it:
`eml 1 (c·e^e) = −ln c` and `eml 1 (−c·e^e) = −ln c + iπ` (lower cut).
-/

private theorem ee_ofReal : Complex.exp (Complex.exp (1 : ℂ)) = ((Real.exp (Real.exp 1) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]

/-- `eml 1 (c·e^e) = −ln c` for a real `c > 0`. -/
theorem eml_one_scaledEE {c : ℝ} (hc : 0 < c) :
    eml 1 ((c : ℂ) * Complex.exp (Complex.exp 1)) = ((-Real.log c : ℝ) : ℂ) := by
  have hpos : 0 < c * Real.exp (Real.exp 1) := by positivity
  have hcast : (c : ℂ) * Complex.exp (Complex.exp 1) = ((c * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [ee_ofReal]; push_cast; rfl
  unfold eml
  rw [hcast, lowerLog_ofReal_pos hpos, Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, ← Complex.ofReal_one, ← Complex.ofReal_exp]
  push_cast; ring

/-- `eml 1 (−c·e^e) = −ln c + iπ` for a real `c > 0` (lower cut). -/
theorem eml_one_negScaledEE {c : ℝ} (hc : 0 < c) :
    eml 1 (-((c : ℂ) * Complex.exp (Complex.exp 1))) = ((-Real.log c : ℝ) : ℂ) + Real.pi * Complex.I := by
  have hneg : -(c * Real.exp (Real.exp 1)) < 0 := by
    have : 0 < c * Real.exp (Real.exp 1) := by positivity
    linarith
  have hcast : -((c : ℂ) * Complex.exp (Complex.exp 1)) = ((-(c * Real.exp (Real.exp 1)) : ℝ) : ℂ) := by
    rw [ee_ofReal]; push_cast; rfl
  unfold eml
  rw [hcast, lowerLog_ofReal_neg hneg, neg_neg,
    Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)), Real.log_exp,
    ← Complex.ofReal_one, ← Complex.ofReal_exp]
  push_cast; ring

/-- `eml e (exp (−c·e^e)) = (1 + c)·e^e` for a real `c`. -/
theorem eml_e_expNegScaledEE (c : ℝ) :
    eml (Complex.exp 1) (Complex.exp (-((c : ℂ) * Complex.exp (Complex.exp 1)))) =
      (((1 + c : ℝ)) : ℂ) * Complex.exp (Complex.exp 1) := by
  have him : (-((c : ℂ) * Complex.exp (Complex.exp 1))).im = 0 := by
    rw [ee_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_neg]; exact Complex.ofReal_im _
  unfold eml
  rw [lowerLog_exp_of_im_zero him]
  push_cast; ring

/-- `exp (−ln c) − 1 = 1/c − 1` for a real `c > 0`. -/
private theorem exp_negLog_sub_one {c : ℝ} (hc : 0 < c) :
    Complex.exp (((-Real.log c : ℝ) : ℂ)) - 1 = (((1 / c - 1 : ℝ)) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hc]
  push_cast; ring

/-- K = 27 `111E111111E1EEEE11EEE1E1EEE` → `−ln 2` (uses `ln 0`). -/
def bits_negLn2 : List Bool :=
  nd leaf (nd bE (nd (nd (nd leaf bits_0x7d0c) leaf) leaf))

theorem evalRpn_negLn2 :
    evalRpn (EmlExt.finite 1) extEml bits_negLn2 [] = some [.finite (-Complex.log 2)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have he := evalRpn_nd _ extEml hl hl
  rw [bits_negLn2, bE, evalRpn_nd _ extEml hl (evalRpn_nd _ extEml he
    (evalRpn_nd _ extEml (evalRpn_nd _ extEml (evalRpn_nd _ extEml hl evalRpn_0x7d0c) hl) hl))]
  simp only [extEml_right_one]
  rw [extEml_finite (by norm_num : (-1 : ℂ) ≠ 0), eml_one_negOne, extEml_right_one, extEml_right_one]
  have hnegee : Complex.exp (Complex.exp 1 + Real.pi * Complex.I) =
      -(((1 : ℝ) : ℂ) * Complex.exp (Complex.exp 1)) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; push_cast; ring
  rw [hnegee, extEml_finite (Complex.exp_ne_zero _), eml_e_expNegScaledEE,
    extEml_finite (by rw [ee_ofReal]; norm_num),
    show ((1 + 1 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) by norm_num, eml_one_scaledEE (by norm_num)]
  congr 3
  push_cast
  rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The `−2/3` body after `−1`: `eml (eml 1 (eml e (exp (−2e^e)))) e = −2/3`. -/
private theorem negTwoThirds_tail :
    eml (eml 1 (eml (Complex.exp 1) (Complex.exp (-(((2 : ℝ) : ℂ) * Complex.exp (Complex.exp 1))))))
      (Complex.exp 1) = -(2 : ℂ) / 3 := by
  rw [eml_e_expNegScaledEE, show ((1 + 2 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
    eml_one_scaledEE (by norm_num), eml_right_e, exp_negLog_sub_one (by norm_num)]
  push_cast; norm_num

private theorem eml_mid' : eml (Complex.exp 1 + Real.pi * Complex.I) (Complex.exp (Complex.exp (Complex.exp 1))) =
    -(((2 : ℝ) : ℂ) * Complex.exp (Complex.exp 1)) := by
  rw [eml_mid]; push_cast; ring

/-- K = 37 `111E111111E1EEEE11EEE11E1E1EE1EEE11EE` → `−2/3` (uses `ln 0`). -/
def bits_negTwoThirds : List Bool :=
  nd (nd leaf (nd bE (nd (nd (nd leaf bits_0x7d0c) bExpExpE) leaf))) bE

theorem evalRpn_negTwoThirds :
    evalRpn (EmlExt.finite 1) extEml bits_negTwoThirds [] = some [.finite (-(2 : ℂ) / 3)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have he := evalRpn_nd _ extEml hl hl
  have heee := evalRpn_nd _ extEml (evalRpn_nd _ extEml he hl) hl
  rw [bits_negTwoThirds, bExpExpE, bExpE, bE, evalRpn_nd _ extEml (evalRpn_nd _ extEml hl
    (evalRpn_nd _ extEml he (evalRpn_nd _ extEml
      (evalRpn_nd _ extEml (evalRpn_nd _ extEml hl evalRpn_0x7d0c) heee) hl))) he]
  simp only [extEml_right_one]
  rw [extEml_finite (by norm_num : (-1 : ℂ) ≠ 0), eml_one_negOne,
    extEml_finite (Complex.exp_ne_zero _), eml_mid', extEml_right_one,
    extEml_finite (Complex.exp_ne_zero _), eml_e_expNegScaledEE,
    extEml_finite (by rw [ee_ofReal]; norm_num),
    extEml_finite (Complex.exp_ne_zero _),
    show ((1 + 2 : ℝ) : ℂ) = ((3 : ℝ) : ℂ) by norm_num, eml_one_scaledEE (by norm_num), eml_right_e,
    exp_negLog_sub_one (by norm_num)]
  congr 3
  push_cast; norm_num

/-- K = 39 `111E111111EEE1EE11E1EEE11E1E1EE1EEE11EE` → `−2/3` (no `ln 0`). -/
def bits_negTwoThirds_strict : List Bool :=
  nd (nd leaf (nd bE (nd (nd (nd leaf bits_negOne_strict) bExpExpE) leaf))) bE

theorem evalRpn_negTwoThirds_strict :
    evalRpn (1 : ℂ) eml bits_negTwoThirds_strict [] = some [-(2 : ℂ) / 3] := by
  have hl := evalRpn_leaf (1 : ℂ) eml
  have he := evalRpn_nd 1 eml hl hl
  have heee := evalRpn_nd 1 eml (evalRpn_nd 1 eml he hl) hl
  rw [bits_negTwoThirds_strict, bExpExpE, bExpE, bE, evalRpn_nd 1 eml (evalRpn_nd 1 eml hl
    (evalRpn_nd 1 eml he (evalRpn_nd 1 eml
      (evalRpn_nd 1 eml (evalRpn_nd 1 eml hl evalRpn_negOne_strict) heee) hl))) he]
  simp only [eml_right_one]
  rw [eml_one_negOne, eml_mid', negTwoThirds_tail]

/-- K = 41 `11111111E1EEEE11E1E1EEE11EEE11E1E1EEE11EE` → `−5/3` (uses `ln 0`). -/
def bits_negFiveThirds : List Bool :=
  nd (nd leaf (nd (nd leaf bits_0x1fa1a8c) bExpExpE)) bE

theorem evalRpn_negFiveThirds :
    evalRpn (EmlExt.finite 1) extEml bits_negFiveThirds [] = some [.finite (-(5 : ℂ) / 3)] := by
  have hl := evalRpn_leaf (EmlExt.finite 1) extEml
  have he := evalRpn_nd _ extEml hl hl
  have heee := evalRpn_nd _ extEml (evalRpn_nd _ extEml he hl) hl
  rw [bits_negFiveThirds, bExpExpE, bExpE, bE, evalRpn_nd _ extEml (evalRpn_nd _ extEml hl
    (evalRpn_nd _ extEml (evalRpn_nd _ extEml hl evalRpn_0x1fa1a8c) heee)) he]
  simp only [extEml_right_one]
  -- eml 1 (−2) = (e − ln 2) + iπ on the lower cut.
  have h1m2 : eml 1 (-2) = ((Real.exp 1 - Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I := by
    unfold eml
    rw [show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num),
      ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring_nf
  -- exp of that, minus e^e, is −(3/2)·e^e.
  have hmid : eml (((Real.exp 1 - Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I)
      (Complex.exp (Complex.exp (Complex.exp 1))) = -(((3 / 2 : ℝ) : ℂ) * Complex.exp (Complex.exp 1)) := by
    unfold eml
    rw [lowerLog_exp_of_im_zero exp_exp_one_im, Complex.exp_add, Complex.exp_pi_mul_I,
      ← Complex.ofReal_exp, Real.exp_sub, Real.exp_log (by norm_num), ee_ofReal]
    push_cast; ring
  rw [extEml_finite (by norm_num : (-2 : ℂ) ≠ 0), h1m2, extEml_finite (Complex.exp_ne_zero _), hmid,
    extEml_finite (by rw [ee_ofReal]; norm_num), eml_one_negScaledEE (by norm_num),
    extEml_finite (Complex.exp_ne_zero _), eml_right_e, Complex.exp_add, Complex.exp_pi_mul_I,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  congr 2; push_cast; norm_num

end Eml.MoreRecords
