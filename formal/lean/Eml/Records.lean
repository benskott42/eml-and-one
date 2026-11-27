/-
  Machine-checked Lean 4 + Mathlib proofs of concrete `ln 0`-free constant
  records over `ℂ` (`lib/eml/best-known.json`, `docs/binary.md`,
  `tools/minimality/decide.py`):
    - `11111EEE1EE11E1EE`                      (K = 17)           → `-1`  (proved minimal without `ln 0`)
    - `111111EEE1EE11EE1EE`                    (K = 19, `0x7e264`) → `2`  (proved minimal)
    - `111111E1E1EEE1EE11E1EEE`                (K = 23)           → `+iπ` (lower cut, proved minimal without `ln 0`)
    - `11111111EEE1EE11EE1EEE1EE`              (K = 25, `0x1fe2644`) → `ln 2`
    - `11111111EEE1EE11EEE1EE11EE1EE`          (K = 29, `0x1fe26264`) → `3`
    - `11111111EEE1EE11EE1EEE11E1E1EEE11EE`    (K = 35)           → `-3`
    - `1111111111EEE1EE11EEE1EE11EEE1EE11EE1EE` (K = 39)          → `4`
    - `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE1E` (K = 39)          → `2/3`
    - `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE11EE` (K = 41)        → `-1/3`

  Every proof evaluates `evalRpn (1 : ℂ) eml` directly on the exact bitstring.
  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Eml.Basic
import Eml.Binary
import Eml.TreeBijection
import Eml.Arithmetic

namespace Eml.Records

open Eml
open Eml.Binary

private theorem exp_one_gt_two : (2 : ℝ) < Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

private theorem exp_one_gt_one : (1 : ℝ) < Real.exp 1 := by
  linarith [exp_one_gt_two]

private theorem exp_exp_one_gt_exp_one : Real.exp 1 < Real.exp (Real.exp 1) := by
  have h := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1))
  linarith

/-- Helper: `emlLn (e - 1) = Real.log (e - 1)`. -/
private theorem emlLn_exp_one_sub_one :
    emlLn (Complex.exp 1 - 1) = (Real.log (Real.exp 1 - 1) : ℂ) := by
  have hpos : (0 : ℝ) < Real.exp 1 - 1 := by linarith [exp_one_gt_one]
  have hcast : Complex.exp (1 : ℂ) - 1 = ((Real.exp 1 - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp]; push_cast; rfl
  rw [emlLn_eq_log, hcast, Complex.ofReal_log (le_of_lt hpos)]

/-- Helper: `emlLn (e - 2) = Real.log (e - 2)`. -/
private theorem emlLn_exp_one_sub_two :
    emlLn (Complex.exp 1 - 2) = (Real.log (Real.exp 1 - 2) : ℂ) := by
  have hpos : (0 : ℝ) < Real.exp 1 - 2 := by linarith [exp_one_gt_two]
  have hcast : Complex.exp (1 : ℂ) - 2 = ((Real.exp 1 - 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp]; push_cast; rfl
  rw [emlLn_eq_log, hcast, Complex.ofReal_log (le_of_lt hpos)]

/-- K = 17 word `11111EEE1EE11E1EE` (`-1` without `ln 0`, proved minimal). -/
def bits_negOne_strict : List Bool :=
  [true, true, true, true, true, false, false, false, true, false, false,
   true, true, false, true, false, false]

theorem valid_negOne_strict : IsValidProgram bits_negOne_strict := rfl

theorem evalRpn_negOne_strict :
    evalRpn (1 : ℂ) eml bits_negOne_strict [] = some [-1] := by
  change some [eml (emlLn (eml 1 (eml 1 1))) (eml (eml 1 1) 1)] = some [-1]
  have h1 : eml 1 (eml 1 1) = Complex.exp 1 - 1 := append0xc_eq 1
  have h2 : eml (eml 1 1) 1 = Complex.exp (Complex.exp 1) := by
    simp [eml, lowerLog_one]
  rw [h1, h2, emlLn_exp_one_sub_one]
  unfold eml
  have hpos : (0 : ℝ) < Real.exp 1 - 1 := by linarith [exp_one_gt_one]
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  rw [← Complex.ofReal_exp, Real.exp_log hpos, lowerLog_exp_of_im_zero he1_im]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  congr 2
  push_cast
  ring

/-- K = 19 word `111111EEE1EE11EE1EE` (`0x7e264`, `2` without `ln 0`, proved minimal). -/
def bits_two : List Bool :=
  [true, true, true, true, true, true, false, false, false, true, false, false,
   true, true, false, false, true, false, false]

/-- `cTwo` as an EML expression over `ℂ` (the K = 19 word `0x7e264`). -/
noncomputable def cTwo : ℂ :=
  eml 1 (eml (eml (emlLn (eml 1 (eml 1 1))) (eml 1 1)) 1)

theorem valid_two : IsValidProgram bits_two := rfl

theorem cTwo_eq_two : cTwo = 2 := by
  unfold cTwo
  have h1 : eml 1 (eml 1 1) = Complex.exp 1 - 1 := append0xc_eq 1
  rw [h1, emlLn_exp_one_sub_one]
  have hpos : (0 : ℝ) < Real.exp 1 - 1 := by linarith [exp_one_gt_one]
  have hmid : eml ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) (eml 1 1) = Complex.exp 1 - 2 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp),
      ← Complex.ofReal_exp, Real.exp_log hpos, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hmid]
  unfold eml
  rw [lowerLog_one, sub_zero]
  have him : (Complex.exp (1 : ℂ) - 2).im = 0 := by
    simp [Complex.exp_im]
  rw [lowerLog_exp_of_im_zero him]
  ring

theorem evalRpn_two :
    evalRpn (1 : ℂ) eml bits_two [] = some [2] := by
  change some [cTwo] = some [2]
  rw [cTwo_eq_two]

/-- K = 23 word `111111E1E1EEE1EE11E1EEE` (`+iπ` on the lower cut, without `ln 0`,
    proved minimal). This theorem depends genuinely on the lower branch cut
    `lowerLog`: under Mathlib's principal `Complex.log`, the same word would
    evaluate to `-iπ`. -/
def bits_ipi_strict : List Bool :=
  [true, true, true, true, true, true, false, true, false, true, false, false, false,
   true, false, false, true, true, false, true, false, false, false]

theorem valid_ipi_strict : IsValidProgram bits_ipi_strict := rfl

theorem evalRpn_ipi_strict :
    evalRpn (1 : ℂ) eml bits_ipi_strict [] = some [Real.pi * Complex.I] := by
  change some [eml 1 (eml (emlLn (eml 1 (eml (eml (eml 1 1) 1) 1))) (eml (eml 1 1) 1))] =
    some [Real.pi * Complex.I]
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hstep1 : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hstep2 : eml 1 (eml (eml (eml 1 1) 1) 1) = Complex.exp 1 - Complex.exp (Complex.exp 1) := by
    rw [hstep1]
    unfold eml
    rw [lowerLog_exp_of_im_zero hee_im]
  have hneg_r : Real.exp 1 - Real.exp (Real.exp 1) < 0 := by
    linarith [exp_exp_one_gt_exp_one]
  have hcast_neg : Complex.exp (1 : ℂ) - Complex.exp (Complex.exp 1) =
      ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  have hne_neg : Complex.exp (1 : ℂ) - Complex.exp (Complex.exp 1) ≠ 0 := by
    rw [hcast_neg]
    exact Complex.ofReal_ne_zero.mpr (ne_of_lt hneg_r)
  have hstep3 : eml (emlLn (eml 1 (eml (eml (eml 1 1) 1) 1))) (eml (eml 1 1) 1) =
      -Complex.exp (Complex.exp 1) := by
    rw [hstep2, emlLn_eq_log]
    have h4 : eml (eml 1 1) 1 = Complex.exp (Complex.exp 1) := by
      simp [eml, lowerLog_one]
    rw [h4]
    unfold eml
    rw [Complex.exp_log hne_neg, lowerLog_exp_of_im_zero he1_im]
    ring
  rw [hstep3]
  unfold eml
  have hneg_ee : -Real.exp (Real.exp 1) < 0 := by
    linarith [Real.exp_pos (Real.exp 1)]
  have hcast_ee : -Complex.exp (Complex.exp (1 : ℂ)) = ((-Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  rw [hcast_ee, lowerLog_ofReal_neg hneg_ee, neg_neg, Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  congr 2
  ring

/-- K = 25 word `11111111EEE1EE11EE1EEE1EE` (`0x1fe2644`, `ln 2` without `ln 0`). -/
def bits_ln2 : List Bool :=
  [true, true, true, true, true, true, true, true, false, false, false, true, false, false,
   true, true, false, false, true, false, false, false, true, false, false]

theorem valid_ln2 : IsValidProgram bits_ln2 := rfl

theorem evalRpn_ln2 :
    evalRpn (1 : ℂ) eml bits_ln2 [] = some [Complex.log 2] := by
  change some [emlLn cTwo] = some [Complex.log 2]
  rw [cTwo_eq_two, emlLn_eq_log]

/-- K = 29 word `11111111EEE1EE11EEE1EE11EE1EE` (`0x1fe26264`, `3` without `ln 0`). -/
def bits_three : List Bool :=
  [true, true, true, true, true, true, true, true, false, false, false, true, false, false,
   true, true, false, false, false, true, false, false, true, true, false, false, true, false, false]

theorem valid_three : IsValidProgram bits_three := rfl

theorem evalRpn_three :
    evalRpn (1 : ℂ) eml bits_three [] = some [3] := by
  change some [eml 1 (eml (eml (emlLn (eml (emlLn (eml 1 (eml 1 1))) (eml 1 1))) (eml 1 1)) 1)] =
    some [3]
  have h1 : eml 1 (eml 1 1) = Complex.exp 1 - 1 := append0xc_eq 1
  rw [h1, emlLn_exp_one_sub_one]
  have hpos1 : (0 : ℝ) < Real.exp 1 - 1 := by linarith [exp_one_gt_one]
  have hpos2 : (0 : ℝ) < Real.exp 1 - 2 := by linarith [exp_one_gt_two]
  have hmid1 : eml ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) (eml 1 1) = Complex.exp 1 - 2 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp),
      ← Complex.ofReal_exp, Real.exp_log hpos1, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hmid1, emlLn_exp_one_sub_two]
  have hmid2 : eml ((Real.log (Real.exp 1 - 2) : ℝ) : ℂ) (eml 1 1) = Complex.exp 1 - 3 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp),
      ← Complex.ofReal_exp, Real.exp_log hpos2, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hmid2]
  unfold eml
  rw [lowerLog_one, sub_zero]
  have him : (Complex.exp (1 : ℂ) - 3).im = 0 := by simp [Complex.exp_im]
  rw [lowerLog_exp_of_im_zero him]
  congr 2
  ring

/-- K = 39 word `1111111111EEE1EE11EEE1EE11EEE1EE11EE1EE` (`4` without `ln 0`). -/
def bits_four : List Bool :=
  [true, true, true, true, true, true, true, true, true, true,
   false, false, false, true, false, false, true, true, false, false, false, true, false, false,
   true, true, false, false, false, true, false, false, true, true, false, false, true, false, false]

theorem valid_four : IsValidProgram bits_four := rfl

theorem evalRpn_four :
    evalRpn (1 : ℂ) eml bits_four [] = some [4] := by
  change some [eml 1 (eml (eml (emlLn (eml (emlLn (eml (emlLn (eml 1 (eml 1 1))) (eml 1 1)))
    (eml 1 1))) (eml 1 1)) 1)] = some [4]
  have h1 : eml 1 (eml 1 1) = Complex.exp 1 - 1 := append0xc_eq 1
  rw [h1, emlLn_exp_one_sub_one]
  have hpos1 : (0 : ℝ) < Real.exp 1 - 1 := by linarith [exp_one_gt_one]
  have hpos2 : (0 : ℝ) < Real.exp 1 - 2 := by linarith [exp_one_gt_two]
  have hmid1 : eml ((Real.log (Real.exp 1 - 1) : ℝ) : ℂ) (eml 1 1) = Complex.exp 1 - 2 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp),
      ← Complex.ofReal_exp, Real.exp_log hpos1, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hmid1, emlLn_exp_one_sub_two]
  have hmid2 : eml ((Real.log (Real.exp 1 - 2) : ℝ) : ℂ) (eml 1 1) = Complex.exp 1 - 3 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp),
      ← Complex.ofReal_exp, Real.exp_log hpos2, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  rw [hmid2, emlLn_eq_log]
  have hlt3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hne3 : Complex.exp (1 : ℂ) - 3 ≠ 0 := by
    have hcast : Complex.exp (1 : ℂ) - 3 = ((Real.exp 1 - 3 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp]; push_cast; rfl
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hmid3 : eml (Complex.log (Complex.exp 1 - 3)) (eml 1 1) = Complex.exp 1 - 4 := by
    unfold eml
    rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero (by simp), Complex.exp_log hne3]
    ring
  rw [hmid3]
  unfold eml
  rw [lowerLog_one, sub_zero]
  have him : (Complex.exp (1 : ℂ) - 4).im = 0 := by simp [Complex.exp_im]
  rw [lowerLog_exp_of_im_zero him]
  congr 2
  ring

/-- K = 35 word `11111111EEE1EE11EE1EEE11E1E1EEE11EE` (`-3` without `ln 0`). -/
def bits_negThree : List Bool :=
  [true, true] ++ bits_two ++
  [false, true, true, false, true, false, true, false, false, false, true, true, false, false]

theorem valid_negThree : IsValidProgram bits_negThree := rfl

theorem evalRpn_negThree :
    evalRpn (1 : ℂ) eml bits_negThree [] = some [-3] := by
  unfold bits_negThree
  change some [append0xc (eml 1 (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)))] = some [-3]
  rw [cTwo_eq_two, append0xc_eq]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h12 : eml 1 2 = Complex.exp 1 - (Real.log 2 : ℂ) := by
    unfold eml
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_pos h2pos]
  have htree : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  rw [h12, htree]
  have hmid : eml (Complex.exp 1 - (Real.log 2 : ℂ)) (Complex.exp (Complex.exp (Complex.exp 1))) =
      -((1 : ℂ) / 2) * Complex.exp (Complex.exp 1) := by
    unfold eml
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log h2pos, lowerLog_exp_of_im_zero hee_im]
    push_cast; ring
  rw [hmid]
  have hneg : -(Real.exp (Real.exp 1) / 2) < 0 := by linarith [Real.exp_pos (Real.exp 1)]
  have hcast : -((1 : ℂ) / 2) * Complex.exp (Complex.exp 1) =
      ((-(Real.exp (Real.exp 1) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; ring
  unfold eml
  rw [hcast, lowerLog_ofReal_neg hneg, neg_neg,
    Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have harg : ((Real.exp 1 : ℝ) : ℂ) - (((Real.exp 1 - Real.log 2 : ℝ) : ℂ) - Real.pi * Complex.I) =
      (Real.log 2 : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_log h2pos]
  congr 2
  push_cast; ring

/-- K = 39 word `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE1E` (`2/3` without `ln 0`). -/
def bits_twoThirds : List Bool :=
  [true, true, true, false, true] ++ bits_two ++
  [false, true, true, false, true, false, true, false, false, true, false, false, false, true, false]

theorem valid_twoThirds : IsValidProgram bits_twoThirds := rfl

theorem evalRpn_twoThirds :
    evalRpn (1 : ℂ) eml bits_twoThirds [] = some [(2 : ℂ) / 3] := by
  unfold bits_twoThirds
  change some [eml (eml 1 (eml (eml 1 1)
    (eml (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)) 1))) 1] = some [(2 : ℂ) / 3]
  rw [cTwo_eq_two]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h12 : eml 1 2 = Complex.exp 1 - (Real.log 2 : ℂ) := by
    unfold eml
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_pos h2pos]
  have htree : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  rw [h12, htree]
  have hmid : eml (Complex.exp 1 - (Real.log 2 : ℂ)) (Complex.exp (Complex.exp (Complex.exp 1))) =
      -((1 : ℂ) / 2) * Complex.exp (Complex.exp 1) := by
    unfold eml
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log h2pos, lowerLog_exp_of_im_zero hee_im]
    push_cast; ring
  rw [hmid]
  have hmid_im : (-((1 : ℂ) / 2) * Complex.exp (Complex.exp 1)).im = 0 := by
    simp [hee_im]
  have hstep : eml (eml 1 1) (eml (-((1 : ℂ) / 2) * Complex.exp (Complex.exp 1)) 1) =
      ((3 : ℝ) / 2 : ℂ) * Complex.exp (Complex.exp 1) := by
    unfold eml
    rw [lowerLog_one, sub_zero, sub_zero, lowerLog_exp_of_im_zero hmid_im]
    push_cast; ring
  rw [hstep]
  have h32_pos : (0 : ℝ) < (3 / 2) * Real.exp (Real.exp 1) := by positivity
  have h32_cast : ((3 : ℝ) / 2 : ℂ) * Complex.exp (Complex.exp 1) =
      (((3 / 2) * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [lowerLog_one, sub_zero, h32_cast, lowerLog_ofReal_pos h32_pos,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - ((Real.log (3 / 2) + Real.exp 1 : ℝ) : ℂ) =
      ((-Real.log (3 / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  congr 2
  push_cast; ring

/-- K = 41 word `111E1111111EEE1EE11EE1EEE11E1E1EE1EEE11EE` (`-1/3` without `ln 0`).
    Obtained by replacing the final `1E` (`exp`) of `2/3` with `11EE` (`0xc`, `exp - 1`). -/
def bits_negThird : List Bool :=
  [true, true, true, false, true] ++ bits_two ++
  [false, true, true, false, true, false, true, false, false, true, false, false, false,
   true, true, false, false]

theorem valid_negThird : IsValidProgram bits_negThird := rfl

theorem evalRpn_negThird :
    evalRpn (1 : ℂ) eml bits_negThird [] = some [-(1 : ℂ) / 3] := by
  unfold bits_negThird
  change some [append0xc (eml 1 (eml (eml 1 1)
    (eml (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)) 1)))] = some [-(1 : ℂ) / 3]
  have h23 : eml (eml 1 (eml (eml 1 1)
      (eml (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)) 1))) 1 = (2 : ℂ) / 3 := by
    have h := evalRpn_twoThirds
    unfold bits_twoThirds at h
    change some [eml (eml 1 (eml (eml 1 1)
      (eml (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)) 1))) 1] = some [(2 : ℂ) / 3] at h
    injection h with hcons; injection hcons
  rw [append0xc_eq]
  have hexp : Complex.exp (eml 1 (eml (eml 1 1)
      (eml (eml (eml 1 cTwo) (eml (eml (eml 1 1) 1) 1)) 1))) = (2 : ℂ) / 3 := by
    simpa [eml, lowerLog_one] using h23
  rw [hexp]
  congr 2
  ring

/-- `cNegOneStrict` as the K = 17 `ln 0`-free word `11111EEE1EE11E1EE`. -/
noncomputable def cNegOneStrict : ℂ :=
  eml (emlLn (eml 1 (eml 1 1))) (eml (eml 1 1) 1)

theorem cNegOneStrict_eq : cNegOneStrict = -1 := by
  have h := evalRpn_negOne_strict
  change some [cNegOneStrict] = some [-1] at h
  injection h with hcons; injection hcons

/-- K = 31 word `111E111111EEE1EE11E1EEE1E1EEE1E` (`1/2-strict`, without `ln 0`). -/
def bits_half_strict : List Bool :=
  [true, true, true, false, true] ++ bits_negOne_strict ++
  [false, true, false, true, false, false, false, true, false]

theorem valid_half_strict : IsValidProgram bits_half_strict := rfl

theorem evalRpn_half_strict :
    evalRpn (1 : ℂ) eml bits_half_strict [] = some [(1 : ℂ) / 2] := by
  unfold bits_half_strict
  change some [eml (eml 1 (eml (eml 1 1) (eml (eml (eml 1 cNegOneStrict) 1) 1))) 1] =
    some [(1 : ℂ) / 2]
  rw [cNegOneStrict_eq]
  have h1m1 : eml 1 (-1) = Complex.exp 1 + Real.pi * Complex.I := by
    unfold eml
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
    simp
  rw [h1m1]
  have hnegee : eml (Complex.exp 1 + Real.pi * Complex.I) 1 = -Complex.exp (Complex.exp 1) := by
    unfold eml
    rw [lowerLog_one, sub_zero, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hnegee]
  have hee_im : (-Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [Complex.neg_im, ← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
      Complex.ofReal_im, neg_zero]
  have h2ee : eml (eml 1 1) (eml (-Complex.exp (Complex.exp 1)) 1) =
      2 * Complex.exp (Complex.exp 1) := by
    unfold eml
    rw [lowerLog_one, sub_zero, sub_zero, lowerLog_exp_of_im_zero hee_im]
    ring
  rw [h2ee]
  have h2ee_pos : (0 : ℝ) < 2 * Real.exp (Real.exp 1) := by positivity
  have h2ee_cast : (2 : ℂ) * Complex.exp (Complex.exp 1) = ((2 * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [lowerLog_one, sub_zero, h2ee_cast, lowerLog_ofReal_pos h2ee_pos,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - ((Real.log 2 + Real.exp 1 : ℝ) : ℂ) = ((-Real.log 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  congr 2; push_cast; ring

/-- K = 31 word `1111111EEE1EE11E1EEE11E1E1EEE1E` (`-1/2-strict`, without `ln 0`). -/
def bits_negHalf_strict : List Bool :=
  [true, true] ++ bits_negOne_strict ++
  [false, true, true, false, true, false, true, false, false, false, true, false]

theorem valid_negHalf_strict : IsValidProgram bits_negHalf_strict := rfl

theorem evalRpn_negHalf_strict :
    evalRpn (1 : ℂ) eml bits_negHalf_strict [] = some [-(1 : ℂ) / 2] := by
  unfold bits_negHalf_strict
  change some [eml (eml 1 (eml (eml 1 cNegOneStrict) (eml (eml (eml 1 1) 1) 1))) 1] =
    some [-(1 : ℂ) / 2]
  rw [cNegOneStrict_eq]
  have h1m1 : eml 1 (-1) = Complex.exp 1 + Real.pi * Complex.I := by
    unfold eml
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
    simp
  have htree : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  rw [h1m1, htree]
  have hmid : eml (Complex.exp 1 + Real.pi * Complex.I) (Complex.exp (Complex.exp (Complex.exp 1))) =
      -(2 * Complex.exp (Complex.exp 1)) := by
    unfold eml
    rw [Complex.exp_add, Complex.exp_pi_mul_I, lowerLog_exp_of_im_zero hee_im]
    ring
  rw [hmid]
  have hneg_pos : -(2 * Real.exp (Real.exp 1)) < 0 := by linarith [Real.exp_pos (Real.exp 1)]
  have hcast : -(2 * Complex.exp (Complex.exp 1)) = ((-(2 * Real.exp (Real.exp 1)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [lowerLog_one, sub_zero, hcast, lowerLog_ofReal_neg hneg_pos, neg_neg,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - (((Real.log 2 + Real.exp 1 : ℝ) : ℂ) - Real.pi * Complex.I) =
      ((-Real.log 2 : ℝ) : ℂ) + Real.pi * Complex.I := by
    push_cast; ring
  rw [hsub, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by norm_num)]
  congr 2; push_cast; ring

/-- K = 31 word `1111111E1E1EEE1EE11E1E1EE1EEE1E` (`1/2-alt`, without `ln 0`). -/
def bits_half_alt : List Bool :=
  [true, true, true, true, true, true, true, false, true, false, true, false, false, false, true,
   false, false, true, true, false, true, false, true, false, false, true, false, false, false,
   true, false]

theorem valid_half_alt : IsValidProgram bits_half_alt := rfl

theorem evalRpn_half_alt :
    evalRpn (1 : ℂ) eml bits_half_alt [] = some [(1 : ℂ) / 2] := by
  change some [eml (eml 1 (eml 1 (eml (eml (emlLn (eml 1 (eml (eml (eml 1 1) 1) 1)))
    (eml (eml (eml 1 1) 1) 1)) 1))) 1] = some [(1 : ℂ) / 2]
  have htree : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  rw [htree]
  have hstep1 : eml 1 (Complex.exp (Complex.exp (Complex.exp 1))) =
      Complex.exp 1 - Complex.exp (Complex.exp 1) := by
    unfold eml; rw [lowerLog_exp_of_im_zero hee_im]
  have hne_neg : Complex.exp (1 : ℂ) - Complex.exp (Complex.exp 1) ≠ 0 := by
    have hcast : Complex.exp (1 : ℂ) - Complex.exp (Complex.exp 1) =
        ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
    rw [hcast]; exact Complex.ofReal_ne_zero.mpr (by linarith [exp_exp_one_gt_exp_one])
  rw [hstep1, emlLn_eq_log]
  have hstep2 : eml (Complex.log (Complex.exp 1 - Complex.exp (Complex.exp 1)))
      (Complex.exp (Complex.exp (Complex.exp 1))) =
      Complex.exp 1 - 2 * Complex.exp (Complex.exp 1) := by
    unfold eml; rw [Complex.exp_log hne_neg, lowerLog_exp_of_im_zero hee_im]; ring
  rw [hstep2]
  have hstep2_im : (Complex.exp (1 : ℂ) - 2 * Complex.exp (Complex.exp 1)).im = 0 := by
    have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
    simp [he1_im, hee_im]
  have hstep3 : eml 1 (eml (Complex.exp 1 - 2 * Complex.exp (Complex.exp 1)) 1) =
      2 * Complex.exp (Complex.exp 1) := by
    unfold eml; rw [lowerLog_one, sub_zero, lowerLog_exp_of_im_zero hstep2_im]; ring
  rw [hstep3]
  have h2ee_pos : (0 : ℝ) < 2 * Real.exp (Real.exp 1) := by positivity
  have h2ee_cast : (2 : ℂ) * Complex.exp (Complex.exp 1) = ((2 * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [lowerLog_one, sub_zero, h2ee_cast, lowerLog_ofReal_pos h2ee_pos,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - ((Real.log 2 + Real.exp 1 : ℝ) : ℂ) = ((-Real.log 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  congr 2; push_cast; ring

/-- K = 37 word `111E111111EEE1EE11E1EEE11E1E1EE1EEE1E` (`1/3-strict`, without `ln 0`). -/
def bits_third_strict : List Bool :=
  [true, true, true, false, true] ++ bits_negOne_strict ++
  [false, true, true, false, true, false, true, false, false, true, false, false, false, true, false]

theorem valid_third_strict : IsValidProgram bits_third_strict := rfl

theorem evalRpn_third_strict :
    evalRpn (1 : ℂ) eml bits_third_strict [] = some [(1 : ℂ) / 3] := by
  unfold bits_third_strict
  change some [eml (eml 1 (eml (eml 1 1)
    (eml (eml (eml 1 cNegOneStrict) (eml (eml (eml 1 1) 1) 1)) 1))) 1] = some [(1 : ℂ) / 3]
  rw [cNegOneStrict_eq]
  have h1m1 : eml 1 (-1) = Complex.exp 1 + Real.pi * Complex.I := by
    unfold eml
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_neg (by norm_num)]
    simp
  have htree : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  rw [h1m1, htree]
  have hmid : eml (Complex.exp 1 + Real.pi * Complex.I) (Complex.exp (Complex.exp (Complex.exp 1))) =
      -(2 * Complex.exp (Complex.exp 1)) := by
    unfold eml; rw [Complex.exp_add, Complex.exp_pi_mul_I, lowerLog_exp_of_im_zero hee_im]; ring
  rw [hmid]
  have hmid_im : (-(2 * Complex.exp (Complex.exp (1 : ℂ)))).im = 0 := by simp [hee_im]
  have h3ee : eml (eml 1 1) (eml (-(2 * Complex.exp (Complex.exp 1))) 1) =
      3 * Complex.exp (Complex.exp 1) := by
    unfold eml; rw [lowerLog_one, sub_zero, sub_zero, lowerLog_exp_of_im_zero hmid_im]; ring
  rw [h3ee]
  have h3ee_pos : (0 : ℝ) < 3 * Real.exp (Real.exp 1) := by positivity
  have h3ee_cast : (3 : ℂ) * Complex.exp (Complex.exp 1) = ((3 * Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  unfold eml
  rw [lowerLog_one, sub_zero, h3ee_cast, lowerLog_ofReal_pos h3ee_pos,
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hsub : ((Real.exp 1 : ℝ) : ℂ) - ((Real.log 3 + Real.exp 1 : ℝ) : ℂ) = ((-Real.log 3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsub, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log (by norm_num)]
  congr 2; push_cast; ring

/-- K = 61 word `111111111EEE1EE11EE1EEEE1EE111111111EEE1EE11EE1EEE1EEE1EE1E1E`
    (`√2 = 2^(1/2)`, without `ln 0`). -/
def bits_sqrt2 : List Bool :=
  [true, true, true] ++ bits_two ++
  [false, false, true, false, false, true] ++ bits_ln2 ++
  [false, true, false, false, true, false, true, false]

theorem valid_sqrt2 : IsValidProgram bits_sqrt2 := rfl

theorem evalRpn_sqrt2 :
    evalRpn (1 : ℂ) eml bits_sqrt2 [] = some [(Real.sqrt 2 : ℂ)] := by
  unfold bits_sqrt2
  have h2_st : ∀ st, evalRpn (1 : ℂ) eml bits_two st = some (2 :: st) := by
    intro st
    have := Eml.TreeBijection.evalRpn_toRpn (1 : ℂ) eml
      (Eml.TreeBijection.fromRpn bits_two valid_two) st
    rw [Eml.TreeBijection.toRpn_fromRpn] at this
    have h0 := Eml.TreeBijection.evalRpn_toRpn (1 : ℂ) eml
      (Eml.TreeBijection.fromRpn bits_two valid_two) []
    rw [Eml.TreeBijection.toRpn_fromRpn, evalRpn_two] at h0
    injection h0 with hcons; injection hcons with hv
    rwa [← hv] at this
  have hln2_st : ∀ st, evalRpn (1 : ℂ) eml bits_ln2 st = some (Complex.log 2 :: st) := by
    intro st
    have := Eml.TreeBijection.evalRpn_toRpn (1 : ℂ) eml
      (Eml.TreeBijection.fromRpn bits_ln2 valid_ln2) st
    rw [Eml.TreeBijection.toRpn_fromRpn] at this
    have h0 := Eml.TreeBijection.evalRpn_toRpn (1 : ℂ) eml
      (Eml.TreeBijection.fromRpn bits_ln2 valid_ln2) []
    rw [Eml.TreeBijection.toRpn_fromRpn, evalRpn_ln2] at h0
    injection h0 with hcons; injection hcons with hv
    rwa [← hv] at this
  have hstep : evalRpn (1 : ℂ) eml
      ([true, true, true] ++ bits_two ++
        [false, false, true, false, false, true] ++ bits_ln2 ++
        [false, true, false, false, true, false, true, false]) [] =
      some [emlExp (Eml.Arithmetic.emlDiv (Complex.log 2) 2)] := by
    simp only [List.append_assoc]
    rw [evalRpn_append]; dsimp only [evalRpn]
    rw [evalRpn_append, h2_st]; dsimp only
    rw [evalRpn_append]; dsimp only [evalRpn]
    rw [evalRpn_append, hln2_st]; dsimp only
    rfl
  rw [hstep, emlExp_eq]
  have hlog2_ne : Complex.log (2 : ℂ) ≠ 0 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have h2_nee : (2 : ℂ) ≠ Complex.exp (Complex.exp 1) := by
    intro h
    have hre : (2 : ℝ) = Real.exp (Real.exp 1) := by
      have := congrArg Complex.re h
      simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
    linarith [exp_one_gt_two, exp_exp_one_gt_exp_one]
  rw [Eml.Arithmetic.emlDiv_eq hlog2_ne two_ne_zero h2_nee]
  congr 2
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hdiv : ((Real.log 2 : ℝ) : ℂ) / ((2 : ℝ) : ℂ) = ((Real.log 2 / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hdiv, ← Complex.ofReal_exp]
  congr 1
  symm
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (le_of_lt (Real.exp_pos _)), sq, ← Real.exp_add]
  rw [show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring, Real.exp_log (by norm_num)]

/-! ### `-iπ` records (K = 47 without `ln 0`, and shared helpers for K = 45 in `Eml.Extended`) -/

/-- The K = 13 subword `11111E1E1EEEE`:
    `A = eml 1 (eml 1 (eml 1 (eml (eml (eml 1 1) 1) 1)))`. -/
def bits_negIpi_A : List Bool :=
  [true, true, true, true, true, false, true, false, true, false, false, false, false]

theorem valid_negIpi_A : IsValidProgram bits_negIpi_A := rfl

/-- Value of `bits_negIpi_A`: `eml 1 (eml 1 (eml 1 (exp (exp 1))))`. -/
noncomputable def cNegIpiA : ℂ :=
  eml 1 (eml 1 (eml 1 (eml (eml (eml 1 1) 1) 1)))

theorem evalRpn_negIpi_A :
    evalRpn (1 : ℂ) eml bits_negIpi_A [] = some [cNegIpiA] := rfl

private theorem exp_exp_one_gt_15 : (15 : ℝ) < Real.exp (Real.exp 1) := by
  have he : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1 : Real.exp (2.718 : ℝ) < Real.exp (Real.exp 1) := Real.exp_lt_exp.mpr he
  -- `Real.exp 2.718 = (exp 1)^2 * exp 0.718 > 2.718^2 * (1 + 0.718 + 0.718^2/2 + 0.718^3/6) > 15.05`
  have h0718 : (1 + 0.718 + 0.718 ^ 2 / 2 + 0.718 ^ 3 / 6 : ℝ) ≤ Real.exp 0.718 := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.718 by norm_num) 4
    simp [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have h2718 : Real.exp 2.718 = Real.exp 1 * Real.exp 1 * Real.exp 0.718 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hsq : (2.718 * 2.718 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith
  nlinarith [Real.exp_pos (0.718 : ℝ)]

private theorem exp_exp_one_lt_16 : Real.exp (Real.exp 1) < (16 : ℝ) := by
  have he : Real.exp 1 < (2.72 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have h1 : Real.exp (Real.exp 1) < Real.exp (2.72 : ℝ) := Real.exp_lt_exp.mpr he
  -- `exp 2.72 = exp 1 * exp 1 * exp 0.72`; `exp 0.72 = (exp (-0.72))⁻¹`
  -- Use `exp 0.72 ≤ 1 / (1 - 0.72)`? Too loose; use `exp (0.36) < 1 / (1 - 0.36)`? Still loose.
  -- `Real.exp_bound` on `x = 0.72` with `n = 4`:
  have h072 : Real.exp (0.72 : ℝ) < 2.06 := by
    have hb := Real.exp_bound (x := (0.72 : ℝ)) (by norm_num) (n := 5) (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial, abs_le] at hb
    linarith
  have h272 : Real.exp 2.72 = Real.exp 1 * Real.exp 1 * Real.exp 0.72 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he_lt : Real.exp 1 < (2.7183 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith [Real.exp_pos (0.72 : ℝ)]

/-- Key algebraic form of `exp cNegIpiA`:
    `exp cNegIpiA = exp(e) / (u + iπ)` where `u = e - ln(e^e - e)`. -/
theorem exp_cNegIpiA_eq :
    let u : ℝ := Real.exp 1 - Real.log (Real.exp (Real.exp 1) - Real.exp 1)
    Complex.exp cNegIpiA = ((Real.exp (Real.exp 1) : ℝ) : ℂ) / ((u : ℂ) + (Real.pi : ℂ) * Complex.I) := by
  intro u
  have hdiff_pos : (0 : ℝ) < Real.exp (Real.exp 1) - Real.exp 1 := by
    linarith [exp_exp_one_gt_15, Real.exp_one_lt_d9]
  have hstep1 : eml (eml (eml 1 1) 1) 1 = Complex.exp (Complex.exp (Complex.exp 1)) := by
    simp [eml, lowerLog_one]
  have hstep2 : eml 1 (Complex.exp (Complex.exp (Complex.exp 1))) =
      ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    unfold eml
    have him : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
    rw [lowerLog_exp_of_im_zero him]
    simp [← Complex.ofReal_one, ← Complex.ofReal_exp]
  have hstep3 : eml 1 ((Real.exp 1 - Real.exp (Real.exp 1) : ℝ) : ℂ) =
      (u : ℂ) + (Real.pi : ℂ) * Complex.I := by
    unfold eml
    rw [lowerLog_ofReal_neg (by linarith)]
    have hneg : -(Real.exp 1 - Real.exp (Real.exp 1)) = Real.exp (Real.exp 1) - Real.exp 1 := by ring
    rw [hneg]
    simp only [u, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    push_cast; ring
  have hw_ne : (u : ℂ) + (Real.pi : ℂ) * Complex.I ≠ 0 := by
    intro h
    have him : ((u : ℂ) + (Real.pi : ℂ) * Complex.I).im = 0 := by rw [h]; simp
    simp at him
  have hw_not_neg : ¬ isNegReal ((u : ℂ) + (Real.pi : ℂ) * Complex.I) := by
    intro ⟨_, him⟩
    simp at him
  have hA : cNegIpiA = Complex.exp 1 - Complex.log ((u : ℂ) + (Real.pi : ℂ) * Complex.I) := by
    unfold cNegIpiA
    rw [hstep1, hstep2, hstep3]
    unfold eml
    rw [lowerLog_eq_log_of_not_isNegReal hw_not_neg]
  rw [hA, Complex.exp_sub, Complex.exp_log hw_ne]
  simp [← Complex.ofReal_one, ← Complex.ofReal_exp]

/-- Bounds on `Re(exp cNegIpiA)` and `Im(exp cNegIpiA)`:
    `-2π < Im(exp cNegIpiA) < -π` and `0 < Re(exp cNegIpiA) < 1`. -/
theorem cNegIpiA_exp_bounds :
    -2 * Real.pi < (Complex.exp cNegIpiA).im ∧
    (Complex.exp cNegIpiA).im < -Real.pi ∧
    0 < (Complex.exp cNegIpiA).re ∧
    (Complex.exp cNegIpiA).re < 1 := by
  set E : ℝ := Real.exp (Real.exp 1)
  set u : ℝ := Real.exp 1 - Real.log (E - Real.exp 1)
  have hE_gt : (15 : ℝ) < E := exp_exp_one_gt_15
  have hE_lt : E < (16 : ℝ) := exp_exp_one_lt_16
  have he_gt : (2.718 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he_lt : Real.exp 1 < (2.7183 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hdiff_gt : (12.2 : ℝ) < E - Real.exp 1 := by linarith
  have hdiff_lt : E - Real.exp 1 < (13.3 : ℝ) := by linarith
  -- `2.4 < ln(E - e) < 2.718` (since `exp 2.4 < 12.2` and `exp 2.718 > 15 > 13.3`)
  have hlog_gt : (2.4 : ℝ) < Real.log (E - Real.exp 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have h04 : Real.exp (0.4 : ℝ) < 1.55 := by
      have hb := Real.exp_bound (x := (0.4 : ℝ)) (by norm_num) (n := 4) (by norm_num)
      simp [Finset.sum_range_succ, Nat.factorial, abs_le] at hb
      linarith
    have h24 : Real.exp 2.4 = Real.exp 1 * Real.exp 1 * Real.exp 0.4 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (0.4 : ℝ)]
  have hlog_lt : Real.log (E - Real.exp 1) < Real.exp 1 := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]
    linarith
  have hu_pos : (0 : ℝ) < u := by linarith
  have hu_lt : u < (0.35 : ℝ) := by linarith
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_lt : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hden_pos : (0 : ℝ) < u ^ 2 + Real.pi ^ 2 := by positivity
  have hden_gt : (9.85 : ℝ) < u ^ 2 + Real.pi ^ 2 := by nlinarith
  have hden_lt : u ^ 2 + Real.pi ^ 2 < (10.06 : ℝ) := by nlinarith
  have hA_eq : Complex.exp cNegIpiA = (E : ℂ) / ((u : ℂ) + (Real.pi : ℂ) * Complex.I) :=
    exp_cNegIpiA_eq
  have hre_eq : (Complex.exp cNegIpiA).re = E * u / (u ^ 2 + Real.pi ^ 2) := by
    rw [hA_eq]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, sq]
    ring
  have him_eq : (Complex.exp cNegIpiA).im = -(E * Real.pi) / (u ^ 2 + Real.pi ^ 2) := by
    rw [hA_eq]
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply, sq]
    ring
  have hratio_gt : (1 : ℝ) < E / (u ^ 2 + Real.pi ^ 2) := by
    rw [one_lt_div hden_pos]; linarith
  have hratio_lt : E / (u ^ 2 + Real.pi ^ 2) < (1.65 : ℝ) := by
    rw [div_lt_iff₀ hden_pos]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [him_eq, show -(E * Real.pi) / (u ^ 2 + Real.pi ^ 2) = -(E / (u ^ 2 + Real.pi ^ 2)) * Real.pi by ring]
    nlinarith [Real.pi_pos]
  · rw [him_eq, show -(E * Real.pi) / (u ^ 2 + Real.pi ^ 2) = -(E / (u ^ 2 + Real.pi ^ 2)) * Real.pi by ring]
    nlinarith [Real.pi_pos]
  · rw [hre_eq]; positivity
  · rw [hre_eq, show E * u / (u ^ 2 + Real.pi ^ 2) = (E / (u ^ 2 + Real.pi ^ 2)) * u by ring]
    nlinarith

/-- `0 < Im(exp(exp cNegIpiA)) < π`, so `exp(exp cNegIpiA)` lies strictly in the lower-cut strip
    and `e - exp(exp cNegIpiA) ≠ 0`. -/
theorem cNegIpiA_exp_exp_im_bounds :
    0 < (Complex.exp (Complex.exp cNegIpiA)).im ∧
    (Complex.exp (Complex.exp cNegIpiA)).im < Real.pi := by
  obtain ⟨h1, h2, hre0, hre1⟩ := cNegIpiA_exp_bounds
  rw [Complex.exp_im]
  have hsin_pos : 0 < Real.sin (Complex.exp cNegIpiA).im := by
    have hshift : Real.sin (Complex.exp cNegIpiA).im = Real.sin ((Complex.exp cNegIpiA).im + 2 * Real.pi) :=
      (Real.sin_add_two_pi _).symm
    rw [hshift]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin_le : Real.sin (Complex.exp cNegIpiA).im ≤ 1 := Real.sin_le_one _
  constructor
  · exact mul_pos (Real.exp_pos _) hsin_pos
  · have hexp_lt : Real.exp (Complex.exp cNegIpiA).re < Real.exp 1 := Real.exp_lt_exp.mpr hre1
    have hexp_lt_pi : Real.exp 1 < Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_d2]
    nlinarith [Real.exp_pos (Complex.exp cNegIpiA).re]

/-- Core `-iπ` identity shared by both `-ipi` (K = 45) and `-ipi-strict` (K = 47):
    `eml cNegIpiA (-exp (exp cNegIpiA)) = -iπ`. -/
theorem eml_cNegIpiA_neg_exp_exp :
    eml cNegIpiA (-Complex.exp (Complex.exp cNegIpiA)) = -(Real.pi * Complex.I) := by
  obtain ⟨h1, h2, _, _⟩ := cNegIpiA_exp_bounds
  unfold eml
  have hneg_eq : -Complex.exp (Complex.exp cNegIpiA) =
      Complex.exp (Complex.exp cNegIpiA + Real.pi * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [hneg_eq, lowerLog_exp]
  · ring
  · simp; linarith
  · simp; linarith

/-- K = 47 `ln 0`-free word for `-iπ` on the lower cut (`-ipi-strict` in `best-known.json`):
    `11111E1E1EEEE11111111E1E1EEEE1E1E1EEE1EE11E1EEE`. -/
def bits_negIpi_strict : List Bool :=
  bits_negIpi_A ++ [true, true, true] ++ bits_negIpi_A ++
    [true, false, true, false, true, false, false, false, true, false, false, true, true, false,
     true, false, false, false]

theorem evalRpn_negIpi_strict :
    evalRpn (1 : ℂ) eml bits_negIpi_strict [] = some [-(Real.pi * Complex.I)] := by
  unfold bits_negIpi_strict
  have hA_st : ∀ st, evalRpn (1 : ℂ) eml bits_negIpi_A st = some (cNegIpiA :: st) := fun _ => rfl
  have hstep : evalRpn (1 : ℂ) eml
      (bits_negIpi_A ++ [true, true, true] ++ bits_negIpi_A ++
        [true, false, true, false, true, false, false, false, true, false, false, true, true, false,
         true, false, false, false]) [] =
      some [eml cNegIpiA
        (eml (emlLn (eml 1 (emlExp (emlExp (emlExp cNegIpiA))))) (emlExp (eml 1 1)))] := by
    simp only [List.append_assoc]
    rw [evalRpn_append, hA_st]; dsimp only
    rw [evalRpn_append]; dsimp only [evalRpn]
    rw [evalRpn_append, hA_st]; dsimp only
    rfl
  rw [hstep]
  obtain ⟨him0, himpi⟩ := cNegIpiA_exp_exp_im_bounds
  have h1 : eml 1 (emlExp (emlExp (emlExp cNegIpiA))) =
      Complex.exp 1 - Complex.exp (Complex.exp cNegIpiA) := by
    rw [emlExp_eq, emlExp_eq, emlExp_eq]
    unfold eml
    rw [lowerLog_exp (by linarith [Real.pi_pos]) himpi]
  have hne : Complex.exp 1 - Complex.exp (Complex.exp cNegIpiA) ≠ 0 := by
    intro h
    have him : (Complex.exp 1 - Complex.exp (Complex.exp cNegIpiA)).im = 0 := by rw [h]; simp
    have he_im : (Complex.exp (1 : ℂ)).im = 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_exp, Complex.ofReal_im]
    simp [he_im] at him
    linarith
  have h2 : eml (emlLn (Complex.exp 1 - Complex.exp (Complex.exp cNegIpiA))) (emlExp (eml 1 1)) =
      -Complex.exp (Complex.exp cNegIpiA) := by
    rw [emlLn_eq_log, emlExp_eq, show eml 1 1 = Complex.exp 1 from cE_eq_exp_one]
    unfold eml
    rw [Complex.exp_log hne, lowerLog_exp_of_im_zero (by rw [← Complex.ofReal_one, ← Complex.ofReal_exp, Complex.ofReal_im])]
    ring
  rw [h1, h2, eml_cNegIpiA_neg_exp_exp]

end Eml.Records
