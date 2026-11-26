/-
  Machine-checked Lean 4 + Mathlib proofs of concrete `ln 0`-free constant
  records over `ℂ` (`lib/eml/best-known.json`, `docs/binary.md`,
  `tools/minimality/decide.py`):
    - `11111EEE1EE11E1EE`            (K = 17)           → `-1`  (proved minimal without `ln 0`)
    - `111111EEE1EE11EE1EE`          (K = 19, `0x7e264`) → `2`  (proved minimal)
    - `111111E1E1EEE1EE11E1EEE`      (K = 23)           → `+iπ` (lower cut, proved minimal without `ln 0`)
    - `11111111EEE1EE11EE1EEE1EE`    (K = 25, `0x1fe2644`) → `ln 2`
    - `11111111EEE1EE11EEE1EE11EE1EE` (K = 29, `0x1fe26264`) → `3`

  Every proof evaluates `evalRpn (1 : ℂ) eml` directly on the exact bitstring.
  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Eml.Basic
import Eml.Binary

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

end Eml.Records
