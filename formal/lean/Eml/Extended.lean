/-
  Machine-checked Lean 4 + Mathlib formalization of the phase-free extended
  EML domain (`ℂ ∪ {+∞, -∞, NaN}`) as an honest concrete inductive type `EmlExt`
  (zero custom axioms, zero inconsistency — replacing the earlier unsound
  axiomatic `EmlExtendedModel` in which `1 = 0` was derivable).

  Semantics follow `docs/rotsub.md`:
    - `ln 0 = -∞`, `ln (+∞) = +∞`
    - `exp (+∞) = +∞`, `exp (-∞) = 0`
    - `u - (-∞) = +∞`, `u - (+∞) = -∞`, `+∞ - u = +∞`, `-∞ - u = -∞`
    - indeterminate forms (`∞ - ∞`, `ln (-∞)`, etc.) evaluate to `nan`

  Proved theorems (zero `sorry`, zero custom axioms):
    - `extRotSub_eq_sub`: for ANY `a, b : ℂ` and any nonzero purely imaginary `c`,
      `extRotSub (finite c) (finite a) (finite b) = finite (a - b)` — covering all
      `ln 0` paths (`κ_L(b) = 0`, `a = 0`, `a = b`, `r1 = 0`, `b = 0`, `x = e^e`).
    - Concrete RPN constant records using `ln 0 = -∞`:
      - `evalRpn_0x7d0`     (K = 11) → `negInf` (`-∞`)
      - `evalRpn_0x7d0c`    (K = 15) → `finite (-1)`
      - `evalRpn_0x1fa1a8`  (K = 21) → `finite (π * I)` (lower cut)
      - `evalRpn_0x1fa1a8c` (K = 25) → `finite (-2)` (lower cut)

  Note: `EmlExt` is the phase-free extended model. Directed infinities (needed
  for `b = 0` on the *scaled* subtraction path `sub(5, 0)` in `docs/rotsub.md`)
  are not modeled here.
-/
import Eml.Basic
import Eml.Binary
import Eml.RotSub

namespace Eml.Extended

open Eml
open Eml.Binary
open Eml.RotSub

/-- Honest concrete inductive type for the phase-free extended complex plane
    used by `eml` with `ln 0 = -∞`. Indeterminate forms map to `nan`. -/
inductive EmlExt where
  | finite (z : ℂ)
  | posInf
  | negInf
  | nan

/-- Extended exponential on `EmlExt`. -/
noncomputable def extExp : EmlExt → EmlExt
  | .finite z => .finite (Complex.exp z)
  | .posInf   => .posInf
  | .negInf   => .finite 0
  | .nan      => .nan

/-- Extended lower-cut logarithm on `EmlExt` (`ln 0 = -∞`, `ln (+∞) = +∞`). -/
noncomputable def extLowerLog : EmlExt → EmlExt
  | .finite z => if z = 0 then .negInf else .finite (lowerLog z)
  | .posInf   => .posInf
  | .negInf   => .nan
  | .nan      => .nan

/-- Extended subtraction on `EmlExt` (indeterminate `∞ - ∞` maps to `nan`). -/
noncomputable def extSub : EmlExt → EmlExt → EmlExt
  | .finite a, .finite b => .finite (a - b)
  | .finite _, .negInf   => .posInf
  | .finite _, .posInf   => .negInf
  | .posInf,   .finite _ => .posInf
  | .negInf,   .finite _ => .negInf
  | _,         _         => .nan

/-- Extended EML operator: `extEml x y = extSub (extExp x) (extLowerLog y)`. -/
noncomputable def extEml (x y : EmlExt) : EmlExt :=
  extSub (extExp x) (extLowerLog y)

/-- `extEml` agrees with `eml` on finite operands whenever `y ≠ 0`. -/
theorem extEml_finite {x y : ℂ} (hy : y ≠ 0) :
    extEml (.finite x) (.finite y) = .finite (eml x y) := by
  simp [extEml, extExp, extLowerLog, extSub, eml, hy]

/-- Extended `exp` word `x1E`: `extEml x 1`. -/
noncomputable def extEmlExp (x : EmlExt) : EmlExt :=
  extEml x (.finite 1)

theorem extEmlExp_eq (x : EmlExt) : extEmlExp x = extExp x := by
  cases x with
  | finite z => simp [extEmlExp, extEml, extExp, extLowerLog, extSub, lowerLog_one]
  | posInf => simp [extEmlExp, extEml, extExp, extLowerLog, extSub, lowerLog_one]
  | negInf => simp [extEmlExp, extEml, extExp, extLowerLog, extSub, lowerLog_one]
  | nan => simp [extEmlExp, extEml, extExp, extLowerLog, extSub, lowerLog_one]

/-- Extended `ln` word `11xE1EE`: `extEml 1 (extEml (extEml 1 x) 1)`. -/
noncomputable def extEmlLn (x : EmlExt) : EmlExt :=
  extEml (.finite 1) (extEml (extEml (.finite 1) x) (.finite 1))

theorem extEmlLn_zero : extEmlLn (.finite 0) = .negInf := by
  simp [extEmlLn, extEml, extExp, extLowerLog, extSub, lowerLog_one]

theorem extEmlLn_finite_ne_zero {x : ℂ} (hx : x ≠ 0) :
    extEmlLn (.finite x) = .finite (Complex.log x) := by
  have h1 : extEml (.finite 1) (.finite x) = .finite (eml 1 x) := extEml_finite hx
  have h2 : extEml (.finite (eml 1 x)) (.finite 1) = .finite (Complex.exp (eml 1 x)) := by
    rw [extEml_finite one_ne_zero, eml, lowerLog_one, sub_zero]
  have hexp_ne : Complex.exp (eml 1 x) ≠ 0 := Complex.exp_ne_zero _
  unfold extEmlLn
  rw [h1, h2, extEml_finite hexp_ne]
  congr 1
  rw [← emlExp_eq (eml 1 x)]
  exact emlLn_eq_log x

/-- Extended `rawSub` word `11xE1EEy1EE`. -/
noncomputable def extRawSub (a b : EmlExt) : EmlExt :=
  extEml (extEmlLn a) (extEmlExp b)

/-- `extRawSub (finite a) (finite b) = finite (a - b + 2πi · κ_L(b))` for ALL `a, b : ℂ`
    (including `a = 0` and `b = 0`). -/
theorem extRawSub_eq (a b : ℂ) :
    extRawSub (.finite a) (.finite b) =
      .finite (a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) := by
  unfold extRawSub
  rw [extEmlExp_eq]
  change extEml (extEmlLn (.finite a)) (.finite (Complex.exp b)) = _
  by_cases ha : a = 0
  · subst ha
    rw [extEmlLn_zero]
    simp [extEml, extExp, extLowerLog, extSub, Complex.exp_ne_zero, lowerLog_exp_eq_sub_unwind]
    ring
  · rw [extEmlLn_finite_ne_zero ha, extEml_finite (Complex.exp_ne_zero b)]
    congr 1
    unfold eml
    rw [Complex.exp_log ha, lowerLog_exp_eq_sub_unwind]
    ring

/-- Extended `mul` word `1111xEE1EEyE1EE1E` (K = 17). -/
noncomputable def extEmlMul (a b : EmlExt) : EmlExt :=
  extEmlExp (extEml (.finite 1) (extEmlExp (extEml (extEmlLn (extEml (.finite 1) a)) b)))

/-- `extEmlMul (finite a) (finite b) = finite (a * b)` for ALL `a ≠ 0` and ALL `b : ℂ`
    (including `b = 0` and `a = exp(exp 1)` via `ln 0 = -∞`, matching `docs/rotsub.md`). -/
theorem extEmlMul_eq {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    extEmlMul (.finite a) (.finite b) = .finite (a * b) := by
  unfold extEmlMul
  rw [extEml_finite ha]
  by_cases hae : eml 1 a = 0
  · rw [hae, extEmlLn_zero]
    by_cases hb : b = 0
    · subst hb
      simp [extEmlExp_eq, extEml, extExp, extLowerLog, extSub]
    · have h1 : extEml .negInf (.finite b) = .finite (-lowerLog b) := by
        simp [extEml, extExp, extLowerLog, extSub, hb]
      rw [h1, extEmlExp_eq, extEmlExp_eq]
      simp only [extExp]
      rw [extEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      have ha_eq : a = Complex.exp (Complex.exp 1) := by
        have hsub : Complex.exp 1 = lowerLog a := sub_eq_zero.mp hae
        rw [← exp_lowerLog ha, ← hsub]
      unfold eml
      rw [lowerLog_exp_eq_sub_unwind]
      set u : ℂ := -lowerLog b
      have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (Complex.exp 1 + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
        exp_lowerLog hb, ha_eq]
  · rw [extEmlLn_finite_ne_zero hae]
    by_cases hb : b = 0
    · subst hb
      simp [extEmlExp_eq, extEml, extExp, extLowerLog, extSub]
    · rw [extEml_finite hb, extEmlExp_eq, extEmlExp_eq]
      simp only [extExp]
      rw [extEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      unfold eml at hae ⊢
      rw [Complex.exp_log hae, lowerLog_exp_eq_sub_unwind]
      set u : ℂ := Complex.exp 1 - lowerLog a - lowerLog b
      have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
        exp_lowerLog ha, exp_lowerLog hb]

/-- Extended `div` word `111yEE1EE1xE1EE1E` (K = 17). -/
noncomputable def extEmlDiv (a b : EmlExt) : EmlExt :=
  extEmlExp (extEml (extEmlLn (extEml (.finite 1) b)) (extEmlExp (extEml (.finite 1) a)))

/-- `extEmlDiv (finite a) (finite b) = finite (a / b)` for ALL `b ≠ 0` and ALL `a : ℂ`
    (including `a = 0` and `b = exp(exp 1)` via `ln 0 = -∞`, matching `docs/rotsub.md`). -/
theorem extEmlDiv_eq (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    extEmlDiv (.finite a) (.finite b) = .finite (a / b) := by
  unfold extEmlDiv
  rw [extEml_finite hb]
  by_cases ha : a = 0
  · subst ha
    have h1a : extEmlExp (extEml (.finite 1) (.finite 0)) = .posInf := by
      simp [extEmlExp_eq, extEml, extExp, extLowerLog, extSub]
    rw [h1a]
    by_cases hbe : eml 1 b = 0
    · rw [hbe, extEmlLn_zero]
      simp [extEmlExp_eq, extEml, extExp, extLowerLog, extSub]
    · rw [extEmlLn_finite_ne_zero hbe]
      simp [extEmlExp_eq, extEml, extExp, extLowerLog, extSub]
  · rw [extEml_finite ha, extEmlExp_eq, extEmlExp_eq]
    simp only [extExp]
    by_cases hbe : eml 1 b = 0
    · rw [hbe, extEmlLn_zero]
      have h1 : extEml .negInf (.finite (Complex.exp (eml 1 a))) =
          .finite (-lowerLog (Complex.exp (eml 1 a))) := by
        simp [extEml, extExp, extLowerLog, extSub, Complex.exp_ne_zero]
      rw [h1]
      dsimp only
      congr 1
      have hb_eq : b = Complex.exp (Complex.exp 1) := by
        have hsub : Complex.exp 1 = lowerLog b := sub_eq_zero.mp hbe
        rw [← exp_lowerLog hb, ← hsub]
      rw [lowerLog_exp_eq_sub_unwind]
      set u : ℂ := eml 1 a
      have hrew : -(u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a - Complex.exp 1) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u, eml]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub,
        exp_lowerLog ha, hb_eq]
    · rw [extEmlLn_finite_ne_zero hbe, extEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      unfold eml at hbe ⊢
      rw [Complex.exp_log hbe, lowerLog_exp_eq_sub_unwind]
      set u : ℂ := Complex.exp 1 - lowerLog a
      have hrew : Complex.exp 1 - lowerLog b - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a - lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub,
        exp_lowerLog ha, exp_lowerLog hb]

/-- Extended rotated subtraction (`docs/rotsub.md`). -/
noncomputable def extRotSub (c a b : EmlExt) : EmlExt :=
  extEmlDiv (extRawSub (extEmlMul c (extRawSub a b)) (extEmlMul c (extRawSub b b))) c

/-- Full rotated subtraction theorem in the phase-free extended model (`docs/rotsub.md`):
    for any nonzero purely imaginary `c` and ANY `a, b : ℂ`,
    `extRotSub (finite c) (finite a) (finite b) = finite (a - b)`.
    Covers every `ln 0` edge case (`κ_L(b) = 0`, `a = 0`, `a = b`, `r1 = 0`, `b = 0`). -/
theorem extRotSub_eq_sub {c : ℂ} (hc_re : c.re = 0) (hc_ne : c ≠ 0) (a b : ℂ) :
    extRotSub (.finite c) (.finite a) (.finite b) = .finite (a - b) := by
  unfold extRotSub
  rw [extRawSub_eq a b, extRawSub_eq b b, sub_self, zero_add]
  rw [extEmlMul_eq hc_ne, extEmlMul_eq hc_ne]
  rw [extRawSub_eq]
  have hm2_im : (c * (2 * Real.pi * Complex.I * (lowerUnwind b : ℂ))).im = 0 :=
    mul_unwind_im_zero hc_re (lowerUnwind b)
  rw [lowerUnwind_of_im_zero hm2_im]
  have hcancel : c * (a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) -
      c * (2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) +
      2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) = c * (a - b) := by
    push_cast; ring
  rw [hcancel, extEmlDiv_eq _ hc_ne, mul_div_cancel_left₀ _ hc_ne]

/-! ### Extended-domain (`ln 0 = -∞`) RPN constant records -/

/-- `0xc` nibble theorem on `EmlExt`. -/
theorem ext_append0xc (x : EmlExt) :
    extEml x (extEml (.finite 1) (.finite 1)) = extSub (extExp x) (.finite 1) := by
  have h1 : extEml (.finite 1) (.finite 1) = .finite (Complex.exp 1) := by
    rw [extEml_finite one_ne_zero]
    congr 1
    exact cE_eq_exp_one
  have h2 : extLowerLog (.finite (Complex.exp 1)) = .finite 1 := by
    simp [extLowerLog, Complex.exp_ne_zero, lowerLog_exp_of_im_zero]
  rw [h1]
  unfold extEml
  rw [h2]

theorem evalRpn_ext_0x74 :
    evalRpn (EmlExt.finite 1) extEml [true, true, true, false, true, false, false] [] =
      some [.finite 0] := by
  change some [extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1))] =
    some [.finite 0]
  rw [extEml_finite one_ne_zero, extEml_finite one_ne_zero,
    extEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
  congr 3
  exact cZero_eq_zero

/-- Binary `0x7d0` (`11111010000₂`, K = 11) → `-∞`. -/
def bits_0x7d0 : List Bool :=
  [true, true, true, true, true, false, true, false, false, false, false]

theorem valid_0x7d0 : IsValidProgram bits_0x7d0 := rfl

theorem evalRpn_0x7d0 :
    evalRpn (EmlExt.finite 1) extEml bits_0x7d0 [] = some [.negInf] := by
  change some [extEml (.finite 1) (extEml (.finite 1)
    (extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1))))] = some [.negInf]
  have h0 : extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1)) = .finite 0 := by
    rw [extEml_finite one_ne_zero, extEml_finite one_ne_zero,
      extEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
    congr 1
    exact cZero_eq_zero
  rw [h0]
  simp [extEml, extExp, extLowerLog, extSub]

/-- Binary `0x7d0c` (`111110100001100₂`, K = 15, proved minimal with `ln 0`) → `-1`. -/
def bits_0x7d0c : List Bool :=
  bits_0x7d0 ++ [true, true, false, false]

theorem valid_0x7d0c : IsValidProgram bits_0x7d0c := rfl

theorem evalRpn_0x7d0c :
    evalRpn (EmlExt.finite 1) extEml bits_0x7d0c [] = some [.finite (-1)] := by
  unfold bits_0x7d0c
  rw [evalRpn_append_0xc (EmlExt.finite 1) extEml bits_0x7d0 .negInf evalRpn_0x7d0]
  rw [ext_append0xc]
  simp [extExp, extSub]

/-- Binary `0x1fa1a8` (`111111010000110101000₂`, K = 21, proved minimal with `ln 0`)
    → `+iπ` on the lower cut. -/
def bits_0x1fa1a8 : List Bool :=
  [true] ++ bits_0x7d0 ++ [true, true, false, true, false, true, false, false, false]

theorem valid_0x1fa1a8 : IsValidProgram bits_0x1fa1a8 := rfl

theorem evalRpn_0x1fa1a8 :
    evalRpn (EmlExt.finite 1) extEml bits_0x1fa1a8 [] = some [.finite (Real.pi * Complex.I)] := by
  unfold bits_0x1fa1a8
  change some [extEml (.finite 1)
    (extEml (extEml (.finite 1) (extEml (.finite 1)
      (extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1)))))
      (extEml (extEml (extEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1)))] =
    some [.finite (Real.pi * Complex.I)]
  have hnegInf : extEml (.finite 1) (extEml (.finite 1)
      (extEml (.finite 1) (extEml (extEml (.finite 1) (.finite 1)) (.finite 1)))) = .negInf := by
    have h := evalRpn_0x7d0
    simpa [bits_0x7d0, evalRpn] using h
  have htree : extEml (extEml (extEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1) =
      .finite (Complex.exp (Complex.exp (Complex.exp 1))) := by
    simp [extEml, extExp, extLowerLog, extSub, lowerLog_one]
  rw [hnegInf, htree]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hinner : extEml .negInf (.finite (Complex.exp (Complex.exp (Complex.exp 1)))) =
      .finite (-Complex.exp (Complex.exp 1)) := by
    simp [extEml, extExp, extLowerLog, extSub, Complex.exp_ne_zero, lowerLog_exp_of_im_zero hee_im]
  rw [hinner]
  have hneg_ee : -Real.exp (Real.exp 1) < 0 := by linarith [Real.exp_pos (Real.exp 1)]
  have hcast_ee : -Complex.exp (Complex.exp (1 : ℂ)) = ((-Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  have hne : -Complex.exp (Complex.exp (1 : ℂ)) ≠ 0 := by
    rw [hcast_ee]; exact Complex.ofReal_ne_zero.mpr (ne_of_lt hneg_ee)
  rw [extEml_finite hne]
  congr 3
  unfold eml
  rw [hcast_ee, lowerLog_ofReal_neg hneg_ee, neg_neg, Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  ring

/-- Binary `0x1fa1a8c` (`1111110100001101010001100₂`, K = 25, proved minimal with `ln 0`)
    → `-2` on the lower cut. -/
def bits_0x1fa1a8c : List Bool :=
  bits_0x1fa1a8 ++ [true, true, false, false]

theorem valid_0x1fa1a8c : IsValidProgram bits_0x1fa1a8c := rfl

theorem evalRpn_0x1fa1a8c :
    evalRpn (EmlExt.finite 1) extEml bits_0x1fa1a8c [] = some [.finite (-2)] := by
  unfold bits_0x1fa1a8c
  rw [evalRpn_append_0xc (EmlExt.finite 1) extEml bits_0x1fa1a8
    (.finite (Real.pi * Complex.I)) evalRpn_0x1fa1a8]
  rw [ext_append0xc]
  simp only [extExp, extSub, Complex.exp_pi_mul_I]
  congr 2
  norm_num

end Eml.Extended
