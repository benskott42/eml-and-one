/-
  Machine-checked Lean 4 end-to-end RPN stack proofs for the extended-domain
  constant records in `best-known.json`:
    - `0x7d0`     (K = 11) → `−∞`
    - `0x7d0c`    (K = 15) → `−1`
    - `0x1fa1a8`  (K = 21) → `+iπ` (lower cut)
    - `0x1fa1a8c` (K = 25) → `−2`  (lower cut)

  Zero `sorry`.
-/
import Eml.Basic
import Eml.Binary
import Eml.RpnSoundness

namespace Eml.Extended

open Eml
open Eml.Binary
open Eml.RpnSoundness

/-- Extended EML model adding `±∞`, `iπ`, `−1`, `−2`, and the extended-domain
    and lower-cut axioms used by the calculator (`ln 0 = −∞`, `exp(−∞) = 0`,
    `ln(−exp(e)) = e − iπ`, `exp(iπ) = −1`). -/
class EmlExtendedModel (α : Type) extends EmlModel α where
  posInf : α
  negInf : α
  ipi : α
  negOne : α
  negTwo : α
  ln_zero : ln zero = negInf
  ln_posInf : ln posInf = posInf
  exp_negInf : exp negInf = zero
  sub_negInf : ∀ x, sub x negInf = posInf
  sub_posInf : ∀ x, sub x posInf = negInf
  sub_zero_one : sub zero one = negOne
  sub_negOne_one : sub negOne one = negTwo
  exp_ipi : exp ipi = negOne
  inStrip_exp_exp_one : inStrip (exp (exp one))
  ln_neg_exp_exp_one : ln (neg (exp (exp one))) = sub (exp one) ipi

section ConstantRecords

variable {α : Type} [X : EmlExtendedModel α]

/-- Binary `0x7d0` (`11111010000₂`, K = 11) = `eml(1, eml(1, 0))` evaluates on the
    RPN stack to `−∞`. -/
def bits_0x7d0 : List Bool :=
  [true, true, true, true, true, false, true, false, false, false, false]

theorem evalRpn_0x7d0 :
    evalRpn X.one (eml (α := α)) bits_0x7d0 [] = some [X.negInf] := by
  change some [eml X.one (eml X.one (cZero (α := α)))] = some [X.negInf]
  rw [cZero_eq_zero]
  unfold eml
  rw [X.ln_zero, X.sub_negInf, X.ln_posInf, X.sub_posInf]

/-- Binary `0x7d0c` (`111110100001100₂`, K = 15) = `0x7d0 ++ 0xc` evaluates on the
    RPN stack to `−1`. -/
def bits_0x7d0c : List Bool :=
  bits_0x7d0 ++ [true, true, false, false]

theorem evalRpn_0x7d0c :
    evalRpn X.one (eml (α := α)) bits_0x7d0c [] = some [X.negOne] := by
  unfold bits_0x7d0c
  rw [evalRpn_append_0xc_value bits_0x7d0 X.negInf evalRpn_0x7d0]
  rw [X.exp_negInf, X.sub_zero_one]

/-- Binary `0x1fa1a8` (`111111010000110101000₂`, K = 21) =
    `eml(1, eml(−∞, exp(exp(e))))` evaluates on the RPN stack to `+iπ` on the lower cut. -/
def bits_0x1fa1a8 : List Bool :=
  [true] ++ bits_0x7d0 ++ [true, true, false, true, false, true, false, false, false]

theorem evalRpn_0x1fa1a8 :
    evalRpn X.one (eml (α := α)) bits_0x1fa1a8 [] = some [X.ipi] := by
  unfold bits_0x1fa1a8
  change some [eml X.one (eml (eml X.one (eml X.one (cZero (α := α))))
    (eml (eml (eml X.one X.one) X.one) X.one))] = some [X.ipi]
  rw [cZero_eq_zero]
  unfold eml
  rw [X.ln_zero, X.sub_negInf, X.ln_posInf, X.sub_posInf]
  rw [X.ln_one, X.sub_zero, X.sub_zero, X.sub_zero]
  rw [X.exp_negInf]
  rw [X.ln_exp (X.exp (X.exp X.one)) X.inStrip_exp_exp_one]
  rw [X.zero_sub, X.ln_neg_exp_exp_one]
  rw [X.sub_sub_cancel]

/-- Binary `0x1fa1a8c` (`1111110100001101010001100₂`, K = 25) = `0x1fa1a8 ++ 0xc`
    evaluates on the RPN stack to `−2` on the lower cut. -/
def bits_0x1fa1a8c : List Bool :=
  bits_0x1fa1a8 ++ [true, true, false, false]

theorem evalRpn_0x1fa1a8c :
    evalRpn X.one (eml (α := α)) bits_0x1fa1a8c [] = some [X.negTwo] := by
  unfold bits_0x1fa1a8c
  rw [evalRpn_append_0xc_value bits_0x1fa1a8 X.ipi evalRpn_0x1fa1a8]
  rw [X.exp_ipi, X.sub_negOne_one]

end ConstantRecords

end Eml.Extended
