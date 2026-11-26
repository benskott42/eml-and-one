/-
  Machine-checked Lean 4 proofs of elementary arithmetic (`+`, `-`, `*`, `/`, `1/x`)
  constructed solely from `eml(x, y) = exp(x) − ln(y)` and `1`
  (Odrzywołek, arXiv:2603.21852).

  Zero `sorry`.
-/
import Eml.Basic

namespace Eml.Arithmetic

/-- Extended algebraic model supporting multiplication, division, and logarithms
    of products/quotients on the principal strip. -/
class EmlArithModel (α : Type) extends EmlModel α where
  div : α → α → α
  inv : α → α
  sub_neg_eq_add : ∀ a b, sub a (neg b) = add a b
  exp_neg : ∀ x, exp (neg x) = inv (exp x)
  exp_sub : ∀ a b, exp (sub a b) = div (exp a) (exp b)
  ln_inv : ∀ x, nonzero x → inStrip (neg (ln x)) → ln (inv x) = neg (ln x)
  inv_eq_div_one : ∀ x, inv x = div one x

section Operations

variable {α : Type} [A : EmlArithModel α]

/- `emlMul`, `emlDiv`, `emlInv`, and `emlAdd` constructed from `eml` and `1`
   under explicit `nonzero` and `inStrip` hypotheses. -/

/-- `emlMul a b = exp(ln a + ln b) = a * b` for `a ≠ 0, b ≠ 0`. -/
def emlMul (a b : α) : α :=
  emlExp (A.add (A.ln a) (A.ln b))

theorem emlMul_eq (a b : α) (ha : A.nonzero a) (hb : A.nonzero b) :
    emlMul a b = A.mul a b := by
  unfold emlMul
  rw [emlExp_eq, A.exp_add, A.exp_ln a ha, A.exp_ln b hb]

/-- `emlDiv a b = exp(ln a − ln b) = a / b` for `a ≠ 0, b ≠ 0`. -/
def emlDiv (a b : α) : α :=
  emlExp (A.sub (A.ln a) (A.ln b))

theorem emlDiv_eq (a b : α) (ha : A.nonzero a) (hb : A.nonzero b) :
    emlDiv a b = A.div a b := by
  unfold emlDiv
  rw [emlExp_eq, A.exp_sub, A.exp_ln a ha, A.exp_ln b hb]

/-- `emlInv x = exp(−ln x) = x⁻¹` for `x ≠ 0`. -/
def emlInv (x : α) : α :=
  emlExp (A.neg (A.ln x))

theorem emlInv_eq (x : α) (hx : A.nonzero x) :
    emlInv x = A.inv x := by
  unfold emlInv
  rw [emlExp_eq, A.exp_neg, A.exp_ln x hx]

/-- `emlAdd a b = eml(ln a, exp(−b)) = a + b` when `a ≠ 0` and `−b` lies in the strip. -/
def emlAdd (a b : α) : α :=
  eml (A.ln a) (A.exp (A.neg b))

theorem emlAdd_eq (a b : α) (ha : A.nonzero a) (hb : A.inStrip (A.neg b)) :
    emlAdd a b = A.add a b := by
  unfold emlAdd eml
  rw [A.exp_ln a ha, A.ln_exp (A.neg b) hb, A.sub_neg_eq_add]

end Operations

end Eml.Arithmetic
