/-
  Machine-checked Lean 4 formalization of the core EML identities from
  Odrzywołek (arXiv:2603.21852) and EML and One.

  Every theorem below is proved with zero `sorry` under explicit strip
  hypotheses so branch cuts are never hidden.
-/

namespace Eml

/-- An abstract algebraic model of a domain with `exp` and `ln` on a
    principal strip `inStrip : α → Prop` (e.g. `Im z ∈ [-π, π)` on `ℂ`,
    or `True` on `ℝ`). -/
class EmlModel (α : Type) where
  zero : α
  one : α
  add : α → α → α
  sub : α → α → α
  neg : α → α
  mul : α → α → α
  exp : α → α
  ln : α → α
  inStrip : α → Prop
  nonzero : α → Prop
  add_zero : ∀ x, add x zero = x
  sub_zero : ∀ x, sub x zero = x
  zero_sub : ∀ x, sub zero x = neg x
  sub_self : ∀ x, sub x x = zero
  sub_sub_cancel : ∀ a b, sub a (sub a b) = b
  sub_add_cancel : ∀ a b, sub (add a b) a = b
  ln_one : ln one = zero
  exp_zero : exp zero = one
  inStrip_one : inStrip one
  inStrip_exp_one : inStrip (exp one)
  ln_exp : ∀ x, inStrip x → ln (exp x) = x
  exp_ln : ∀ y, nonzero y → exp (ln y) = y
  exp_add : ∀ a b, exp (add a b) = mul (exp a) (exp b)

section CoreIdentities

variable {α : Type} [M : EmlModel α]

/-- The single binary operator: `eml(x, y) = exp(x) − ln(y)`. -/
def eml (x y : α) : α :=
  M.sub (M.exp x) (M.ln y)

/-- `e = eml(1, 1)` (RPN: `11E`, K = 3, hex `0x6`). -/
def cE : α := eml M.one M.one

theorem cE_eq_exp_one : cE (α := α) = M.exp M.one := by
  unfold cE eml
  rw [M.ln_one, M.sub_zero]

/-- `0 = eml(1, eml(eml(1, 1), 1))` (RPN: `111E1EE`, K = 7, hex `0x74`). -/
def cZero : α := eml M.one (eml (eml M.one M.one) M.one)

theorem cZero_eq_zero : cZero (α := α) = M.zero := by
  unfold cZero eml
  rw [M.ln_one, M.sub_zero, M.sub_zero]
  rw [M.ln_exp (M.exp M.one) M.inStrip_exp_one]
  exact M.sub_self (M.exp M.one)

/-- `exp(x) = eml(x, 1)`. -/
def emlExp (x : α) : α := eml x M.one

theorem emlExp_eq (x : α) : emlExp x = M.exp x := by
  unfold emlExp eml
  rw [M.ln_one, M.sub_zero]

/-- `ln(x) = eml(1, eml(eml(1, x), 1))` whenever `e − ln(x)` lies in the strip. -/
def emlLn (x : α) : α := eml M.one (eml (eml M.one x) M.one)

theorem emlLn_eq (x : α) (h : M.inStrip (M.sub (M.exp M.one) (M.ln x))) :
    emlLn x = M.ln x := by
  unfold emlLn eml
  rw [M.ln_one, M.sub_zero]
  rw [M.ln_exp _ h]
  exact M.sub_sub_cancel (M.exp M.one) (M.ln x)

/-- The `0xc` binary nibble identity (`docs/binary.md`):
    appending `1100₂` (`11EE`) to any program `X` computes `eml(X, eml(1, 1)) = exp(X) − 1`. -/
def append0xc (x : α) : α := eml x (eml M.one M.one)

theorem append0xc_eq (x : α) : append0xc x = M.sub (M.exp x) M.one := by
  unfold append0xc eml
  rw [M.ln_one, M.sub_zero]
  rw [M.ln_exp M.one M.inStrip_one]

/-- Negation via `0`: `eml(0, exp(x)) = 1 − x`? Better: `ln(1) - ...` or `exp(ln(x))`:
    here `rawSub a b = ln(exp(a) / exp(b))` via `eml(a, exp(b))` = `exp(a) - b`.
    Specifically `eml(ln(a), exp(b)) = a - b` when `a ≠ 0` and `b` is in the strip. -/
def rawSub (a b : α) : α := eml (M.ln a) (M.exp b)

theorem rawSub_eq (a b : α) (ha : M.nonzero a) (hb : M.inStrip b) :
    rawSub a b = M.sub a b := by
  unfold rawSub eml
  rw [M.exp_ln a ha, M.ln_exp b hb]

/-- `rawNeg x = rawSub 0 x` requires `ln 0`; alternatively `sub(0, x)` via `eml(cZero, exp(x))` gives `1 - x`,
    and `eml(ln(1), exp(x))` gives `1 - x`. Direct `eml` form for `1 - x`: -/
theorem eml_zero_exp (x : α) (hx : M.inStrip x) :
    eml cZero (M.exp x) = M.sub M.one x := by
  unfold eml
  rw [cZero_eq_zero, M.exp_zero, M.ln_exp x hx]

end CoreIdentities

end Eml
