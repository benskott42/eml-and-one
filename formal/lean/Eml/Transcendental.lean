/-
  Machine-checked Lean 4 proofs of elementary transcendental functions
  (`cos`, `sin`, `cosh`, `sinh`, `pow`, `sqrt`, `logBase`) built from
  `eml(x, y) = exp(x) − ln(y)` and `1`.

  Zero `sorry`.
-/
import Eml.Basic
import Eml.Arithmetic

namespace Eml.Transcendental

open Eml
open Eml.Arithmetic

/-- Algebraic model extending `EmlArithModel` with `2`, `i`, and the
    exponential definitions of circular and hyperbolic functions. -/
class EmlTransModel (α : Type) extends EmlArithModel α where
  two : α
  iu : α
  cos : α → α
  sin : α → α
  cosh : α → α
  sinh : α → α
  pow : α → α → α
  sqrt : α → α
  logBase : α → α → α
  cos_def : ∀ x, cos x = div (add (exp (mul iu x)) (exp (neg (mul iu x)))) two
  sin_def : ∀ x, sin x = div (sub (exp (mul iu x)) (exp (neg (mul iu x)))) (mul two iu)
  cosh_def : ∀ x, cosh x = div (add (exp x) (exp (neg x))) two
  sinh_def : ∀ x, sinh x = div (sub (exp x) (exp (neg x))) two
  pow_def : ∀ x y, nonzero x → pow x y = exp (mul y (ln x))
  sqrt_def : ∀ x, nonzero x → sqrt x = exp (div (ln x) two)
  logBase_def : ∀ b x, nonzero b → nonzero x → logBase b x = div (ln x) (ln b)

section Constructions

variable {α : Type} [T : EmlTransModel α]

/-- `emlCos x = (emlExp(i·x) + emlExp(−(i·x))) / 2 = cos(x)`. -/
def emlCos (x : α) : α :=
  T.div (T.add (emlExp (T.mul T.iu x)) (emlExp (T.neg (T.mul T.iu x)))) T.two

theorem emlCos_eq (x : α) : emlCos x = T.cos x := by
  unfold emlCos
  rw [emlExp_eq, emlExp_eq, T.cos_def]

/-- `emlSin x = (emlExp(i·x) − emlExp(−(i·x))) / (2i) = sin(x)`. -/
def emlSin (x : α) : α :=
  T.div (T.sub (emlExp (T.mul T.iu x)) (emlExp (T.neg (T.mul T.iu x)))) (T.mul T.two T.iu)

theorem emlSin_eq (x : α) : emlSin x = T.sin x := by
  unfold emlSin
  rw [emlExp_eq, emlExp_eq, T.sin_def]

/-- `emlCosh x = (emlExp(x) + emlExp(−x)) / 2 = cosh(x)`. -/
def emlCosh (x : α) : α :=
  T.div (T.add (emlExp x) (emlExp (T.neg x))) T.two

theorem emlCosh_eq (x : α) : emlCosh x = T.cosh x := by
  unfold emlCosh
  rw [emlExp_eq, emlExp_eq, T.cosh_def]

/-- `emlSinh x = (emlExp(x) − emlExp(−x)) / 2 = sinh(x)`. -/
def emlSinh (x : α) : α :=
  T.div (T.sub (emlExp x) (emlExp (T.neg x))) T.two

theorem emlSinh_eq (x : α) : emlSinh x = T.sinh x := by
  unfold emlSinh
  rw [emlExp_eq, emlExp_eq, T.sinh_def]

/-- `emlPow x y = emlExp(y · emlLn(x)) = x^y` for `x ≠ 0` and `e − ln x` in the strip. -/
def emlPow (x y : α) : α :=
  emlExp (T.mul y (emlLn x))

theorem emlPow_eq (x y : α) (hx : T.nonzero x)
    (hstrip : T.inStrip (T.sub (T.exp T.one) (T.ln x))) :
    emlPow x y = T.pow x y := by
  unfold emlPow
  rw [emlExp_eq, emlLn_eq x hstrip, T.pow_def x y hx]

/-- `emlSqrt x = emlExp(emlLn(x) / 2) = √x` for `x ≠ 0` and `e − ln x` in the strip. -/
def emlSqrt (x : α) : α :=
  emlExp (T.div (emlLn x) T.two)

theorem emlSqrt_eq (x : α) (hx : T.nonzero x)
    (hstrip : T.inStrip (T.sub (T.exp T.one) (T.ln x))) :
    emlSqrt x = T.sqrt x := by
  unfold emlSqrt
  rw [emlExp_eq, emlLn_eq x hstrip, T.sqrt_def x hx]

/-- `emlLogBase b x = emlLn(x) / emlLn(b) = log_b(x)`. -/
def emlLogBase (b x : α) : α :=
  T.div (emlLn x) (emlLn b)

theorem emlLogBase_eq (b x : α) (hb : T.nonzero b) (hx : T.nonzero x)
    (hsb : T.inStrip (T.sub (T.exp T.one) (T.ln b)))
    (hsx : T.inStrip (T.sub (T.exp T.one) (T.ln x))) :
    emlLogBase b x = T.logBase b x := by
  unfold emlLogBase
  rw [emlLn_eq x hsx, emlLn_eq b hsb, T.logBase_def b x hb hx]

end Constructions

end Eml.Transcendental
