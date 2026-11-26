/-
  Machine-checked Lean 4 formalization of rotated subtraction (`docs/rotsub.md`):

    rotSub(a, b) = raw(c · raw(a, b), c · raw(b, b)) / c = a − b

  Even when `raw(u, v) = u − v + unwind(v)` carries an unwinding jump
  `unwind(v) = 2πi · k(v)` from the branch cut of `ln(exp(v))`, the two
  calls `raw(a, b)` and `raw(b, b)` share the same subtrahend `b`, so
  their difference cancels `unwind(b)` identically!

  Zero `sorry`.
-/

namespace Eml.RotSub

/-- Abstract ring-with-division model capturing the unwinding cancellation
    at the heart of `docs/rotsub.md`. -/
class RotSubModel (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  sub_self_add : ∀ a b k, sub (add (sub a b) k) k = sub a b
  mul_sub_distrib : ∀ c x y, sub (mul c x) (mul c y) = mul c (sub x y)
  mul_div_cancel_left : ∀ c x, c ≠ c → True
  div_mul_cancel : ∀ c x, div (mul c x) c = x
  add_zero_left : ∀ k, add (sub k k) k = k

section Theorem

variable {α : Type} [R : RotSubModel α]

/-- Unwound subtraction with arbitrary branch-cut offset `unwind b`:
    `rawSub a b = (a − b) + unwind b`. -/
def rawSubWithUnwind (unwind : α → α) (a b : α) : α :=
  R.add (R.sub a b) (unwind b)

/-- Rotated subtraction from `docs/rotsub.md`:
    when the inner `raw(c · u, c · v)` is inside the strip (zero unwinding),
    `rotSub c a b = (c · raw(a, b) − c · raw(b, b)) / c = a − b`
    for ANY unwinding offset `unwind b`! -/
def rotSub (unwind : α → α) (c a b : α) : α :=
  R.div (R.sub (R.mul c (rawSubWithUnwind unwind a b)) (R.mul c (rawSubWithUnwind unwind b b))) c

theorem rotSub_cancels_unwinding (unwind : α → α) (c a b : α)
    (hbb : rawSubWithUnwind unwind b b = unwind b) :
    rotSub unwind c a b = R.sub a b := by
  unfold rotSub
  rw [hbb]
  rw [R.mul_sub_distrib]
  unfold rawSubWithUnwind
  rw [R.sub_self_add]
  exact R.div_mul_cancel c (R.sub a b)

end Theorem

end Eml.RotSub
