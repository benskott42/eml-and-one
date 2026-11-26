/-
  Machine-checked Lean 4 proofs of EML syntax-tree compilation, RPN compiler
  correctness, and unique parsing (injectivity of `toRpn`).

  Zero axioms, zero `sorry` — pure Lean 4 inductive proofs.
-/
import Eml.Binary

namespace Eml.TreeBijection

open Eml.Binary

/-- The full binary tree grammar `S → 1 | eml(S, S)`. -/
inductive EmlTree where
  | one : EmlTree
  | eml : EmlTree → EmlTree → EmlTree
  deriving DecidableEq, Repr

/-- Number of `eml` gates in a tree. -/
def EmlTree.gates : EmlTree → Nat
  | .one => 0
  | .eml a b => a.gates + b.gates + 1

/-- Compile an `EmlTree` to its post-order RPN binary program (`true = 1`, `false = EML`). -/
def EmlTree.toRpn : EmlTree → List Bool
  | .one => [true]
  | .eml a b => a.toRpn ++ b.toRpn ++ [false]

/-- Direct structural evaluation of an `EmlTree` in any algebra `(α, one, op)`. -/
def EmlTree.eval {α : Type} (one : α) (op : α → α → α) : EmlTree → α
  | .one => one
  | .eml a b => op (a.eval one op) (b.eval one op)

/-- Every `EmlTree` compiles to a valid Dyck-prefix binary program (`IsValidProgram`). -/
theorem toRpn_valid (t : EmlTree) : IsValidProgram t.toRpn := by
  induction t with
  | one => exact valid_one
  | eml a b iha ihb => exact valid_eml_combine a.toRpn b.toRpn iha ihb

/-- Every `g`-gate `EmlTree` compiles to a bitstring of length `K = 2 * g + 1`. -/
theorem toRpn_length (t : EmlTree) : t.toRpn.length = 2 * t.gates + 1 := by
  induction t with
  | one => rfl
  | eml a b iha ihb =>
    simp only [EmlTree.toRpn, EmlTree.gates, List.length_append, List.length_singleton]
    omega

/-- Compiler correctness theorem: running the 2-button RPN stack machine `evalRpn`
    on `t.toRpn` always pushes `t.eval one op` onto any existing stack `st`. -/
theorem evalRpn_toRpn {α : Type} (one : α) (op : α → α → α) (t : EmlTree) (st : List α) :
    evalRpn one op t.toRpn st = some (t.eval one op :: st) := by
  induction t generalizing st with
  | one => rfl
  | eml a b iha ihb =>
    simp only [EmlTree.toRpn, EmlTree.eval]
    rw [List.append_assoc, evalRpn_append, iha, evalRpn_append, ihb]
    rfl

/-- Evaluating a tree in the free term algebra `(EmlTree, .one, .eml)` is the identity. -/
theorem eval_free (t : EmlTree) : t.eval EmlTree.one EmlTree.eml = t := by
  induction t with
  | one => rfl
  | eml a b iha ihb =>
    simp only [EmlTree.eval, iha, ihb]

/-- Unique-parse theorem (injectivity of `toRpn`):
    no two distinct EML trees compile to the same binary bitstring. -/
theorem toRpn_injective (t₁ t₂ : EmlTree) (h : t₁.toRpn = t₂.toRpn) : t₁ = t₂ := by
  have h1 := evalRpn_toRpn EmlTree.one EmlTree.eml t₁ []
  have h2 := evalRpn_toRpn EmlTree.one EmlTree.eml t₂ []
  rw [h, eval_free] at h1
  rw [eval_free] at h2
  rw [h1] at h2
  injection h2 with hcons
  injection hcons

end Eml.TreeBijection
