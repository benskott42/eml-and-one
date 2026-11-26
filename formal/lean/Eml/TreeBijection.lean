/-
  Machine-checked Lean 4 proofs of the full bijection between EML syntax trees
  (`EmlTree`) and valid Dyck-prefix binary programs (`{ p : List Bool // IsValidProgram p }`),
  along with RPN compiler correctness and unique parsing.

  Zero axioms (beyond Lean's standard `propext`), zero `sorry` — pure Lean 4 inductive proofs.
-/
import Eml.Binary
import Eml.RpnSoundness

namespace Eml.TreeBijection

open Eml.Binary
open Eml.RpnSoundness

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
    rw [List.append_assoc, evalRpn_append, iha]
    dsimp only
    rw [evalRpn_append, ihb]
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

/-! ### Inverse parser and full bijection `EmlTree ≃ { p : List Bool // IsValidProgram p }` -/

/-- Concatenate the RPN encodings of a stack of trees from bottom to top. -/
def stackRpn : List EmlTree → List Bool
  | [] => []
  | t :: rest => stackRpn rest ++ t.toRpn

/-- Key stack invariant: parsing `xs` in the free tree algebra preserves the
    concatenated RPN bitstring `stackRpn st' = stackRpn st ++ xs`. -/
theorem evalRpn_free_stackRpn (xs : List Bool) (st st' : List EmlTree)
    (h : evalRpn EmlTree.one EmlTree.eml xs st = some st') :
    stackRpn st' = stackRpn st ++ xs := by
  induction xs generalizing st with
  | nil =>
    simp only [evalRpn, Option.some.injEq] at h
    subst h
    simp
  | cons b rest ih =>
    cases b with
    | true =>
      simp only [evalRpn] at h
      have hrec := ih (EmlTree.one :: st) h
      simp only [stackRpn, EmlTree.toRpn, List.append_assoc, List.singleton_append] at hrec ⊢
      exact hrec
    | false =>
      match st with
      | [] => simp [evalRpn] at h
      | [_] => simp [evalRpn] at h
      | bTree :: aTree :: restSt =>
        simp only [evalRpn] at h
        have hrec := ih (EmlTree.eml aTree bTree :: restSt) h
        simp only [stackRpn, EmlTree.toRpn, List.append_assoc, List.singleton_append] at hrec ⊢
        exact hrec

/-- Parse any valid Dyck-prefix binary program back into its unique `EmlTree`. -/
def fromRpn (p : List Bool) (hp : IsValidProgram p) : EmlTree :=
  match h : evalRpn EmlTree.one EmlTree.eml p [] with
  | some [t] => t
  | some [] =>
    False.elim (by
      obtain ⟨v, hv⟩ := valid_program_evals_singleton EmlTree.one EmlTree.eml p hp
      rw [hv] at h; cases h)
  | some (_ :: _ :: _) =>
    False.elim (by
      obtain ⟨v, hv⟩ := valid_program_evals_singleton EmlTree.one EmlTree.eml p hp
      rw [hv] at h; cases h)
  | none =>
    False.elim (by
      obtain ⟨v, hv⟩ := valid_program_evals_singleton EmlTree.one EmlTree.eml p hp
      rw [hv] at h; cases h)

/-- Right inverse (surjectivity of `toRpn`): compiling `fromRpn p hp` recovers `p`. -/
theorem toRpn_fromRpn (p : List Bool) (hp : IsValidProgram p) :
    (fromRpn p hp).toRpn = p := by
  obtain ⟨v, hv⟩ := valid_program_evals_singleton EmlTree.one EmlTree.eml p hp
  have hfrom : fromRpn p hp = v := by
    unfold fromRpn
    split
    · rename_i t ht
      rw [hv] at ht
      injection ht with hcons
      injection hcons with htv
      exact htv.symm
    all_goals
      rename_i hbad
      rw [hv] at hbad
      cases hbad
  rw [hfrom]
  have hinv := evalRpn_free_stackRpn p [] [v] hv
  simpa [stackRpn] using hinv

/-- Left inverse: parsing `t.toRpn` recovers `t`. -/
theorem fromRpn_toRpn (t : EmlTree) :
    fromRpn t.toRpn (toRpn_valid t) = t := by
  apply toRpn_injective
  exact toRpn_fromRpn t.toRpn (toRpn_valid t)

/-- Full semantic bridge: evaluating ANY valid binary program `p` on the RPN stack
    in any algebra `(α, one, op)` yields `[ (fromRpn p hp).eval one op ]`. -/
theorem evalRpn_eq_eval_fromRpn {α : Type} (one : α) (op : α → α → α)
    (p : List Bool) (hp : IsValidProgram p) :
    evalRpn one op p [] = some [(fromRpn p hp).eval one op] := by
  have h := evalRpn_toRpn one op (fromRpn p hp) []
  rwa [toRpn_fromRpn p hp] at h

/-- Explicit bijection `EmlTree ≃ { p : List Bool // IsValidProgram p }`. -/
def treeEquivValidProgram : EmlTree ≃ { p : List Bool // IsValidProgram p } where
  toFun t := ⟨t.toRpn, toRpn_valid t⟩
  invFun s := fromRpn s.1 s.2
  left_inv t := fromRpn_toRpn t
  right_inv s := Subtype.ext (toRpn_fromRpn s.1 s.2)

end Eml.TreeBijection
