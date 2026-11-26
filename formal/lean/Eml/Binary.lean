/-
  Machine-checked combinatorial theorems for the binary representation of
  constant EML programs (`docs/binary.md`):
    - `true`  = bit `1` = press `1`  (stack depth +1)
    - `false` = bit `0` = press `EML` (stack depth -1)

  Zero axioms, zero `sorry` — pure Lean 4 inductive proofs.
-/

namespace Eml.Binary

/-- Run the stack-height transition of a binary EML program from an initial
    stack depth `d`. Returns `none` if the stack underflows (`false` on depth < 2). -/
def runDepth : List Bool → Nat → Option Nat
  | [], d => some d
  | true :: rest, d => runDepth rest (d + 1)
  | false :: rest, d =>
    if d ≥ 2 then runDepth rest (d - 1) else none

/-- A bit list is a valid constant EML program iff starting from depth 0
    it never underflows and ends at stack depth 1. -/
def IsValidProgram (bits : List Bool) : Prop :=
  runDepth bits 0 = some 1

/-- Appending two bit lists composes `runDepth`. -/
theorem runDepth_append (xs ys : List Bool) (d : Nat) :
    runDepth (xs ++ ys) d =
      match runDepth xs d with
      | some d' => runDepth ys d'
      | none => none := by
  induction xs generalizing d with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true => exact ih (d + 1)
    | false =>
      simp only [List.cons_append, runDepth]
      split
      · exact ih (d - 1)
      · rfl

/-- The 1-press program `[true]` (`1`, `0x1`) is valid. -/
theorem valid_one : IsValidProgram [true] := rfl

/-- The 3-press program `[true, true, false]` (`110₂ = 0x6`, `e`) is valid. -/
theorem valid_e : IsValidProgram [true, true, false] := rfl

/-- The 7-press program `1110100₂ = 0x74` (`0`) is valid. -/
theorem valid_zero : IsValidProgram [true, true, true, false, true, false, false] := rfl

/-- The `0xc` nibble (`1100₂ = [true, true, false, false]`):
    appending `0xc` to ANY valid program produces a valid program!
    Combined with `Eml.append0xc_eq`, this proves appending hex digit `c`
    to any valid EML binary program always computes `exp(X) - 1`. -/
theorem valid_append_0xc (p : List Bool) (hp : IsValidProgram p) :
    IsValidProgram (p ++ [true, true, false, false]) := by
  unfold IsValidProgram at hp ⊢
  rw [runDepth_append, hp]
  rfl

/-- Appending any valid program `q` followed by `EML` (`false`) to a valid
    program `p` produces a valid program `eml(p, q)`. -/
theorem runDepth_shift (xs : List Bool) (d k r : Nat) :
    runDepth xs d = some r → runDepth xs (d + k) = some (r + k) := by
  induction xs generalizing d with
  | nil =>
    intro h
    simp only [runDepth, Option.some.injEq] at h ⊢
    omega
  | cons b rest ih =>
    intro h
    cases b with
    | true =>
      simp only [runDepth] at h ⊢
      have h1 : d + k + 1 = (d + 1) + k := by omega
      rw [h1]
      exact ih (d + 1) h
    | false =>
      simp only [runDepth] at h ⊢
      split at h
      · rename_i hge
        have hge' : d + k ≥ 2 := by omega
        simp only [hge', ↓reduceIte]
        have hsub : d + k - 1 = (d - 1) + k := by omega
        rw [hsub]
        exact ih (d - 1) h
      · cases h

theorem valid_eml_combine (p q : List Bool) (hp : IsValidProgram p) (hq : IsValidProgram q) :
    IsValidProgram (p ++ q ++ [false]) := by
  unfold IsValidProgram at hp hq ⊢
  rw [List.append_assoc, runDepth_append, hp]
  dsimp only
  rw [runDepth_append]
  have hq' : runDepth q (0 + 1) = some (1 + 1) := runDepth_shift q 0 1 1 hq
  simp only [Nat.zero_add] at hq'
  rw [hq']
  rfl

/-- Every valid EML program starts with `true` (the `1` key) and is therefore non-empty. -/
theorem valid_program_starts_true (p : List Bool) (hp : IsValidProgram p) :
    ∃ rest, p = true :: rest := by
  cases p with
  | nil =>
    unfold IsValidProgram runDepth at hp
    cases hp
  | cons b rest =>
    cases b with
    | true => exact ⟨rest, rfl⟩
    | false =>
      unfold IsValidProgram runDepth at hp
      simp at hp

/-- Helper invariant: `runDepth` changes stack depth by `ones - zeros`, so
    `d + ones = r + zeros` whenever `runDepth xs d = some r`. -/
theorem runDepth_balance (xs : List Bool) (d r : Nat) :
    runDepth xs d = some r →
      d + xs.count true = r + xs.count false := by
  induction xs generalizing d with
  | nil =>
    intro h
    simp only [runDepth, Option.some.injEq] at h
    simp [h]
  | cons b rest ih =>
    intro h
    cases b with
    | true =>
      simp only [runDepth] at h
      have hrec := ih (d + 1) h
      simp [List.count_cons]
      omega
    | false =>
      simp only [runDepth] at h
      split at h
      · rename_i hge
        have hrec := ih (d - 1) h
        simp [List.count_cons]
        omega
      · cases h

theorem list_bool_length_eq_count (xs : List Bool) :
    xs.length = xs.count true + xs.count false := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simp [List.count_cons, ih] <;> omega

/-- Every valid EML program has `ones = zeros + 1` and odd length `2 * zeros + 1`. -/
theorem valid_program_odd_length (p : List Bool) (hp : IsValidProgram p) :
    p.count true = p.count false + 1 ∧ p.length = 2 * p.count false + 1 := by
  have hbal : 0 + p.count true = 1 + p.count false := runDepth_balance p 0 1 hp
  have hlen : p.length = p.count true + p.count false := list_bool_length_eq_count p
  constructor <;> omega

/-- Formal RPN stack evaluator parameterized by any binary operator `op` and constant `one`. -/
def evalRpn {α : Type} (one : α) (op : α → α → α) : List Bool → List α → Option (List α)
  | [], st => some st
  | true :: rest, st => evalRpn one op rest (one :: st)
  | false :: rest, y :: x :: st => evalRpn one op rest (op x y :: st)
  | false :: _, _ => none

theorem evalRpn_append {α : Type} (one : α) (op : α → α → α) (xs ys : List Bool) (st : List α) :
    evalRpn one op (xs ++ ys) st =
      match evalRpn one op xs st with
      | some st' => evalRpn one op ys st'
      | none => none := by
  induction xs generalizing st with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | true => exact ih (one :: st)
    | false =>
      cases st with
      | nil => rfl
      | cons y st1 =>
        cases st1 with
        | nil => rfl
        | cons x st2 => exact ih (op x y :: st2)

/-- Semantics bridge for the `0xc` nibble (`1100₂ = [true, true, false, false]`):
    if program `p` evaluates to value `v` on the stack, then `p ++ 0xc`
    evaluates to `op v (op one one)` (= `eml v (eml 1 1) = exp(v) - 1`). -/
theorem evalRpn_append_0xc {α : Type} (one : α) (op : α → α → α)
    (p : List Bool) (v : α) (hp : evalRpn one op p [] = some [v]) :
    evalRpn one op (p ++ [true, true, false, false]) [] = some [op v (op one one)] := by
  rw [evalRpn_append, hp]
  rfl

end Eml.Binary
