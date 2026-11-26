/-
  Machine-checked Lean 4 soundness bridge between the combinatorial binary
  representation (`Eml.Binary`) and the algebraic EML semantics (`Eml.Basic`).

  Key theorems (zero `sorry`):
  - `evalRpn_runDepth_iff`: `runDepth xs st.length = some r` iff `evalRpn`
    succeeds with a stack of length `r`.
  - `valid_program_evals_singleton`: every valid binary EML program
    (`IsValidProgram p`) never underflows and evaluates to a singleton `[v]`.
  - Concrete end-to-end RPN stack proofs for `0x1` (`1`), `0x6` (`e`),
    `0x74` (`0`), and the `0xc` nibble (`p ++ 0xc ↦ exp(v) − 1`).
-/
import Eml.Basic
import Eml.Binary

namespace Eml.RpnSoundness

open Eml
open Eml.Binary

/-- Stack-depth soundness: `runDepth` tracks the exact stack length of `evalRpn`
    for every bitstring `xs`, every starting stack `st`, and any binary operator `op`. -/
theorem evalRpn_some_of_runDepth {α : Type} (one : α) (op : α → α → α)
    (xs : List Bool) (st : List α) (r : Nat) :
    runDepth xs st.length = some r →
      ∃ st', evalRpn one op xs st = some st' ∧ st'.length = r := by
  induction xs generalizing st with
  | nil =>
    intro h
    simp only [runDepth, Option.some.injEq] at h
    exact ⟨st, rfl, h⟩
  | cons b rest ih =>
    intro h
    cases b with
    | true =>
      simp only [runDepth] at h
      have hlen : (one :: st).length = st.length + 1 := rfl
      rw [← hlen] at h
      exact ih (one :: st) h
    | false =>
      simp only [runDepth] at h
      split at h
      · rename_i hge
        match st with
        | [] => simp at hge
        | [_] => simp at hge
        | y :: x :: st2 =>
          simp only [List.length_cons] at h
          have hsub : st2.length + 1 + 1 - 1 = (op x y :: st2).length := by
            simp only [List.length_cons]
            omega
          rw [hsub] at h
          exact ih (op x y :: st2) h
      · cases h

/-- Every valid binary EML program (`IsValidProgram p`) evaluates on an empty
    RPN stack without underflowing and produces a unique singleton result `[v]`. -/
theorem valid_program_evals_singleton {α : Type} (one : α) (op : α → α → α)
    (p : List Bool) (hp : IsValidProgram p) :
    ∃ v : α, evalRpn one op p [] = some [v] := by
  have ⟨st', heval, hlen⟩ := evalRpn_some_of_runDepth one op p [] 1 hp
  match st' with
  | [v] => exact ⟨v, heval⟩
  | [] => simp at hlen
  | _ :: _ :: _ => simp at hlen

section ConcretePrograms

variable {α : Type} [M : EmlModel α]

/-- Binary `0x1` (`1₂`) evaluates on the RPN stack to `1`. -/
theorem evalRpn_0x1 :
    evalRpn M.one (eml (α := α)) [true] [] = some [M.one] := rfl

/-- Binary `0x6` (`110₂`) evaluates on the RPN stack to `e = exp(1)`. -/
theorem evalRpn_0x6 :
    evalRpn M.one (eml (α := α)) [true, true, false] [] = some [M.exp M.one] := by
  change some [cE (α := α)] = some [M.exp M.one]
  rw [cE_eq_exp_one]

/-- Binary `0x74` (`1110100₂`) evaluates on the RPN stack to `0`. -/
theorem evalRpn_0x74 :
    evalRpn M.one (eml (α := α)) [true, true, true, false, true, false, false] [] = some [M.zero] := by
  change some [cZero (α := α)] = some [M.zero]
  rw [cZero_eq_zero]

/-- End-to-end `0xc` nibble theorem: if binary program `p` evaluates on the
    RPN stack to `[v]`, then `p ++ 0xc` (`1100₂`) evaluates to `[exp(v) − 1]`. -/
theorem evalRpn_append_0xc_value (p : List Bool) (v : α)
    (hp : evalRpn M.one (eml (α := α)) p [] = some [v]) :
    evalRpn M.one (eml (α := α)) (p ++ [true, true, false, false]) [] =
      some [M.sub (M.exp v) M.one] := by
  rw [evalRpn_append_0xc M.one (eml (α := α)) p v hp]
  change some [append0xc v] = some [M.sub (M.exp v) M.one]
  rw [append0xc_eq]

end ConcretePrograms

end Eml.RpnSoundness
