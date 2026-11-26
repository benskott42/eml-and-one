/-
  Machine-checked Lean 4 + Mathlib proofs of:
  1. Raney's Cycle Lemma (`docs/binary.md`, `lib/eml/binary.ts`):
     Every binary word `p : List Bool` with `p.count true = p.count false + 1`
     has a UNIQUE cyclic rotation `k < p.length` that is a valid EML program
     (`IsValidProgram (cycleRotate p k)`).
  2. Catalan enumeration (`docs/binary.md`):
     The number of `n`-gate EML syntax trees — and hence the number of valid
     binary EML programs of length `K = 2 * n + 1` — equals `catalan n`.

  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Finset.Card
import Eml.Binary
import Eml.TreeBijection

namespace Eml.CycleLemma

open Eml.Binary
open Eml.TreeBijection

/-! ### Part 1: Raney's Cycle Lemma -/

/-- Cyclic left-rotation of `p` by `k` positions: `p.drop k ++ p.take k`. -/
def cycleRotate (p : List Bool) (k : Nat) : List Bool :=
  p.drop k ++ p.take k

/-- Signed net stack-height delta of a bitstring (`true => +1`, `false => -1`). -/
def netBal : List Bool → Int
  | [] => 0
  | true :: xs => netBal xs + 1
  | false :: xs => netBal xs - 1

theorem netBal_append (xs ys : List Bool) :
    netBal (xs ++ ys) = netBal xs + netBal ys := by
  induction xs with
  | nil => simp [netBal]
  | cons b rest ih =>
    cases b <;> simp [netBal, ih] <;> omega

theorem netBal_eq_count_sub (xs : List Bool) :
    netBal xs = (xs.count true : Int) - (xs.count false : Int) := by
  induction xs with
  | nil => simp [netBal]
  | cons b rest ih =>
    cases b <;> simp [netBal, ih] <;> omega

/-- Exact characterization of `runDepth` via `netBal`. -/
theorem runDepth_eq_some_iff (xs : List Bool) (d r : Nat) :
    runDepth xs d = some r ↔
      ((r : Int) = (d : Int) + netBal xs ∧
        ∀ j, 1 ≤ j → j ≤ xs.length → 1 ≤ (d : Int) + netBal (xs.take j)) := by
  induction xs generalizing d with
  | nil =>
    simp only [runDepth, Option.some.injEq, netBal, add_zero, List.length_nil]
    constructor
    · intro h; subst h; exact ⟨rfl, fun j h1 h2 => by omega⟩
    · rintro ⟨h, _⟩; omega
  | cons b rest ih =>
    cases b with
    | true =>
      simp only [runDepth, netBal, List.length_cons]
      rw [ih (d + 1)]
      constructor
      · rintro ⟨hsum, hpref⟩
        refine ⟨by omega, fun j hj1 hjlen => ?_⟩
        cases j with
        | zero => omega
        | succ j' =>
          cases j' with
          | zero => simp [netBal]
          | succ j'' =>
            have h := hpref (j'' + 1) (by omega) (by omega)
            simp only [List.take_succ_cons, netBal] at h ⊢
            omega
      · rintro ⟨hsum, hpref⟩
        refine ⟨by omega, fun j hj1 hjlen => ?_⟩
        have h := hpref (j + 1) (by omega) (by omega)
        simp only [List.take_succ_cons, netBal] at h ⊢
        omega
    | false =>
      simp only [runDepth, netBal, List.length_cons]
      constructor
      · intro h
        split at h
        · rename_i hge
          rw [ih (d - 1)] at h
          rcases h with ⟨hsum, hpref⟩
          refine ⟨by omega, fun j hj1 hjlen => ?_⟩
          cases j with
          | zero => omega
          | succ j' =>
            cases j' with
            | zero => simp [netBal]; omega
            | succ j'' =>
              have h' := hpref (j'' + 1) (by omega) (by omega)
              simp only [List.take_succ_cons, netBal] at h' ⊢
              omega
        · cases h
      · rintro ⟨hsum, hpref⟩
        have h1 := hpref 1 (by omega) (by omega)
        simp only [List.take_succ_cons, List.take_zero, netBal] at h1
        have hge : 2 ≤ d := by omega
        rw [if_pos hge, ih (d - 1)]
        refine ⟨by omega, fun j hj1 hjlen => ?_⟩
        have h := hpref (j + 1) (by omega) (by omega)
        simp only [List.take_succ_cons, netBal] at h ⊢
        omega

/-- `IsValidProgram p` iff `netBal p = 1` and every non-empty prefix has strictly
    positive `netBal`. -/
theorem isValidProgram_iff_netBal (p : List Bool) :
    IsValidProgram p ↔
      (netBal p = 1 ∧ ∀ j, 1 ≤ j → j ≤ p.length → 1 ≤ netBal (p.take j)) := by
  unfold IsValidProgram
  rw [runDepth_eq_some_iff]
  simp [eq_comm]

private theorem take_cycleRotate (p : List Bool) (k r : Nat) (hk : k ≤ p.length)
    (hr : r ≤ p.length) :
    netBal ((cycleRotate p k).take r) =
      if r ≤ p.length - k then
        netBal (p.take (k + r)) - netBal (p.take k)
      else
        netBal p - netBal (p.take k) + netBal (p.take (r - (p.length - k))) := by
  unfold cycleRotate
  rw [List.take_append]
  have hdrop_len : (p.drop k).length = p.length - k := List.length_drop
  split_ifs with hle
  · have hzero : r - (p.drop k).length = 0 := by omega
    rw [hzero, List.take_zero, List.append_nil]
    have hsplit : p.take k ++ (p.drop k).take r = p.take (k + r) := by
      have h1 : (p.take k ++ p.drop k).take (k + r) = p.take (k + r) := by
        rw [List.take_append_drop]
      rw [List.take_append, List.length_take, Nat.min_eq_left hk, Nat.add_sub_cancel_left] at h1
      rw [List.take_take, Nat.min_eq_right (Nat.le_add_right k r)] at h1
      exact h1
    have hbal := congrArg netBal hsplit
    rw [netBal_append] at hbal
    omega
  · have hall : (p.drop k).take r = p.drop k := List.take_of_length_le (by omega)
    rw [hall, List.take_take, Nat.min_eq_left (by omega), hdrop_len, netBal_append]
    have hfull : netBal (p.take k) + netBal (p.drop k) = netBal p := by
      rw [← netBal_append, List.take_append_drop]
    omega

/-- Helper: in any non-empty finite sequence `f : Nat → Int` on `0 .. n-1`,
    there exists a rightmost index `k < n` attaining the minimum value. -/
private theorem exists_rightmost_min (f : Nat → Int) :
    ∀ n, 0 < n → ∃ k < n, (∀ j < n, f k ≤ f j) ∧ (∀ j, k < j → j < n → f k < f j)
  | 0, h => by omega
  | 1, _ =>
    ⟨0, by omega,
      fun j hj => by
        have h0 : j = 0 := by omega
        rw [h0],
      fun j hj1 hj2 => by omega⟩
  | n + 2, _ => by
    obtain ⟨k, hk, hle, hlt⟩ := exists_rightmost_min f (n + 1) (by omega)
    by_cases hcmp : f (n + 1) ≤ f k
    · refine ⟨n + 1, by omega, fun j hj => ?_, fun j hj1 hj2 => by omega⟩
      by_cases hj' : j = n + 1
      · subst hj'; exact le_refl _
      · exact le_trans hcmp (hle j (by omega))
    · refine ⟨k, by omega, fun j hj => ?_, fun j hj1 hj2 => ?_⟩
      · by_cases hj' : j = n + 1
        · subst hj'; omega
        · exact hle j (by omega)
      · by_cases hj' : j = n + 1
        · subst hj'; omega
        · exact hlt j hj1 (by omega)

/-- **Raney's Cycle Lemma** (`docs/binary.md`, `lib/eml/binary.ts`):
    Every bitstring `p` with `p.count true = p.count false + 1` has a UNIQUE
    cyclic rotation `k < p.length` that is a valid EML program. -/
theorem raney_cycle_lemma (p : List Bool) (hbal : p.count true = p.count false + 1) :
    ∃! k, k < p.length ∧ IsValidProgram (cycleRotate p k) := by
  have hnet : netBal p = 1 := by
    rw [netBal_eq_count_sub, hbal]; omega
  have hpos : 0 < p.length := by
    cases p with
    | nil => simp at hbal
    | cons _ _ => simp
  obtain ⟨k, hk, hle, hlt⟩ := exists_rightmost_min (fun j => netBal (p.take j)) p.length hpos
  have hvalid_k : IsValidProgram (cycleRotate p k) := by
    rw [isValidProgram_iff_netBal]
    have hrot_len : (cycleRotate p k).length = p.length := by
      unfold cycleRotate; rw [List.length_append, List.length_drop, List.length_take]; omega
    have hrot_bal : netBal (cycleRotate p k) = 1 := by
      unfold cycleRotate; rw [netBal_append, add_comm, ← netBal_append, List.take_append_drop, hnet]
    refine ⟨hrot_bal, fun r hr1 hrlen => ?_⟩
    rw [hrot_len] at hrlen
    rw [take_cycleRotate p k r (le_of_lt hk) hrlen]
    split_ifs with hsub
    · by_cases hend : k + r = p.length
      · rw [hend, List.take_length, hnet]
        have h0 := hle 0 hpos; simp [netBal] at h0; omega
      · have hgt := hlt (k + r) (by omega) (by omega); omega
    · have hge := hle (r - (p.length - k)) (by omega); omega
  refine ⟨k, ⟨hk, hvalid_k⟩, ?_⟩
  rintro k' ⟨hk', hval'⟩
  by_contra hne
  rw [isValidProgram_iff_netBal] at hval'
  have hval := (isValidProgram_iff_netBal (cycleRotate p k)).mp hvalid_k
  have hrot_len_k : (cycleRotate p k).length = p.length := by
    unfold cycleRotate; rw [List.length_append, List.length_drop, List.length_take]; omega
  have hrot_len_k' : (cycleRotate p k').length = p.length := by
    unfold cycleRotate; rw [List.length_append, List.length_drop, List.length_take]; omega
  rcases lt_or_gt_of_ne hne with hlt' | hgt'
  · have h1 := hval'.2 (k - k') (by omega) (by rw [hrot_len_k']; omega)
    rw [take_cycleRotate p k' (k - k') (le_of_lt hk') (by omega), if_pos (by omega)] at h1
    rw [show k' + (k - k') = k by omega] at h1
    have h2 := hval.2 (p.length - (k - k')) (by omega) (by rw [hrot_len_k]; omega)
    rw [take_cycleRotate p k (p.length - (k - k')) (le_of_lt hk) (by omega)] at h2
    split_ifs at h2 with hle2
    · have hk'0 : k' = 0 := by omega
      subst hk'0
      rw [show k + (p.length - (k - 0)) = p.length by omega, List.take_length, hnet] at h2
      simp [netBal] at h1
      omega
    · rw [show p.length - (k - k') - (p.length - k) = k' by omega, hnet] at h2
      omega
  · have h1 := hval.2 (k' - k) (by omega) (by rw [hrot_len_k]; omega)
    rw [take_cycleRotate p k (k' - k) (le_of_lt hk) (by omega), if_pos (by omega)] at h1
    rw [show k + (k' - k) = k' by omega] at h1
    have h2 := hval'.2 (p.length - (k' - k)) (by omega) (by rw [hrot_len_k']; omega)
    rw [take_cycleRotate p k' (p.length - (k' - k)) (le_of_lt hk') (by omega)] at h2
    split_ifs at h2 with hle2
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [show k' + (p.length - (k' - 0)) = p.length by omega, List.take_length, hnet] at h2
      simp [netBal] at h1
      omega
    · rw [show p.length - (k' - k) - (p.length - k') = k by omega, hnet] at h2
      omega

/-! ### Part 2: Catalan Counting of EML Trees and Valid Binary Programs -/

/-- The `Finset` of all `EmlTree`s with exactly `n` gates, built by Catalan recursion. -/
def emlTreesOfGates : Nat → Finset EmlTree
  | 0 => {.one}
  | n + 1 =>
    (Finset.antidiagonal n).attach.biUnion fun ⟨p, hp⟩ =>
      have _ : p.1 < n + 1 := by have := Finset.mem_antidiagonal.mp hp; omega
      have _ : p.2 < n + 1 := by have := Finset.mem_antidiagonal.mp hp; omega
      (emlTreesOfGates p.1 ×ˢ emlTreesOfGates p.2).image fun ab => EmlTree.eml ab.1 ab.2

theorem mem_emlTreesOfGates {n : Nat} {t : EmlTree} :
    t ∈ emlTreesOfGates n ↔ t.gates = n := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases n with
    | zero =>
      cases t with
      | one => simp [emlTreesOfGates, EmlTree.gates]
      | eml a b => simp [emlTreesOfGates, EmlTree.gates]
    | succ m =>
      simp only [emlTreesOfGates, Finset.mem_biUnion, Finset.mem_attach, true_and,
        Finset.mem_image, Finset.mem_product, Subtype.exists, Finset.mem_antidiagonal, Prod.exists]
      constructor
      · rintro ⟨i, j, hij, a, b, ⟨ha, hb⟩, rfl⟩
        rw [ih i (by omega)] at ha
        rw [ih j (by omega)] at hb
        simp only [EmlTree.gates]
        omega
      · intro hg
        cases t with
        | one => simp [EmlTree.gates] at hg
        | eml a b =>
          simp only [EmlTree.gates] at hg
          refine ⟨a.gates, b.gates, by omega, a, b, ?_, rfl⟩
          exact ⟨(ih a.gates (by omega)).mpr rfl, (ih b.gates (by omega)).mpr rfl⟩

/-- The number of `n`-gate EML syntax trees equals the `n`-th Catalan number `catalan n`. -/
theorem card_emlTreesOfGates (n : Nat) :
    (emlTreesOfGates n).card = catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [emlTreesOfGates]
    | succ m =>
      rw [emlTreesOfGates, catalan_succ']
      rw [Finset.card_biUnion]
      · rw [← Finset.sum_attach (Finset.antidiagonal m)]
        refine Finset.sum_congr rfl fun ⟨p, hp⟩ _ => ?_
        have hsum := Finset.mem_antidiagonal.mp hp
        rw [Finset.card_image_of_injective]
        · rw [Finset.card_product, ih p.1 (by omega), ih p.2 (by omega)]
        · intro x y hxy
          injection hxy with h1 h2
          exact Prod.ext h1 h2
      · intro ⟨p, _⟩ _ ⟨q, _⟩ _ hpq
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro t ht1 ht2
        simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at ht1 ht2
        rcases ht1 with ⟨a1, b1, ⟨ha1, hb1⟩, rfl⟩
        rcases ht2 with ⟨a2, b2, ⟨ha2, hb2⟩, heq⟩
        injection heq with h1 h2
        subst h1; subst h2
        rw [mem_emlTreesOfGates] at ha1 ha2 hb1 hb2
        apply hpq
        exact Subtype.ext (Prod.ext (ha1.symm.trans ha2) (hb1.symm.trans hb2))

/-- The `Finset` of all valid binary EML programs of length `K = 2 * n + 1`. -/
def validProgramsOfGates (n : Nat) : Finset (List Bool) :=
  (emlTreesOfGates n).map ⟨EmlTree.toRpn, toRpn_injective⟩

theorem mem_validProgramsOfGates {n : Nat} {p : List Bool} :
    p ∈ validProgramsOfGates n ↔ IsValidProgram p ∧ p.length = 2 * n + 1 := by
  unfold validProgramsOfGates
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_emlTreesOfGates]
  constructor
  · rintro ⟨t, rfl, rfl⟩
    exact ⟨toRpn_valid t, toRpn_length t⟩
  · rintro ⟨hp, hlen⟩
    refine ⟨fromRpn p hp, ?_, toRpn_fromRpn p hp⟩
    have hl := toRpn_length (fromRpn p hp)
    rw [toRpn_fromRpn p hp] at hl
    omega

/-- **Catalan enumeration of valid EML programs** (`docs/binary.md`):
    there are exactly `catalan n` valid binary EML programs of length `K = 2 * n + 1`. -/
theorem card_validProgramsOfGates (n : Nat) :
    (validProgramsOfGates n).card = catalan n := by
  unfold validProgramsOfGates
  rw [Finset.card_map, card_emlTreesOfGates]

end Eml.CycleLemma
