/-
  Certificates in `EmlDir` (directed infinities and signed zero).

  `certify_sound_dir`: when `Eml.Cert.certify` certifies a constant program, it also
  evaluates to the same finite value in `EmlDir`. The certificate never meets `ln 0`
  (every `ln` argument is proved nonzero), and on finite operands with a nonzero right
  argument `dirEml` is `eml` (`dirEml_finite`). So every certified constant word, such
  as the `3` word, has its `EmlDir` value by kernel computation, for use inside the
  compiler's circuits (`Eml.AppOps`).

  Zero `sorry`, zero custom axioms.
-/
import Eml.Cert
import Eml.DirectedInf

namespace Eml.Cert

open Eml Eml.Binary Eml.DirectedInf

/-- Pairs (symbolic, `EmlDir`) whose symbolic value, when present, is the true value. -/
def GoodD : Type := { t : Option Sym × EmlDir // ∀ s, t.1 = some s → t.2 = .finite s.denote }

noncomputable def goodDOne : GoodD :=
  ⟨(some (.int 1), .finite 1), by
    intro s hs
    cases hs
    simp [Sym.denote]⟩

noncomputable def goodDOp (x y : GoodD) : GoodD :=
  ⟨(optGate x.1.1 y.1.1, dirEml x.1.2 y.1.2), by
    obtain ⟨⟨ox, wx⟩, hx⟩ := x
    obtain ⟨⟨oy, wy⟩, hy⟩ := y
    intro c hc
    cases ox with
    | none => simp [optGate] at hc
    | some a =>
      cases oy with
      | none => simp [optGate] at hc
      | some b =>
        simp only [optGate] at hc
        obtain ⟨hb, hcv⟩ := gate_sound hc
        have ha' : wx = .finite a.denote := hx a rfl
        have hb' : wy = .finite b.denote := hy b rfl
        show dirEml wx wy = _
        rw [ha', hb', dirEml_finite hb, hcv]⟩

/-- **`EmlDir` certificate soundness.** A certified constant program evaluates to the
    certificate's value in `EmlDir` as well. -/
theorem certify_sound_dir {bits : List Bool} {s : Sym} (h : certify bits = some s) :
    evalRpn (EmlDir.finite 1) dirEml bits [] = some [.finite s.denote] := by
  have h1 := evalRpn_map (fun g : GoodD => g.1.1) goodDOne goodDOp (some (Sym.int 1)) optGate
    rfl (fun _ _ => rfl) bits []
  have h2 := evalRpn_map (fun g : GoodD => g.1.2) goodDOne goodDOp (EmlDir.finite 1) dirEml
    rfl (fun _ _ => rfl) bits []
  simp only [List.map_nil] at h1 h2
  generalize evalRpn goodDOne goodDOp bits [] = R at h1 h2
  unfold certify at h
  rw [h1] at h
  rw [h2]
  rcases R with _ | _ | ⟨g, _ | ⟨g', l⟩⟩
  · simp at h
  · simp at h
  · simp only [Option.map_some, List.map_cons, List.map_nil] at h ⊢
    rw [g.2 s h]
  · simp at h

/-- The `EmlDir` value of a constant program (`nan` if it does not leave one value). -/
noncomputable def dirConst (bits : List Bool) : EmlDir :=
  match evalRpn (EmlDir.finite 1) dirEml bits [] with
  | some [v] => v
  | _ => .nan

theorem dirConst_eq {bits : List Bool} {s : Sym} (h : certify bits = some s) :
    dirConst bits = .finite s.denote := by
  unfold dirConst
  rw [certify_sound_dir h]

end Eml.Cert
