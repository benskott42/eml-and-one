/-
  Certificates in the calculator's own semantics, `EmlExt` (`ln 0 = −∞`).

  `certifyExt` runs the symbolic gate of `Eml.Cert.certify` on finite values and
  adds the two infinities of `EmlExt`: `ln 0 = −∞` when the argument is the symbol
  `0`, `exp(−∞) = 0`, `ln(+∞) = +∞`, and the `extSub` table (`x − (−∞) = +∞`, …).
  It is proved sound once (`certifyExt_sound`):

    certifyExt bits = some x  →  evalRpn (EmlExt.finite 1) extEml bits [] = some [x.denote]

  so a circuit that uses `ln 0` is certified by `certifyExt_sound (by decide)`.
  A `ln` argument that is neither the symbol `0` nor provably nonzero is refused.
  When `certify` succeeds, `certifyExt` returns the same value (no gate meets `0`).

  The TypeScript port is `certifyRpnForLeanExt` in `lib/eml/leanCert.ts`; the bridge
  (`scripts/lean-bridge-check.ts`) cross-checks the two on 237 programs.

  Zero `sorry`, zero custom axioms.
-/
import Eml.Cert

namespace Eml.Cert

open Eml Eml.Binary Eml.Extended

/-- Symbolic `EmlExt` values: a finite `Sym`, or a phase-free infinity. -/
inductive XSym where
  | fin (s : Sym)
  | posInf
  | negInf
  deriving DecidableEq, Repr

noncomputable def XSym.denote : XSym → EmlExt
  | .fin s => .finite s.denote
  | .posInf => .posInf
  | .negInf => .negInf

/-- `extExp`: `exp(+∞) = +∞`, `exp(−∞) = 0`. -/
def xExp : XSym → XSym
  | .fin s => .fin (rExp s)
  | .posInf => .posInf
  | .negInf => .fin (.int 0)

theorem xExp_sound (a : XSym) : (xExp a).denote = extExp a.denote := by
  cases a with
  | fin s => simp only [xExp, XSym.denote, extExp, rExp_sound]
  | posInf => rfl
  | negInf => simp [xExp, XSym.denote, extExp, Sym.denote]

/-- `extLowerLog`: `ln 0 = −∞` for the symbol `0`, `ln(+∞) = +∞`; a finite argument
    must otherwise be provably nonzero, and `ln(−∞)` (`nan`) is refused. -/
def xLn : XSym → Option XSym
  | .fin s =>
    if s = .int 0 then some .negInf else if nz s = true then (rLn s).map .fin else none
  | .posInf => some .posInf
  | .negInf => none

theorem xLn_sound {b l : XSym} (h : xLn b = some l) : l.denote = extLowerLog b.denote := by
  cases b with
  | fin s =>
    by_cases h0 : s = .int 0
    · subst h0
      simp only [xLn, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [XSym.denote, extLowerLog, Sym.denote]
    · by_cases hn : nz s = true
      · simp only [xLn, h0, ↓reduceIte, hn, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp only [XSym.denote, extLowerLog, nz_sound s hn, ↓reduceIte, rLn_sound s hv]
      · simp only [xLn, h0, ↓reduceIte, hn, Bool.false_eq_true, reduceCtorEq] at h
  | posInf =>
    simp only [xLn, Option.some.injEq] at h
    subst h
    rfl
  | negInf => simp [xLn] at h

/-- `extSub`, refusing the indeterminate `∞ − ∞`. -/
def xSub : XSym → XSym → Option XSym
  | .fin a, .fin b => some (.fin (rSub a b))
  | .fin _, .negInf => some .posInf
  | .fin _, .posInf => some .negInf
  | .posInf, .fin _ => some .posInf
  | .negInf, .fin _ => some .negInf
  | .posInf, .negInf => some .posInf
  | .negInf, .posInf => some .negInf
  | _, _ => none

theorem xSub_sound {a b c : XSym} (h : xSub a b = some c) :
    c.denote = extSub a.denote b.denote := by
  cases a with
  | fin x =>
    cases b with
    | fin y =>
      simp only [xSub, Option.some.injEq] at h
      subst h
      simp only [XSym.denote, extSub, rSub_sound]
    | posInf => simp only [xSub, Option.some.injEq] at h; subst h; rfl
    | negInf => simp only [xSub, Option.some.injEq] at h; subst h; rfl
  | posInf =>
    cases b with
    | fin y => simp only [xSub, Option.some.injEq] at h; subst h; rfl
    | posInf => simp [xSub] at h
    | negInf => simp only [xSub, Option.some.injEq] at h; subst h; rfl
  | negInf =>
    cases b with
    | fin y => simp only [xSub, Option.some.injEq] at h; subst h; rfl
    | posInf => simp only [xSub, Option.some.injEq] at h; subst h; rfl
    | negInf => simp [xSub] at h

/-- One `extEml` gate: `extSub (extExp a) (extLowerLog b)`. -/
def xGate (a b : XSym) : Option XSym := (xLn b).bind (xSub (xExp a))

theorem xGate_sound {a b c : XSym} (h : xGate a b = some c) :
    c.denote = extEml a.denote b.denote := by
  unfold xGate at h
  obtain ⟨l, hl, hc⟩ := Option.bind_eq_some_iff.mp h
  rw [xSub_sound hc, xExp_sound, xLn_sound hl]
  rfl

def optXGate : Option XSym → Option XSym → Option XSym
  | some a, some b => xGate a b
  | _, _ => none

/-- The `EmlExt` certificate checker: symbolic RPN evaluation of a bit program. -/
def certifyExt (bits : List Bool) : Option XSym :=
  match evalRpn (some (XSym.fin (.int 1))) optXGate bits [] with
  | some [x] => x
  | _ => none

/-- Pairs (symbolic, `EmlExt`) whose symbolic value, when present, is the true value. -/
def XGood : Type := { t : Option XSym × EmlExt // ∀ x, t.1 = some x → t.2 = x.denote }

noncomputable def xGoodOne : XGood :=
  ⟨(some (.fin (.int 1)), .finite 1), by
    intro x hx
    cases hx
    simp [XSym.denote, Sym.denote]⟩

noncomputable def xGoodOp (x y : XGood) : XGood :=
  ⟨(optXGate x.1.1 y.1.1, extEml x.1.2 y.1.2), by
    obtain ⟨⟨ox, wx⟩, hx⟩ := x
    obtain ⟨⟨oy, wy⟩, hy⟩ := y
    intro c hc
    cases ox with
    | none => simp [optXGate] at hc
    | some a =>
      cases oy with
      | none => simp [optXGate] at hc
      | some b =>
        simp only [optXGate] at hc
        have ha : wx = a.denote := hx a rfl
        have hb : wy = b.denote := hy b rfl
        show extEml wx wy = c.denote
        rw [ha, hb]
        exact (xGate_sound hc).symm⟩

/-- **`EmlExt` certificate soundness.** If the checker returns `x`, the program
    evaluates to `x.denote` in the calculator's `ln 0 = −∞` semantics. -/
theorem certifyExt_sound {bits : List Bool} {x : XSym} (h : certifyExt bits = some x) :
    evalRpn (EmlExt.finite 1) extEml bits [] = some [x.denote] := by
  have h1 := evalRpn_map (fun g : XGood => g.1.1) xGoodOne xGoodOp (some (XSym.fin (.int 1)))
    optXGate rfl (fun _ _ => rfl) bits []
  have h2 := evalRpn_map (fun g : XGood => g.1.2) xGoodOne xGoodOp (EmlExt.finite 1) extEml
    rfl (fun _ _ => rfl) bits []
  simp only [List.map_nil] at h1 h2
  generalize evalRpn xGoodOne xGoodOp bits [] = R at h1 h2
  unfold certifyExt at h
  rw [h1] at h
  rw [h2]
  rcases R with _ | _ | ⟨g, _ | ⟨g', l⟩⟩
  · simp at h
  · simp at h
  · simp only [Option.map_some, List.map_cons, List.map_nil] at h ⊢
    rw [g.2 x h]
  · simp at h

/-! ### Sanity checks (kernel-evaluated certificates) -/

/-- `−∞ = 11111E1EEEE` (K 11): `ln 0` itself. -/
example : certifyExt [true, true, true, true, true, false, true, false, false, false, false] =
    some .negInf := by decide

/-- `−1 = 11111E1EEEE11EE` (K 15), through `exp(−∞) = 0`. -/
example : evalRpn (EmlExt.finite 1) extEml
    [true, true, true, true, true, false, true, false, false, false, false, true, true, false, false]
    [] = some [.finite (-1)] := by
  have := certifyExt_sound (bits := [true, true, true, true, true, false, true, false, false, false,
    false, true, true, false, false]) (x := .fin (.int (-1))) (by decide)
  simpa [XSym.denote, Sym.denote] using this

end Eml.Cert
