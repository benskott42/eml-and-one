/-
  Certificates in `EmlDir` (directed infinities and signed zero).

  `certify_sound_dir`: when `Eml.Cert.certify` certifies a constant program, it also
  evaluates to the same finite value in `EmlDir`. The certificate never meets `ln 0`
  (every `ln` argument is proved nonzero), and on finite operands with a nonzero right
  argument `dirEml` is `eml` (`dirEml_finite`). So every certified constant word, such
  as the `3` word, has its `EmlDir` value by kernel computation, for use inside the
  compiler's circuits (`Eml.AppOps`).

  `certifyDir` is the directed checker: the same bit programs, evaluated in `EmlDir`,
  with infinity phases kept in units of `π/2` (`DSym`). It returns `none` when a zero
  test or a phase is not decided, which is sound and stricter than the value. The
  current boxes do not decide `π` or `10`.

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

/-! ### Directed certificates, with phases in units of `π/2`

`certify` refuses every program that meets `ln 0`. The trigonometric constants (`i`, `−i`,
`1/2`, `π`, …) all do. `certifyDir` evaluates those programs in `EmlDir`: a finite result
keeps its `Sym`, and an infinity keeps its direction when the angle is an exact multiple
of `π/2`. An unknown angle is `none`. The checker returns `none` only when a step is `nan`
or when a zero test cannot be decided. -/

/-- A symbolic `EmlDir` value. `k` in `posInf`/`negInf`/`dirInf` is the angle as a multiple
    of `π/2`; `none` is an angle the checker did not determine. -/
inductive DSym where
  | fin (s : Sym)
  | negZero
  | posInf (k : Option Int)
  | negInf (k : Option Int)
  | dirInf (k : Option Int)
  deriving DecidableEq, Repr

/-- `θ` is the angle recorded by `k`, or any angle when `k` is unknown. -/
def Phase : Option Int → ℝ → Prop
  | some k, θ => θ = (k : ℝ) * (Real.pi / 2)
  | none, _ => True

/-- What an `EmlDir` value must be to realise a `DSym`. -/
def Den : DSym → EmlDir → Prop
  | .fin s, v => v = .finite s.denote
  | .negZero, v => v = .negZero
  | .posInf k, v => ∃ θ, v = .posInf θ ∧ Phase k θ
  | .negInf k, v => ∃ θ, v = .negInf θ ∧ Phase k θ
  | .dirInf k, v => ∃ θ, v = .dirInf θ ∧ Phase k θ

/-- `2·Im/π` when the imaginary part is structurally a multiple of `π/2`. -/
def imH : Sym → Option Int
  | .int _ => some 0
  | .e => some 0
  | .ipi k => some (2 * k)
  | .neg a => (imH a).map fun k => -k
  | .add a b => (imH a).bind fun ka => (imH b).map fun kb => ka + kb
  | .sub a b => (imH a).bind fun ka => (imH b).map fun kb => ka - kb
  | .exp a => if imH a = some 0 then some 0 else none
  | .ln _ => none

theorem imH_sound : ∀ {s : Sym} {k : Int}, imH s = some k → s.denote.im = (k : ℝ) * (Real.pi / 2)
  | .int n, k, h => by
      simp only [imH, Option.some.injEq] at h
      subst h
      simp [Sym.denote]
  | .e, k, h => by
      simp only [imH, Option.some.injEq] at h
      subst h
      simp [Sym.denote, ← Complex.ofReal_one, ← Complex.ofReal_exp, Complex.ofReal_im]
  | .ipi n, k, h => by
      simp only [imH, Option.some.injEq] at h
      subst h
      simp [Sym.denote, mul_assoc]
      ring_nf
  | .neg a, k, h => by
      simp only [imH, Option.map_eq_some_iff] at h
      obtain ⟨ka, ha, rfl⟩ := h
      rw [Sym.denote, Complex.neg_im, imH_sound ha, Int.cast_neg]
      ring_nf
  | .add a b, k, h => by
      simp only [imH, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨ka, ha, kb, hb, rfl⟩ := h
      rw [Sym.denote, Complex.add_im, imH_sound ha, imH_sound hb, Int.cast_add]
      ring_nf
  | .sub a b, k, h => by
      simp only [imH, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨ka, ha, kb, hb, rfl⟩ := h
      rw [Sym.denote, Complex.sub_im, imH_sound ha, imH_sound hb, Int.cast_sub]
      ring_nf
  | .exp a, k, h => by
      simp only [imH] at h
      split_ifs at h with h0
      · simp only [Option.some.injEq] at h
        subst h
        have him : a.denote.im = 0 := by simpa using imH_sound h0
        rw [Sym.denote, Complex.exp_im, him, Real.sin_zero, mul_zero]
        simp
  | .ln _, _, h => by simp [imH] at h

theorem phase_imH (s : Sym) : Phase (imH s) s.denote.im := by
  cases h : imH s with
  | none => simp [Phase]
  | some k =>
      simp only [Phase]
      exact imH_sound h

/-- `Im(lowerLog(k·iπ))` is `±π/2`, the sign of `k`. -/
theorem lowerLog_ipi_im {k : Int} (hk : k ≠ 0) :
    (lowerLog ((k : ℂ) * (Real.pi * Complex.I))).im =
      (if 0 < k then (1 : ℝ) else -1) * (Real.pi / 2) := by
  have hre : ((k : ℂ) * (Real.pi * Complex.I)).re = 0 := by simp
  have hnot : ¬ isNegReal ((k : ℂ) * (Real.pi * Complex.I)) := by
    intro hneg
    have hlt := hneg.1
    rw [hre] at hlt
    exact lt_irrefl (0 : ℝ) hlt
  rw [lowerLog_eq_log_of_not_isNegReal hnot, Complex.log_im]
  by_cases hk0 : 0 < k
  · have hr : (0 : ℝ) < (k : ℝ) * Real.pi := mul_pos (Int.cast_pos.mpr hk0) Real.pi_pos
    have harg : Complex.arg ((k : ℂ) * (Real.pi * Complex.I)) = Complex.arg Complex.I := by
      have hcast : (k : ℂ) * (Real.pi * Complex.I) =
          (((k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.arg_real_mul Complex.I hr, Complex.arg_I]
    simp [hk0, harg]
  · have hkneg : k < 0 := lt_of_le_of_ne (not_lt.mp hk0) hk
    have hr : (0 : ℝ) < ((-k : Int) : ℝ) * Real.pi :=
      mul_pos (Int.cast_pos.mpr (neg_pos.mpr hkneg)) Real.pi_pos
    have hcast : (k : ℂ) * (Real.pi * Complex.I) =
        ((((-k : Int) : ℝ) * Real.pi : ℝ) : ℂ) * (-Complex.I) := by
      push_cast; ring
    have harg : Complex.arg ((k : ℂ) * (Real.pi * Complex.I)) = Complex.arg (-Complex.I) := by
      rw [hcast, Complex.arg_real_mul (-Complex.I) hr, Complex.arg_neg_I]
    simp [hk0, harg]

def phaseSub (p q : Option Int) : Option Int :=
  match p, q with
  | some x, some y => some (x - y)
  | _, _ => none

theorem phase_sub {p q : Option Int} {θ φ : ℝ} (hp : Phase p θ) (hq : Phase q φ) :
    Phase (phaseSub p q) (θ - φ) := by
  cases p with
  | none => cases q <;> simp [phaseSub, Phase]
  | some x =>
      cases q with
      | none => simp [phaseSub, Phase]
      | some y =>
          simp only [phaseSub, Phase] at hp hq ⊢
          rw [hp, hq, Int.cast_sub]
          ring_nf

theorem phase_neg {p : Option Int} {θ : ℝ} (hp : Phase p θ) :
    Phase (p.map fun k => -k) (-θ) := by
  cases p with
  | none => simp [Phase]
  | some k =>
      simp only [Phase, Option.map] at hp ⊢
      rw [hp, Int.cast_neg]
      ring_nf

private theorem angle_split (k : Int) :
    (k : ℝ) * (Real.pi / 2) =
      ((k % 4 : Int) : ℝ) * (Real.pi / 2) + ((k / 4 : Int) : ℝ) * (2 * Real.pi) := by
  have h := Int.emod_add_mul_ediv k 4
  have h' : (k : ℝ) = ((k % 4 : Int) : ℝ) + 4 * ((k / 4 : Int) : ℝ) := by
    exact_mod_cast h.symm
  rw [h']; ring

private theorem cos_reduced (k : Int) :
    Real.cos ((k : ℝ) * (Real.pi / 2)) = Real.cos (((k % 4 : Int) : ℝ) * (Real.pi / 2)) := by
  rw [angle_split k, Real.cos_add_int_mul_two_pi]

private theorem sin_reduced (k : Int) :
    Real.sin ((k : ℝ) * (Real.pi / 2)) = Real.sin (((k % 4 : Int) : ℝ) * (Real.pi / 2)) := by
  rw [angle_split k, Real.sin_add_int_mul_two_pi]

private theorem emod_four (k : Int) : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by decide)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by decide)
  omega

theorem cos_half_turn (k : Int) :
    (Real.cos ((k : ℝ) * (Real.pi / 2)) < 0 ↔ k % 4 = 2) ∧
    (0 < Real.cos ((k : ℝ) * (Real.pi / 2)) ∧ Real.sin ((k : ℝ) * (Real.pi / 2)) = 0 ↔ k % 4 = 0) ∧
    (Real.cos ((k : ℝ) * (Real.pi / 2)) < 0 ∧ Real.sin ((k : ℝ) * (Real.pi / 2)) = 0 ↔ k % 4 = 2) := by
  rw [cos_reduced k, sin_reduced k]
  rcases emod_four k with h | h | h | h
  · rw [h]; simp [Real.cos_zero, Real.sin_zero]
  · rw [h]
    have he : ((1 : Int) : ℝ) * (Real.pi / 2) = Real.pi / 2 := by ring
    rw [he, Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  · rw [h]
    have he : ((2 : Int) : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [he, Real.cos_pi, Real.sin_pi]
    norm_num
  · rw [h]
    have he : ((3 : Int) : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi := by ring
    rw [he, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num

/-- `true` when `s` is the integer `0`, `false` when `s` is provably nonzero. -/
def symKnownZero (s : Sym) : Option Bool :=
  if s = .int 0 then some true else if nz s = true then some false else none

def dExp : DSym → Option DSym
  | .fin s => some (.fin (rExp s))
  | .negZero => some (.fin (.int 1))
  | .posInf k => some (.dirInf k)
  | .negInf (some k) => some (if k % 4 = 2 then .negZero else .fin (.int 0))
  | .negInf none => none
  | .dirInf (some k) =>
      if k % 4 = 0 then some (.dirInf (some 0))
      else if k % 4 = 2 then some (.fin (.int 0))
      else none
  | .dirInf none => none

def dLn : DSym → Option DSym
  | .fin s =>
      if s = .int 0 then some (.negInf (some 0))
      else match rLn s, nz s with
        | some l, true => some (.fin l)
        | _, _ => none
  | .negZero => some (.negInf (some (-2)))
  | .posInf _ => some (.posInf (some 0))
  | .negInf (some k) => some (.posInf (some (if 0 < k then 2 else -2)))
  | .negInf none => none
  | .dirInf (some k) => some (.posInf (some (if k % 4 = 2 then -2 else 0)))
  | .dirInf none => none

def dSub : DSym → DSym → Option DSym
  | .fin a, .fin b => some (.fin (rSub a b))
  | .fin a, .negZero => some (.fin a)
  | .negZero, .fin b =>
      match symKnownZero b with
      | some true => some .negZero
      | some false => some (.fin (negOf b))
      | none => none
  | .negZero, .negZero => some (.fin (.int 0))
  | .fin a, .posInf q => some (.negInf (phaseSub (imH a) q))
  | .fin a, .negInf q => some (.posInf (phaseSub (imH a) q))
  | .fin a, .dirInf (some k) =>
      if k % 4 = 0 then some (.negInf (imH a))
      else if k % 4 = 2 then some (.posInf (imH a))
      else none
  | .fin _, .dirInf none => none
  | .negZero, .posInf q => some (.negInf (q.map fun k => -k))
  | .negZero, .negInf q => some (.posInf (q.map fun k => -k))
  | .negZero, .dirInf _ => none
  | .posInf p, .fin b => some (.posInf (phaseSub p (imH b)))
  | .negInf p, .fin b => some (.negInf (phaseSub p (imH b)))
  | .posInf p, .negZero => some (.posInf p)
  | .negInf p, .negZero => some (.negInf p)
  | .posInf p, .negInf q => some (.posInf (phaseSub p q))
  | .negInf p, .posInf q => some (.negInf (phaseSub p q))
  | .dirInf p, .fin _ => some (.dirInf p)
  | .dirInf p, .negZero => some (.dirInf p)
  | .dirInf (some k), .negInf _ => if k % 4 = 0 then some (.posInf (some 0)) else none
  | .dirInf none, .negInf _ => none
  | _, _ => none

theorem dExp_sound {a ae : DSym} {v : EmlDir} (ha : Den a v) (h : dExp a = some ae) :
    Den ae (dirExp v) := by
  cases a with
  | fin s =>
      simp only [Den] at ha
      subst ha
      simp only [dExp, Option.some.injEq] at h
      subst h
      simp [Den, dirExp, rExp_sound]
  | negZero =>
      simp only [Den] at ha
      subst ha
      simp only [dExp, Option.some.injEq] at h
      subst h
      simp [Den, dirExp, Sym.denote]
  | posInf k =>
      simp only [dExp, Option.some.injEq] at h
      subst h
      rcases ha with ⟨θ, rfl, hp⟩
      exact ⟨θ, by simp [dirExp], hp⟩
  | negInf k =>
      cases k with
      | none => simp [dExp] at h
      | some k =>
          rcases ha with ⟨θ, rfl, hp⟩
          have hθ : θ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
          have hc := (cos_half_turn k).1
          simp only [dExp, Option.some.injEq] at h
          by_cases hk : k % 4 = 2
          · simp only [hk, ↓reduceIte] at h
            subst h
            have hcos : Real.cos θ < 0 := by simpa [hθ] using hc.mpr hk
            simp [Den, dirExp, hcos]
          · simp only [hk, ↓reduceIte] at h
            subst h
            have hcos : ¬ Real.cos θ < 0 := by simpa [hθ] using hc.not.mpr hk
            simp [Den, dirExp, hcos, Sym.denote]
  | dirInf k =>
      cases k with
      | none => simp [dExp] at h
      | some k =>
          rcases ha with ⟨θ, rfl, hp⟩
          have hθ : θ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
          have hpos := (cos_half_turn k).2.1
          have hneg := (cos_half_turn k).2.2
          simp only [dExp] at h
          by_cases h0 : k % 4 = 0
          · rw [if_pos h0] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hc, hs⟩ := hpos.mpr h0
            simp [Den, dirExp, hθ, hc, hs, Phase]
          · rw [if_neg h0] at h
            by_cases h2 : k % 4 = 2
            · rw [if_pos h2] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hc, hs⟩ := hneg.mpr h2
              have hcos : Real.cos θ < 0 := by simpa [hθ] using hc
              have hsin : Real.sin θ = 0 := by simpa [hθ] using hs
              have hng : ¬ 0 < Real.cos θ := lt_asymm hcos
              simp [Den, dirExp, hcos, hsin, hng, Sym.denote]
            · rw [if_neg h2] at h
              simp at h

theorem dLn_sound {a al : DSym} {v : EmlDir} (ha : Den a v) (h : dLn a = some al) :
    Den al (dirLowerLog v) := by
  cases a with
  | fin s =>
      simp only [Den] at ha
      subst ha
      simp only [dLn] at h
      by_cases hz : s = .int 0
      · rw [hz] at h ⊢
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        simp [Den, dirLowerLog, Phase, Sym.denote]
      · simp only [hz, ↓reduceIte] at h
        cases hr : rLn s with
        | none => simp [hr] at h
        | some l =>
            cases hnz : nz s with
            | false => simp [hr, hnz] at h
            | true =>
                simp only [hr, hnz, Option.some.injEq] at h
                subst h
                have hb := nz_sound s hnz
                simp [Den, dirLowerLog, hb, rLn_sound s hr]
  | negZero =>
      simp only [Den] at ha
      subst ha
      simp only [dLn, Option.some.injEq] at h
      subst h
      refine ⟨-Real.pi, by simp [dirLowerLog], ?_⟩
      simp [Phase]; ring
  | posInf k =>
      simp only [dLn, Option.some.injEq] at h
      subst h
      rcases ha with ⟨θ, rfl, _⟩
      refine ⟨0, by simp [dirLowerLog], ?_⟩
      simp [Phase]
  | negInf k =>
      cases k with
      | none => simp [dLn] at h
      | some k =>
          rcases ha with ⟨θ, rfl, hp⟩
          have hθ : θ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
          simp only [dLn, Option.some.injEq] at h
          subst h
          by_cases hk : 0 < k
          · have hθp : 0 < θ := by
              rw [hθ]
              exact mul_pos (Int.cast_pos.mpr hk) (div_pos Real.pi_pos (by norm_num))
            refine ⟨Real.pi, by simp [dirLowerLog, hθp], ?_⟩
            simp [Phase, hk]; ring
          · have hθn : ¬ 0 < θ := by
              rw [hθ]
              exact not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr (not_lt.mp hk))
                (div_nonneg Real.pi_pos.le (by norm_num)))
            refine ⟨-Real.pi, by simp [dirLowerLog, hθn], ?_⟩
            simp [Phase, hk]; ring
  | dirInf k =>
      cases k with
      | none => simp [dLn] at h
      | some k =>
          rcases ha with ⟨θ, rfl, hp⟩
          have hθ : θ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
          have hc := (cos_half_turn k).1
          simp only [dLn, Option.some.injEq] at h
          subst h
          by_cases hk : k % 4 = 2
          · have hcos : Real.cos θ < 0 := by simpa [hθ] using hc.mpr hk
            refine ⟨-Real.pi, by simp [dirLowerLog, hcos], ?_⟩
            simp [Phase, hk]; ring
          · have hcos : ¬ Real.cos θ < 0 := by simpa [hθ] using hc.not.mpr hk
            refine ⟨0, by simp [dirLowerLog, hcos], ?_⟩
            simp [Phase, hk]

theorem dSub_sound {a b c : DSym} {va vb : EmlDir}
    (ha : Den a va) (hb : Den b vb) (h : dSub a b = some c) : Den c (dirSub va vb) := by
  cases a <;> cases b <;> simp only [dSub] at h
  case fin.fin s t =>
    simp only [Den] at ha hb
    subst ha hb
    simp only [Option.some.injEq] at h
    subst h
    simp [Den, dirSub, rSub_sound]
  case fin.negZero s =>
    simp only [Den] at ha hb
    subst ha hb
    simp only [Option.some.injEq] at h
    subst h
    simp [Den, dirSub]
  case fin.posInf s q =>
    simp only [Den] at ha
    subst ha
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨s.denote.im - φ, by simp [dirSub], ?_⟩
    exact phase_sub (phase_imH s) hq
  case fin.negInf s q =>
    simp only [Den] at ha
    subst ha
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨s.denote.im - φ, by simp [dirSub], ?_⟩
    exact phase_sub (phase_imH s) hq
  case fin.dirInf s q =>
    cases q with
    | none => simp at h
    | some k =>
        simp only [Den] at ha
        subst ha
        rcases hb with ⟨φ, rfl, hp⟩
        dsimp only [dSub] at h
        have hφ : φ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
        have hpos := (cos_half_turn k).2.1
        have hneg := (cos_half_turn k).2.2
        by_cases h0 : k % 4 = 0
        · rw [if_pos h0] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hc, hs⟩ := hpos.mpr h0
          have hcos : 0 < Real.cos φ := by simpa [hφ] using hc
          have hsin : Real.sin φ = 0 := by simpa [hφ] using hs
          refine ⟨s.denote.im, by simp [dirSub, hcos, hsin], phase_imH s⟩
        · rw [if_neg h0] at h
          by_cases h2 : k % 4 = 2
          · rw [if_pos h2] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hc, hs⟩ := hneg.mpr h2
            have hcos : Real.cos φ < 0 := by simpa [hφ] using hc
            have hsin : Real.sin φ = 0 := by simpa [hφ] using hs
            have hle : Real.cos φ ≤ 0 := hcos.le
            refine ⟨s.denote.im, by simp [dirSub, hcos, hsin, hle], phase_imH s⟩
          · rw [if_neg h2] at h
            simp at h
  case negZero.fin t =>
    simp only [Den] at ha hb
    subst ha hb
    simp only [symKnownZero] at h
    by_cases ht : t = .int 0
    · rw [ht] at h ⊢
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      simp [Den, dirSub, Sym.denote]
    · simp only [ht, ↓reduceIte] at h
      cases hnz : nz t with
      | false => simp [hnz] at h
      | true =>
          simp only [hnz, ↓reduceIte, Option.some.injEq] at h
          subst h
          have hb0 := nz_sound t hnz
          simp [Den, dirSub, hb0, negOf_sound]
  case negZero.negZero =>
    simp only [Den] at ha hb
    subst ha hb
    simp only [Option.some.injEq] at h
    subst h
    simp [Den, dirSub, Sym.denote]
  case negZero.posInf q =>
    simp only [Den] at ha
    subst ha
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨-φ, by simp [dirSub], ?_⟩
    exact phase_neg hq
  case negZero.negInf q =>
    simp only [Den] at ha
    subst ha
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨-φ, by simp [dirSub], ?_⟩
    exact phase_neg hq
  case negZero.dirInf =>
    simp at h
  case posInf.fin p t =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨θ - t.denote.im, by simp [dirSub], ?_⟩
    exact phase_sub hp (phase_imH t)
  case posInf.negZero p =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨θ, by simp [dirSub], hp⟩
  case posInf.posInf =>
    simp at h
  case posInf.negInf p q =>
    rcases ha with ⟨θ, rfl, hp⟩
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨θ - φ, by simp [dirSub], ?_⟩
    exact phase_sub hp hq
  case posInf.dirInf =>
    simp at h
  case negInf.fin p t =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨θ - t.denote.im, by simp [dirSub], ?_⟩
    exact phase_sub hp (phase_imH t)
  case negInf.negZero p =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨θ, by simp [dirSub], hp⟩
  case negInf.posInf p q =>
    rcases ha with ⟨θ, rfl, hp⟩
    rcases hb with ⟨φ, rfl, hq⟩
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨θ - φ, by simp [dirSub], ?_⟩
    exact phase_sub hp hq
  case negInf.negInf =>
    simp at h
  case negInf.dirInf =>
    simp at h
  case dirInf.fin p t =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨θ, by simp [dirSub], hp⟩
  case dirInf.negZero p =>
    rcases ha with ⟨θ, rfl, hp⟩
    simp only [Den] at hb
    subst hb
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨θ, by simp [dirSub], hp⟩
  case dirInf.posInf =>
    simp at h
  case dirInf.negInf p q =>
    cases p with
    | none => simp at h
    | some k =>
        rcases ha with ⟨θ, rfl, hp⟩
        have hθ : θ = (k : ℝ) * (Real.pi / 2) := by simpa [Phase] using hp
        have hpos := (cos_half_turn k).2.1
        by_cases h0 : k % 4 = 0
        · simp only [h0, ↓reduceIte, Option.some.injEq] at h
          subst h
          have ⟨hc, hs⟩ := hpos.mpr h0
          rcases hb with ⟨φ, rfl, _⟩
          refine ⟨0, by simp [dirSub, hθ, hc, hs], ?_⟩
          simp [Phase]
        · simp [h0] at h
  case dirInf.dirInf =>
    simp at h

def dEml (a b : DSym) : Option DSym :=
  (dExp a).bind fun e => (dLn b).bind fun l => dSub e l

theorem dEml_sound {a b c : DSym} {va vb : EmlDir}
    (ha : Den a va) (hb : Den b vb) (h : dEml a b = some c) :
    Den c (dirEml va vb) := by
  cases he : dExp a with
  | none => simp [dEml, he] at h
  | some e =>
      cases hl : dLn b with
      | none => simp [dEml, he, hl] at h
      | some l =>
          simp [dEml, he, hl] at h
          simpa [dirEml] using dSub_sound (dExp_sound ha he) (dLn_sound hb hl) h

def dGate : Option DSym → Option DSym → Option DSym
  | some a, some b => dEml a b
  | _, _ => none

/-- Pairs whose symbolic value, when the checker accepts it, is the `EmlDir` value. -/
def GoodDir : Type := { t : Option DSym × EmlDir // ∀ x, t.1 = some x → Den x t.2 }

def goodDirOne : GoodDir :=
  ⟨(some (.fin (.int 1)), .finite 1), by
    intro x hx
    simp only [Option.some.injEq] at hx
    subst hx
    simp [Den, Sym.denote]⟩

noncomputable def goodDirOp (x y : GoodDir) : GoodDir :=
  ⟨(dGate x.1.1 y.1.1, dirEml x.1.2 y.1.2), by
    intro z hz
    cases hx : x.1.1 with
    | none => simp [dGate, hx] at hz
    | some a =>
        cases hy : y.1.1 with
        | none => simp [dGate, hx, hy] at hz
        | some b =>
            simp only [dGate, hx, hy] at hz
            exact dEml_sound (x.2 a hx) (y.2 b hy) hz⟩

/-- The directed certificate checker. -/
def certifyDir (bits : List Bool) : Option DSym :=
  match evalRpn (some (.fin (Sym.int 1))) dGate bits [] with
  | some [x] => x
  | _ => none

theorem certifyDir_sound {bits : List Bool} {x : DSym} (h : certifyDir bits = some x) :
    ∃ v, evalRpn (EmlDir.finite 1) dirEml bits [] = some [v] ∧ Den x v := by
  have h1 := evalRpn_map (fun g : GoodDir => g.1.1) goodDirOne goodDirOp
    (some (.fin (Sym.int 1))) dGate rfl (fun _ _ => rfl) bits []
  have h2 := evalRpn_map (fun g : GoodDir => g.1.2) goodDirOne goodDirOp
    (EmlDir.finite 1) dirEml rfl (fun _ _ => rfl) bits []
  simp only [List.map_nil] at h1 h2
  generalize evalRpn goodDirOne goodDirOp bits [] = R at h1 h2
  unfold certifyDir at h
  rw [h1] at h
  rw [h2]
  rcases R with _ | _ | ⟨g, _ | ⟨g', l⟩⟩
  · simp at h
  · simp at h
  · simp only [Option.map_some, List.map_cons, List.map_nil] at h ⊢
    exact ⟨g.1.2, rfl, g.2 x h⟩
  · simp at h

/-- One `true` bit pushes the seed `1`. -/
example : certifyDir [true] = some (.fin (.int 1)) := rfl

end Eml.Cert
