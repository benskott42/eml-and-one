/-
  Proof-carrying certificates for constant EML circuits.

  `certify : List Bool → Option Sym` is a small, computable symbolic evaluator
  for RPN bit programs (`true` = press `1`, `false` = press `EML`). It mirrors the
  calculator's deductive proof kernel (`lib/eml/proof.ts`) but is *proved sound
  once and for all* here (`certify_sound`):

    certify bits = some s  →
      evalRpn (1 : ℂ) eml bits [] = some [s.denote]   ∧
      evalRpn (EmlExt.finite 1) extEml bits [] = some [.finite s.denote]

  So a single circuit is certified by kernel computation alone
  (`certify_sound (by decide)`), with no per-circuit proof search. The second
  conjunct ties the value to the calculator's own `ln 0 = −∞` semantics: every
  `eml` gate's right operand is proved nonzero, so `ln 0` is never used and the
  `ℂ` and `EmlExt` evaluations agree.

  Besides its structural rules, the checker asks `Eml.CertBox` for proved
  fixed-point bounds on a value's real and imaginary parts, to show it nonzero,
  positive or negative real, or inside the strip `−π ≤ Im < π`.

  The TypeScript port in `lib/eml/leanCert.ts` is checked against this file on
  every program with K ≤ 13 plus every closed stored word (237 programs) by the generated
  `formal/lean/.lake/UiCrossCheck.lean` (`scripts/lean-bridge-check.ts`).

  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Eml.Basic
import Eml.Binary
import Eml.Extended
import Eml.CertBox
import Eml.CertBoxC

namespace Eml.Cert

open Eml Eml.Binary Eml.Extended

/-! ### Real / positive classification -/

/-- `e − n` with integer `n ≤ 2` (provably positive since `e > 2`). -/
def eSubSmall : Sym → Sym → Bool
  | .e, .int n => decide (n ≤ 2)
  | _, _ => false

/-- `2` = provably positive real, `1` = provably real, `0` = unknown. -/
def cls : Sym → Nat
  | .int n => if 0 < n then 2 else 1
  | .e => 2
  | .ipi _ => 0
  | .exp a => if 1 ≤ cls a then 2 else 0
  | .ln a => if cls a = 2 then 1 else 0
  | .neg a => if 1 ≤ cls a then 1 else 0
  | .add a b => if 1 ≤ cls a ∧ 1 ≤ cls b then 1 else 0
  | .sub a b => if eSubSmall a b = true then 2 else if 1 ≤ cls a ∧ 1 ≤ cls b then 1 else 0

theorem eSubSmall_spec {a b : Sym} (h : eSubSmall a b = true) :
    ∃ n : Int, a = .e ∧ b = .int n ∧ n ≤ 2 := by
  cases a <;> cases b <;> simp_all [eSubSmall]

theorem cls_sound (s : Sym) :
    (1 ≤ cls s → ∃ r : ℝ, s.denote = r) ∧ (cls s = 2 → ∃ r : ℝ, 0 < r ∧ s.denote = r) := by
  induction s with
  | int n =>
    refine ⟨fun _ => ⟨n, by simp [Sym.denote]⟩, fun h => ?_⟩
    by_cases hn : 0 < n
    · exact ⟨n, by exact_mod_cast hn, by simp [Sym.denote]⟩
    · simp [cls, hn] at h
  | e =>
    have hd : Sym.e.denote = ((Real.exp 1 : ℝ) : ℂ) := by
      simp [Sym.denote, Complex.ofReal_exp]
    exact ⟨fun _ => ⟨_, hd⟩, fun _ => ⟨_, Real.exp_pos 1, hd⟩⟩
  | ipi k => simp [cls]
  | exp a iha =>
    by_cases h1 : 1 ≤ cls a
    · obtain ⟨r, hr⟩ := iha.1 h1
      have hd : (Sym.exp a).denote = ((Real.exp r : ℝ) : ℂ) := by
        simp [Sym.denote, hr, Complex.ofReal_exp]
      exact ⟨fun _ => ⟨_, hd⟩, fun _ => ⟨_, Real.exp_pos r, hd⟩⟩
    · have h0 : cls (.exp a) = 0 := by simp only [cls]; rw [if_neg h1]
      simp [h0]
  | ln a iha =>
    by_cases h2 : cls a = 2
    · obtain ⟨r, hr0, hr⟩ := iha.2 h2
      have hd : (Sym.ln a).denote = ((Real.log r : ℝ) : ℂ) := by
        simp only [Sym.denote, hr]; exact lowerLog_ofReal_pos hr0
      have hc : cls (.ln a) = 1 := by simp only [cls]; rw [if_pos h2]
      refine ⟨fun _ => ⟨_, hd⟩, fun h => ?_⟩
      rw [hc] at h; exact absurd h (by decide)
    · have h0 : cls (.ln a) = 0 := by simp only [cls]; rw [if_neg h2]
      simp [h0]
  | neg a iha =>
    by_cases h1 : 1 ≤ cls a
    · obtain ⟨r, hr⟩ := iha.1 h1
      have hc : cls (.neg a) = 1 := by simp only [cls]; rw [if_pos h1]
      refine ⟨fun _ => ⟨-r, by simp [Sym.denote, hr]⟩, fun h => ?_⟩
      rw [hc] at h; exact absurd h (by decide)
    · have h0 : cls (.neg a) = 0 := by simp only [cls]; rw [if_neg h1]
      simp [h0]
  | add a b iha ihb =>
    by_cases h1 : 1 ≤ cls a ∧ 1 ≤ cls b
    · obtain ⟨r, hr⟩ := iha.1 h1.1
      obtain ⟨t, ht⟩ := ihb.1 h1.2
      have hc : cls (.add a b) = 1 := by simp only [cls]; rw [if_pos h1]
      refine ⟨fun _ => ⟨r + t, by simp [Sym.denote, hr, ht]⟩, fun h => ?_⟩
      rw [hc] at h; exact absurd h (by decide)
    · have h0 : cls (.add a b) = 0 := by simp only [cls]; rw [if_neg h1]
      simp [h0]
  | sub a b iha ihb =>
    by_cases hs : eSubSmall a b = true
    · obtain ⟨n, rfl, rfl, hn⟩ := eSubSmall_spec hs
      have hd : (Sym.sub .e (.int n)).denote = ((Real.exp 1 - n : ℝ) : ℂ) := by
        simp [Sym.denote, Complex.ofReal_exp]
      have hpos : (0 : ℝ) < Real.exp 1 - n := by
        have h27 := Real.exp_one_gt_d9
        have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
        linarith
      exact ⟨fun _ => ⟨_, hd⟩, fun _ => ⟨_, hpos, hd⟩⟩
    · by_cases h1 : 1 ≤ cls a ∧ 1 ≤ cls b
      · obtain ⟨r, hr⟩ := iha.1 h1.1
        obtain ⟨t, ht⟩ := ihb.1 h1.2
        have hc : cls (.sub a b) = 1 := by simp only [cls]; rw [if_neg hs, if_pos h1]
        refine ⟨fun _ => ⟨r - t, by simp [Sym.denote, hr, ht]⟩, fun h => ?_⟩
        rw [hc] at h; exact absurd h (by decide)
      · have h0 : cls (.sub a b) = 0 := by simp only [cls]; rw [if_neg hs, if_neg h1]
        simp [h0]

theorem cls_pos_ne_zero {s : Sym} (h : cls s = 2) : s.denote ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := (cls_sound s).2 h
  rw [hr]; exact_mod_cast hr0.ne'

/-! ### Provably nonzero (so `ln` of it is never `ln 0`) -/

/-- `e − n` for any integer `n`: never 0, since `2 < e < 3`. -/
def eSubInt : Sym → Sym → Bool
  | .e, .int _ => true
  | _, _ => false

theorem eSubInt_ne_zero {a b : Sym} (h : eSubInt a b = true) : a.denote - b.denote ≠ 0 := by
  cases a <;> cases b <;> simp_all [eSubInt]
  rename_i n
  show Complex.exp 1 - (n : ℂ) ≠ 0
  have hcast : Complex.exp (1 : ℂ) - (n : ℂ) = ((Real.exp 1 - n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp]; push_cast; rfl
  rw [hcast, Complex.ofReal_ne_zero, sub_ne_zero]
  intro h
  have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  rw [h] at h2 h3
  have : (2 : ℤ) < n := by exact_mod_cast h2
  have : n < (3 : ℤ) := by exact_mod_cast h3
  omega

/-- Structural nonzero test. -/
def nz0 : Sym → Bool
  | .int n => n != 0
  | .e => true
  | .ipi k => k != 0
  | .exp _ => true
  | .ln _ => false
  | .neg a => nz0 a
  | .add _ _ => false
  | .sub a b => eSubInt a b

theorem nz0_sound : ∀ s : Sym, nz0 s = true → s.denote ≠ 0
  | .int n, h => by simpa [nz0, Sym.denote] using h
  | .e, _ => Complex.exp_ne_zero _
  | .ipi k, h => by
      simp only [nz0, bne_iff_ne, ne_eq] at h
      simp [Sym.denote, h, Real.pi_ne_zero, Complex.I_ne_zero]
  | .exp _, _ => Complex.exp_ne_zero _
  | .ln _, h => by simp [nz0] at h
  | .neg a, h => by simpa [Sym.denote] using nz0_sound a h
  | .add _ _, h => by simp [nz0] at h
  | .sub a b, h => by simpa [Sym.denote] using eSubInt_ne_zero (by simpa [nz0] using h)

/-- Provably nonzero: structurally, or because the value's box excludes `0` (`CertBox`). -/
def nz (s : Sym) : Bool := nz0 s || boxNz s

theorem nz_sound (s : Sym) (h : nz s = true) : s.denote ≠ 0 := by
  unfold nz at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact nz0_sound s h
  · exact boxNz_sound h

/-! ### `exp` rules -/

/-- `exp (ln u) = u` needs only `u ≠ 0`: a positive real, or anything `nz` proves nonzero. -/
def lnInvOk (u : Sym) : Bool :=
  cls u == 2 || nz u

theorem lnInvOk_sound {u : Sym} (h : lnInvOk u = true) : u.denote ≠ 0 := by
  unfold lnInvOk at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact cls_pos_ne_zero h
  · exact nz_sound u h

def negOf : Sym → Sym
  | .int n => .int (-n)
  | .ipi k => .ipi (-k)
  | .neg u => u
  | v => .neg v

theorem negOf_sound (v : Sym) : (negOf v).denote = -v.denote := by
  cases v <;> simp [negOf, Sym.denote]

/-- `exp`, simplified: `exp 0`, `exp 1`, `exp(kiπ) = ±1`, `exp(ln u) = u`, and
    `exp(a ± kiπ) = ±exp a`. -/
def rExp : Sym → Sym
  | .int n => if n = 0 then .int 1 else if n = 1 then .e else .exp (.int n)
  | .ipi k => .int (if k % 2 = 0 then 1 else -1)
  | .ln u => if lnInvOk u = true then u else .exp (.ln u)
  | .sub a b =>
    match b with
    | .ipi k => if k % 2 = 0 then rExp a else negOf (rExp a)
    | _ => .exp (.sub a b)
  | .add a b =>
    match b with
    | .ipi k => if k % 2 = 0 then rExp a else negOf (rExp a)
    | _ => .exp (.add a b)
  | a => .exp a

theorem exp_ipi (k : Int) :
    Complex.exp ((k : ℂ) * (Real.pi * Complex.I)) = ((if k % 2 = 0 then 1 else -1 : Int) : ℂ) := by
  have hk : (k : ℂ) * (Real.pi * Complex.I) =
      ((k / 2 : Int) : ℂ) * (2 * Real.pi * Complex.I) +
        ((k % 2 : Int) : ℂ) * (Real.pi * Complex.I) := by
    have h := Int.emod_add_mul_ediv k 2
    have h' : (k : ℂ) = ((k % 2 : Int) : ℂ) + 2 * ((k / 2 : Int) : ℂ) := by
      exact_mod_cast h.symm
    rw [h']; ring
  rw [hk, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h]; simp
  · rw [h]; simp [Complex.exp_pi_mul_I]

theorem rExp_sound : ∀ a : Sym, (rExp a).denote = Complex.exp a.denote
  | .int n => by
    by_cases h0 : n = 0
    · subst h0; simp [rExp, Sym.denote]
    · by_cases h1 : n = 1
      · subst h1; simp [rExp, Sym.denote]
      · simp [rExp, h0, h1, Sym.denote]
  | .ipi k => by
    simp only [rExp, Sym.denote]
    exact (exp_ipi k).symm
  | .ln u => by
    by_cases h : lnInvOk u = true
    · simp only [rExp, h, ↓reduceIte, Sym.denote]
      exact (exp_lowerLog (lnInvOk_sound h)).symm
    · simp only [rExp, h, Bool.false_eq_true, ↓reduceIte]
      rfl
  | .e => rfl
  | .exp _ => rfl
  | .neg _ => rfl
  | .sub a b => by
    cases b with
    | ipi k =>
      simp only [rExp, Sym.denote]
      rw [Complex.exp_sub, exp_ipi k, ← rExp_sound a]
      split_ifs <;> simp [negOf_sound, div_neg]
    | _ => rfl
  | .add a b => by
    cases b with
    | ipi k =>
      simp only [rExp, Sym.denote]
      rw [Complex.exp_add, exp_ipi k, ← rExp_sound a]
      split_ifs <;> simp [negOf_sound]
    | _ => rfl

/-! ### Subtraction rules (each proved sound separately) -/

abbrev Rule := Sym → Sym → Option Sym

def RuleSound (r : Rule) : Prop :=
  ∀ a b c, r a b = some c → c.denote = a.denote - b.denote

def r2 : Rule := fun a b => if b = .int 0 then some a else none
def r3 : Rule := fun a b => if a = .int 0 then some (negOf b) else none
def r4 : Rule := fun a b => if a = b then some (.int 0) else none
def r5 : Rule := fun a b =>
  match a, b with
  | .int x, .int y => some (.int (x - y))
  | _, _ => none
def r6 : Rule := fun a b =>
  match a, b with
  | .ipi x, .ipi y => some (if x - y = 0 then .int 0 else .ipi (x - y))
  | _, _ => none
def r8 : Rule := fun a b =>
  match b with
  | .sub a' c => if a = a' then some c else none
  | _ => none
def r9 : Rule := fun a b =>
  match a with
  | .add x y => if x = b then some y else none
  | _ => none
def r10 : Rule := fun a b =>
  match a with
  | .add x y => if y = b then some x else none
  | _ => none
def r11 : Rule := fun a b =>
  match b with
  | .neg u => some (.add a u)
  | _ => none
def r12 : Rule := fun a b =>
  match a, b with
  | .sub u (.int n), .int m => some (if n + m = 0 then u else .sub u (.int (n + m)))
  | _, _ => none
def r13 : Rule := fun a b =>
  match a with
  | .sub u v => if u = b then some (negOf v) else none
  | _ => none

/-- `a − (c − kiπ) = (a − c) + kiπ`: keep `iπ` multiples outermost, for `rExp`. -/
def r14 : Rule := fun a b =>
  match b with
  | .sub c (.ipi k) => some (.add (.sub a c) (.ipi k))
  | _ => none
/-- `(c − kiπ) − b = (c − b) − kiπ`. -/
def r15 : Rule := fun a b =>
  match a with
  | .sub c (.ipi k) => some (.sub (.sub c b) (.ipi k))
  | _ => none

theorem r2_sound : RuleSound r2 := by
  intro a b c h
  by_cases hb : b = .int 0
  · subst hb; simp [r2] at h; subst h; simp [Sym.denote]
  · simp [r2, hb] at h

theorem r3_sound : RuleSound r3 := by
  intro a b c h
  by_cases ha : a = .int 0
  · subst ha; simp [r3] at h; subst h; rw [negOf_sound]; simp [Sym.denote]
  · simp [r3, ha] at h

theorem r4_sound : RuleSound r4 := by
  intro a b c h
  by_cases hab : a = b
  · subst hab; simp [r4] at h; subst h; simp [Sym.denote]
  · simp [r4, hab] at h

theorem r5_sound : RuleSound r5 := by
  intro a b c h
  simp only [r5] at h
  split at h
  next x y => cases h; simp [Sym.denote]
  next => cases h

theorem r6_sound : RuleSound r6 := by
  intro a b c h
  simp only [r6] at h
  split at h
  next x y =>
    cases h
    by_cases hxy : x - y = 0
    · have hx : x = y := by omega
      subst hx; simp [Sym.denote]
    · simp only [hxy, ↓reduceIte, Sym.denote]; push_cast; ring
  next => cases h

theorem r8_sound : RuleSound r8 := by
  intro a b c h
  simp only [r8] at h
  split at h
  next a' c' =>
    by_cases ha : a = a'
    · subst ha; simp at h; subst h; simp [Sym.denote]
    · simp [ha] at h
  next => cases h

theorem r9_sound : RuleSound r9 := by
  intro a b c h
  simp only [r9] at h
  split at h
  next x y =>
    by_cases hx : x = b
    · subst hx; simp at h; subst h; simp [Sym.denote]
    · simp [hx] at h
  next => cases h

theorem r10_sound : RuleSound r10 := by
  intro a b c h
  simp only [r10] at h
  split at h
  next x y =>
    by_cases hy : y = b
    · subst hy; simp at h; subst h; simp [Sym.denote]
    · simp [hy] at h
  next => cases h

theorem r11_sound : RuleSound r11 := by
  intro a b c h
  simp only [r11] at h
  split at h
  next u => cases h; simp [Sym.denote]
  next => cases h

theorem r12_sound : RuleSound r12 := by
  intro a b c h
  simp only [r12] at h
  split at h
  next u n m =>
    cases h
    by_cases hnm : n + m = 0
    · have hc : (n : ℂ) + m = 0 := by exact_mod_cast hnm
      simp only [hnm, ↓reduceIte, Sym.denote]
      linear_combination hc
    · simp only [hnm, ↓reduceIte, Sym.denote]; push_cast; ring
  next => cases h

theorem r13_sound : RuleSound r13 := by
  intro a b c h
  simp only [r13] at h
  split at h
  next u v =>
    by_cases hu : u = b
    · subst hu; simp at h; subst h; rw [negOf_sound]; simp [Sym.denote]
    · simp [hu] at h
  next => cases h

theorem r14_sound : RuleSound r14 := by
  intro a b c h
  simp only [r14] at h
  split at h
  next c' k => cases h; simp only [Sym.denote]; ring
  next => cases h

theorem r15_sound : RuleSound r15 := by
  intro a b c h
  simp only [r15] at h
  split at h
  next c' k => cases h; simp only [Sym.denote]; ring
  next => cases h

/-- Subtraction rules, tried in order (`lib/eml/proof.ts` order, then `r14`, `r15`). -/
def subRules : List Rule := [r2, r3, r4, r5, r6, r8, r9, r10, r11, r12, r13, r14, r15]

theorem subRules_sound : ∀ r ∈ subRules, RuleSound r := by
  intro r hr
  simp only [subRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [r2_sound, r3_sound, r4_sound, r5_sound, r6_sound, r8_sound, r9_sound,
    r10_sound, r11_sound, r12_sound, r13_sound, r14_sound, r15_sound]

def rSub (a b : Sym) : Sym :=
  (subRules.findSome? (fun r => r a b)).getD (.sub a b)

theorem rSub_sound (a b : Sym) : (rSub a b).denote = a.denote - b.denote := by
  unfold rSub
  cases h : subRules.findSome? (fun r => r a b) with
  | none => rfl
  | some c =>
    obtain ⟨r, hr, hrc⟩ := List.exists_of_findSome?_eq_some h
    exact subRules_sound r hr a b c hrc

/-! ### `ln` rules -/

def ipiStrip : Sym → Bool
  | .ipi k => decide (-1 ≤ k) && decide (k < 1)
  | _ => false

def inStrip (u : Sym) : Bool := decide (1 ≤ cls u) || ipiStrip u || boxStrip u

theorem inStrip_sound {u : Sym} (h : inStrip u = true) :
    -Real.pi ≤ u.denote.im ∧ u.denote.im < Real.pi := by
  unfold inStrip at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · obtain ⟨r, hr⟩ := (cls_sound u).1 h
    rw [hr, Complex.ofReal_im]
    constructor <;> linarith [Real.pi_pos]
  · cases u with
    | ipi k =>
      simp only [ipiStrip, Bool.and_eq_true, decide_eq_true_eq] at h
      have hk : k = -1 ∨ k = 0 := by omega
      rcases hk with rfl | rfl
      · simp [Sym.denote]; linarith [Real.pi_pos]
      · simp [Sym.denote]; exact ⟨Real.pi_pos.le, Real.pi_pos⟩
    | _ => simp [ipiStrip] at h
  · exact boxStrip_sound h

/-- Provably a positive real: by `cls`, or by the value's box. -/
def posOk (u : Sym) : Bool := decide (cls u = 2) || boxPos u

theorem posOk_sound {u : Sym} (h : posOk u = true) : ∃ r : ℝ, 0 < r ∧ u.denote = r := by
  unfold posOk at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact (cls_sound u).2 h
  · exact boxPos_sound h

/-- `ln a` with no structural rule: on the negative real axis (by box),
    `ln a = ln(−a) − iπ` (lower cut). -/
def lnRest (a : Sym) : Sym :=
  if boxNeg a = true then rSub (.ln (negOf a)) (.ipi 1) else .ln a

theorem lnRest_sound (a : Sym) : (lnRest a).denote = lowerLog a.denote := by
  unfold lnRest
  by_cases h : boxNeg a = true
  · simp only [h, ↓reduceIte]
    obtain ⟨r, hr0, hr⟩ := boxNeg_sound h
    rw [rSub_sound]
    show lowerLog (negOf a).denote - ((1 : Int) : ℂ) * (Real.pi * Complex.I) = lowerLog a.denote
    rw [negOf_sound, hr, lowerLog_ofReal_neg hr0]
    have hneg : -(r : ℂ) = ((-r : ℝ) : ℂ) := by push_cast; ring
    rw [hneg, lowerLog_ofReal_pos (by linarith)]
    simp
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rfl

def rLn : Sym → Option Sym
  | .int n =>
    if n = 1 then some (.int 0)
    else if n = 0 then none
    else if n = -1 then some (.ipi (-1))
    else some (lnRest (.int n))
  | .e => some (.int 1)
  | .neg u => if posOk u = true then (rLn u).map (fun v => rSub v (.ipi 1)) else some (.ln (.neg u))
  | .exp u => if inStrip u = true then some u else some (.ln (.exp u))
  | a => some (lnRest a)

theorem rLn_sound : ∀ (a : Sym) {b : Sym}, rLn a = some b → b.denote = lowerLog a.denote
  | .int n, b, h => by
    by_cases h1 : n = 1
    · subst h1; simp [rLn] at h; subst h; simp [Sym.denote, lowerLog_one]
    · by_cases h0 : n = 0
      · simp [rLn, h0] at h
      · by_cases hm : n = -1
        · subst hm; simp [rLn] at h; subst h
          show ((-1 : Int) : ℂ) * (Real.pi * Complex.I) = lowerLog ((-1 : Int) : ℂ)
          have hc : ((-1 : Int) : ℂ) = ((-1 : ℝ) : ℂ) := by norm_num
          rw [hc, lowerLog_ofReal_neg (by norm_num : (-1 : ℝ) < 0)]
          simp
        · simp [rLn, h1, h0, hm] at h; subst h; exact lnRest_sound _
  | .e, b, h => by
    simp [rLn] at h; subst h
    show ((1 : Int) : ℂ) = lowerLog (Complex.exp 1)
    rw [lowerLog_exp_of_im_zero (by simp)]; simp
  | .neg u, b, h => by
    by_cases hu : posOk u = true
    · simp only [rLn, hu, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      have hv' := rLn_sound u hv
      obtain ⟨r, hr0, hr⟩ := posOk_sound hu
      rw [rSub_sound, hv']
      show lowerLog u.denote - ((1 : Int) : ℂ) * (Real.pi * Complex.I) = lowerLog (-u.denote)
      rw [hr, lowerLog_ofReal_pos hr0]
      have hneg : -(r : ℂ) = ((-r : ℝ) : ℂ) := by push_cast; ring
      rw [hneg, lowerLog_ofReal_neg (by linarith), neg_neg]
      simp
    · simp only [rLn, hu, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
  | .exp u, b, h => by
    by_cases hs : inStrip u = true
    · simp only [rLn, hs, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hst := inStrip_sound hs
      exact (lowerLog_exp hst.1 hst.2).symm
    · simp [rLn, hs] at h; subst h; rfl
  | .ipi _, b, h => by simp only [rLn, Option.some.injEq] at h; subst h; exact lnRest_sound _
  | .ln _, b, h => by simp only [rLn, Option.some.injEq] at h; subst h; exact lnRest_sound _
  | .add _ _, b, h => by simp only [rLn, Option.some.injEq] at h; subst h; exact lnRest_sound _
  | .sub _ _, b, h => by simp only [rLn, Option.some.injEq] at h; subst h; exact lnRest_sound _

/-! ### One `eml` gate and the RPN certificate checker -/

/-- Symbolic `eml a b = exp a − ln b`, refusing whenever `b` is not provably nonzero. -/
def gate (a b : Sym) : Option Sym :=
  if nz b = true then (rLn b).map (fun l => rSub (rExp a) l) else none

theorem gate_sound {a b c : Sym} (h : gate a b = some c) :
    b.denote ≠ 0 ∧ c.denote = eml a.denote b.denote := by
  unfold gate at h
  by_cases hb : nz b = true
  · simp only [hb, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    refine ⟨nz_sound b hb, ?_⟩
    rw [rSub_sound, rExp_sound, rLn_sound b hl]
    rfl
  · simp [hb] at h

def optGate : Option Sym → Option Sym → Option Sym
  | some a, some b => gate a b
  | _, _ => none

/-- The certificate checker: symbolic RPN evaluation of a bit program. -/
def certify (bits : List Bool) : Option Sym :=
  match evalRpn (some (Sym.int 1)) optGate bits [] with
  | some [x] => x
  | _ => none

/-! ### Soundness -/

theorem evalRpn_map {α β : Type} (f : α → β) (one : α) (op : α → α → α)
    (one' : β) (op' : β → β → β)
    (hone : f one = one') (hop : ∀ x y, f (op x y) = op' (f x) (f y)) :
    ∀ (bits : List Bool) (st : List α),
      evalRpn one' op' bits (st.map f) = (evalRpn one op bits st).map (List.map f)
  | [], _ => rfl
  | true :: rest, st => by
    have ih := evalRpn_map f one op one' op' hone hop rest (one :: st)
    rw [List.map_cons, hone] at ih
    exact ih
  | false :: _, [] => rfl
  | false :: _, [_] => rfl
  | false :: rest, y :: x :: st => by
    have ih := evalRpn_map f one op one' op' hone hop rest (op x y :: st)
    rw [List.map_cons, hop] at ih
    exact ih

/-- Triples (symbolic, `ℂ`, `EmlExt`) whose symbolic value, when present, is the true value. -/
def Good : Type :=
  { t : Option Sym × ℂ × EmlExt //
      ∀ s, t.1 = some s → t.2.1 = s.denote ∧ t.2.2 = .finite s.denote }

noncomputable def goodOne : Good :=
  ⟨(some (.int 1), 1, .finite 1), by
    intro s hs
    cases hs
    simp [Sym.denote]⟩

noncomputable def goodOp (x y : Good) : Good :=
  ⟨(optGate x.1.1 y.1.1, eml x.1.2.1 y.1.2.1, extEml x.1.2.2 y.1.2.2), by
    obtain ⟨⟨ox, zx, wx⟩, hx⟩ := x
    obtain ⟨⟨oy, zy, wy⟩, hy⟩ := y
    intro c hc
    cases ox with
    | none => simp [optGate] at hc
    | some a =>
      cases oy with
      | none => simp [optGate] at hc
      | some b =>
        simp only [optGate] at hc
        obtain ⟨hb, hcv⟩ := gate_sound hc
        obtain ⟨rfl, rfl⟩ := hx a rfl
        obtain ⟨rfl, rfl⟩ := hy b rfl
        exact ⟨hcv.symm, by rw [extEml_finite hb, hcv]⟩⟩

/-- **Certificate soundness.** If the checker returns `s`, the program evaluates to
    `s.denote` over `ℂ` *and* to the same finite value in the calculator's
    `EmlExt` semantics (`ln 0 = −∞` is never triggered). -/
theorem certify_sound {bits : List Bool} {s : Sym} (h : certify bits = some s) :
    evalRpn (1 : ℂ) eml bits [] = some [s.denote] ∧
      evalRpn (EmlExt.finite 1) extEml bits [] = some [.finite s.denote] := by
  have h1 := evalRpn_map (fun g : Good => g.1.1) goodOne goodOp (some (Sym.int 1)) optGate
    rfl (fun _ _ => rfl) bits []
  have h2 := evalRpn_map (fun g : Good => g.1.2.1) goodOne goodOp (1 : ℂ) eml
    rfl (fun _ _ => rfl) bits []
  have h3 := evalRpn_map (fun g : Good => g.1.2.2) goodOne goodOp (EmlExt.finite 1) extEml
    rfl (fun _ _ => rfl) bits []
  simp only [List.map_nil] at h1 h2 h3
  generalize evalRpn goodOne goodOp bits [] = R at h1 h2 h3
  unfold certify at h
  rw [h1] at h
  rw [h2, h3]
  rcases R with _ | _ | ⟨g, _ | ⟨g', l⟩⟩
  · simp at h
  · simp at h
  · simp only [Option.map_some, List.map_cons, List.map_nil] at h ⊢
    obtain ⟨hz, hw⟩ := g.2 s h
    rw [hz, hw]; exact ⟨rfl, rfl⟩
  · simp at h

/-! ### Sanity checks (kernel-evaluated certificates) -/

/-- `e = 11E`. -/
example : certify [true, true, false] = some .e := by decide

/-- `0 = 111E1EE` (K 7). -/
example : certify [true, true, true, false, true, false, false] = some (.int 0) := by decide

/-- `0` is certified, so its value is kernel-checked in both semantics. -/
example : evalRpn (1 : ℂ) eml [true, true, true, false, true, false, false] [] = some [0] := by
  have := (certify_sound (bits := [true, true, true, false, true, false, false])
    (s := .int 0) (by decide)).1
  simpa [Sym.denote] using this

end Eml.Cert
