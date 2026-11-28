/-
  Sound rectangular bounds for certificate values (`Eml.Cert.Sym`).

  `bnd s = some b` gives integer fixed-point bounds (`n` stands for `n / 2^48`) on
  the real and imaginary parts of `s.denote`, proved by `bnd_sound`. The checker in
  `Cert.lean` uses them to show values nonzero (so `ln` of them is never `ln 0`),
  positive real, or inside the strip `−π ≤ Im < π`, which its purely structural
  rules cannot see: `e − exp e ≠ 0`, `exp(e − ln 2) − exp e ≠ 0`, and so on.

  Everything is plain `Int` arithmetic, so the kernel evaluates it under `decide`.

  * `e` and `π` from Mathlib's decimal bounds (`Real.exp_one_gt_d9`, `Real.pi_gt_d6`, …).
  * `exp` on real boxes: `(1 + x/2^16)^(2^16) ≤ exp x ≤ (1 − x/2^16)^(−2^16)`,
    by 16 squarings rounded outward (`sqDn`, `sqUp`); arguments above 64 are refused.
  * `ln` on real boxes away from 0: `1 − 1/x ≤ log x ≤ x − 1`, and `Im = −π` on the
    negative axis (lower cut).

  Zero `sorry`, zero custom axioms.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Eml.CertSym

namespace Eml.Cert

open Eml

/-! ### Fixed point -/

/-- Fixed-point scale `2^48`: the integer `n` stands for the real `n / D`. -/
def D : Int := 281474976710656

theorem D_pos : (0 : Int) < D := by decide

noncomputable def fx (n : Int) : ℝ := (n : ℝ) / (D : ℝ)

theorem DR_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast D_pos

theorem fx_add (a b : Int) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring
theorem fx_sub (a b : Int) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring
theorem fx_neg (a : Int) : fx (-a) = -fx a := by unfold fx; push_cast; ring
theorem fx_zero : fx 0 = 0 := by simp [fx]
theorem fx_mulD (n : Int) : fx (n * D) = n := by
  have := DR_pos.ne'
  unfold fx; push_cast; field_simp
theorem fx_mul_int (k a : Int) : fx (k * a) = k * fx a := by unfold fx; push_cast; ring
theorem fx_mono {a b : Int} (h : a ≤ b) : fx a ≤ fx b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) DR_pos.le
theorem fx_strict {a b : Int} (h : a < b) : fx a < fx b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) DR_pos
theorem fx_nonneg {a : Int} (h : 0 ≤ a) : 0 ≤ fx a := div_nonneg (by exact_mod_cast h) DR_pos.le
theorem fx_pos {a : Int} (h : 0 < a) : 0 < fx a := div_pos (by exact_mod_cast h) DR_pos

/-- Floor division never overshoots. -/
theorem ediv_le (n d : Int) (hd : 0 < d) : ((n / d : Int) : ℝ) ≤ (n : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Int.ediv_mul_le n hd.ne'

/-- Ceiling division `−((−n)/d)` never undershoots. -/
theorem le_cdiv (n d : Int) (hd : 0 < d) : (n : ℝ) / d ≤ ((-((-n) / d) : Int) : ℝ) := by
  have h := ediv_le (-n) d hd
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

/-! ### `e` and `π` -/

def eLo : Int := 2718281828 * D / 1000000000
def eHi : Int := -((-(27182818286 * D)) / 10000000000)
def piLo : Int := 3141592 * D / 1000000
def piHi : Int := -((-(3141593 * D)) / 1000000)

theorem fx_eLo : fx eLo < Real.exp 1 := by
  have h := ediv_le (2718281828 * D) 1000000000 (by norm_num)
  have : fx eLo ≤ 2718281828 / 1000000000 := by
    unfold fx eLo
    rw [div_le_iff₀ DR_pos]
    push_cast at h
    linarith
  linarith [Real.exp_one_gt_d9]

theorem fx_eHi : Real.exp 1 < fx eHi := by
  have h := le_cdiv (27182818286 * D) 10000000000 (by norm_num)
  have : (27182818286 / 10000000000 : ℝ) ≤ fx eHi := by
    unfold fx eHi
    rw [le_div_iff₀ DR_pos]
    push_cast at h ⊢
    linarith
  linarith [Real.exp_one_lt_d9]

theorem fx_piLo : fx piLo < Real.pi := by
  have h := ediv_le (3141592 * D) 1000000 (by norm_num)
  have : fx piLo ≤ 3141592 / 1000000 := by
    unfold fx piLo
    rw [div_le_iff₀ DR_pos]
    push_cast at h
    linarith
  linarith [Real.pi_gt_d6]

theorem fx_piHi : Real.pi < fx piHi := by
  have h := le_cdiv (3141593 * D) 1000000 (by norm_num)
  have : (3141593 / 1000000 : ℝ) ≤ fx piHi := by
    unfold fx piHi
    rw [le_div_iff₀ DR_pos]
    push_cast at h ⊢
    linarith
  linarith [Real.pi_lt_d6]

/-! ### `exp` bounds by repeated squaring -/

/-- `2^16`: `exp x = exp(x / N)^N`. -/
def N : Int := 65536

theorem N_pos : (0 : Int) < N := by decide

theorem NR : (N : ℝ) = 2 ^ 16 := by norm_num [N]

def sqDn : Nat → Int → Int
  | 0, r => r
  | k + 1, r => sqDn k (r * r / D)

def sqUp : Nat → Int → Int
  | 0, r => r
  | k + 1, r => sqUp k (-((-(r * r)) / D))

theorem two_halves (y : ℝ) (k : Nat) :
    Real.exp (y / 2 ^ (k + 1)) * Real.exp (y / 2 ^ (k + 1)) = Real.exp (y / 2 ^ k) := by
  rw [← Real.exp_add]; congr 1; rw [pow_succ]; field_simp; ring

theorem sqDn_le : ∀ (k : Nat) (r : Int) (y : ℝ), 0 ≤ r → fx r ≤ Real.exp (y / 2 ^ k) →
    fx (sqDn k r) ≤ Real.exp y
  | 0, r, y, _, h => by simpa [sqDn] using h
  | k + 1, r, y, hr, h => by
    rw [sqDn]
    have hq : 0 ≤ r * r / D := Int.ediv_nonneg (mul_nonneg hr hr) D_pos.le
    refine sqDn_le k _ y hq ?_
    have hD := DR_pos.ne'
    have h1 : fx (r * r / D) ≤ fx r * fx r := by
      have := ediv_le (r * r) D D_pos
      unfold fx
      rw [div_le_iff₀ DR_pos]
      push_cast at this
      calc _ ≤ (r : ℝ) * r / D := this
        _ = (r / D) * (r / D) * D := by field_simp
    have h2 : fx r * fx r ≤ Real.exp (y / 2 ^ (k + 1)) * Real.exp (y / 2 ^ (k + 1)) :=
      mul_self_le_mul_self (fx_nonneg hr) h
    linarith [two_halves y k]

theorem le_sqUp : ∀ (k : Nat) (r : Int) (y : ℝ), 0 ≤ r → Real.exp (y / 2 ^ k) ≤ fx r →
    Real.exp y ≤ fx (sqUp k r)
  | 0, r, y, _, h => by simpa [sqUp] using h
  | k + 1, r, y, hr, h => by
    rw [sqUp]
    have hD := DR_pos.ne'
    have h1 : fx r * fx r ≤ fx (-((-(r * r)) / D)) := by
      have := le_cdiv (r * r) D D_pos
      unfold fx
      rw [le_div_iff₀ DR_pos]
      push_cast at this ⊢
      calc (r : ℝ) / D * (r / D) * D = (r : ℝ) * r / D := by field_simp
        _ ≤ _ := this
    have hq : 0 ≤ -((-(r * r)) / D) := by
      have h0 : (0 : ℝ) ≤ fx (-((-(r * r)) / D)) := le_trans (mul_self_nonneg _) h1
      unfold fx at h0
      rw [le_div_iff₀ DR_pos, zero_mul] at h0
      exact_mod_cast h0
    refine le_sqUp k _ y hq ?_
    have h2 : Real.exp (y / 2 ^ (k + 1)) * Real.exp (y / 2 ^ (k + 1)) ≤ fx r * fx r :=
      mul_self_le_mul_self (Real.exp_pos _).le h
    linarith [two_halves y k]

/-- Arguments above `64` are not bounded above (the numbers would get large). -/
def expCap : Int := 64 * D

/-- A lower bound for `exp`: `(1 + x/N)^N`, rounded down. -/
def expLo (x : Int) : Int :=
  if N * D + min x expCap < 0 then 0 else sqDn 16 ((N * D + min x expCap) / N)

/-- An upper bound for `exp`: `(1 − x/N)^(−N)`, rounded up; none above `expCap`. -/
def expHi (x : Int) : Option Int :=
  if expCap < x then none else some (sqUp 16 (-((-(N * D * D)) / (N * D - x))))

theorem fx_expLo_le (x : Int) : fx (expLo x) ≤ Real.exp (fx x) := by
  unfold expLo
  have hmono : Real.exp (fx (min x expCap)) ≤ Real.exp (fx x) :=
    Real.exp_le_exp.mpr (fx_mono (min_le_left _ _))
  split_ifs with h
  · rw [fx_zero]; exact (Real.exp_pos _).le
  · push_neg at h
    refine le_trans ?_ hmono
    generalize min x expCap = m at h ⊢
    apply sqDn_le 16 _ _ (Int.ediv_nonneg h N_pos.le)
    have hD := DR_pos.ne'
    have hb : fx ((N * D + m) / N) ≤ fx m / 2 ^ 16 + 1 := by
      have := ediv_le (N * D + m) N N_pos
      unfold fx
      rw [div_le_iff₀ DR_pos]
      push_cast at this
      rw [NR] at this
      calc _ ≤ _ := this
        _ = _ := by field_simp; ring
    linarith [Real.add_one_le_exp (fx m / 2 ^ 16)]

theorem exp_le_fx_expHi {x h : Int} (hx : expHi x = some h) : Real.exp (fx x) ≤ fx h := by
  unfold expHi at hx
  split_ifs at hx with hc
  cases hx
  push_neg at hc
  have hND : 0 < N * D - x := by unfold expCap at hc; unfold N D at *; omega
  have hcpos : 0 ≤ -((-(N * D * D)) / (N * D - x)) := by
    have h0 := le_cdiv (N * D * D) (N * D - x) hND
    have : (0 : ℝ) ≤ (((N * D * D : Int)) : ℝ) / ((N * D - x : Int) : ℝ) :=
      div_nonneg (by exact_mod_cast (mul_pos (mul_pos N_pos D_pos) D_pos).le)
        (by exact_mod_cast hND.le)
    exact_mod_cast le_trans this h0
  apply le_sqUp 16 _ _ hcpos
  set t := fx x / 2 ^ 16 with ht
  set c := -((-(N * D * D)) / (N * D - x))
  have hNDR : (0 : ℝ) < (N : ℝ) * D - x := by exact_mod_cast hND
  have hNDp : (0 : ℝ) < (N : ℝ) * D := by exact_mod_cast mul_pos N_pos D_pos
  have hNDDp : (0 : ℝ) < (N : ℝ) * D * D := by exact_mod_cast mul_pos (mul_pos N_pos D_pos) D_pos
  have h1t : 0 < 1 - t := by
    have : t = (x : ℝ) / ((N : ℝ) * D) := by rw [ht, ← NR]; unfold fx; field_simp
    rw [this, sub_pos, div_lt_one hNDp]
    linarith
  have key : Real.exp t * (1 - t) ≤ 1 := by
    have := Real.add_one_le_exp (-t)
    calc Real.exp t * (1 - t) = Real.exp t * (-t + 1) := by ring
      _ ≤ Real.exp t * Real.exp (-t) := mul_le_mul_of_nonneg_left this (Real.exp_pos t).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hc : 1 ≤ fx c * (1 - t) := by
    have h0 : ((N * D * D : Int) : ℝ) / ((N * D - x : Int) : ℝ) ≤ (c : ℝ) := le_cdiv _ _ hND
    have hD := DR_pos.ne'
    have hN : (N : ℝ) ≠ 0 := by rw [NR]; norm_num
    have : fx c * (1 - t) = (c : ℝ) * ((N : ℝ) * D - x) / ((N : ℝ) * D * D) := by
      rw [ht, ← NR]; unfold fx; field_simp
    rw [this, le_div_iff₀ hNDDp, one_mul]
    rw [div_le_iff₀ (by exact_mod_cast hND)] at h0
    push_cast at h0
    linarith
  exact le_of_mul_le_mul_right (le_trans key hc) h1t

/-! ### `ln` bounds -/

/-- `1 − 1/x`, rounded down (for `x > 0`). -/
def lnLo (x : Int) : Int := D - (-((-(D * D)) / x))

/-- `x − 1`. -/
def lnHi (x : Int) : Int := x - D

theorem fx_lnLo_le {x : Int} (hx : 0 < x) {r : ℝ} (hr : fx x ≤ r) : fx (lnLo x) ≤ Real.log r := by
  have hfx := fx_pos hx
  have hlog : Real.log (fx x) ≤ Real.log r := Real.log_le_log hfx hr
  have h1 := Real.one_sub_inv_le_log_of_pos hfx
  have hc : (fx x)⁻¹ ≤ fx (-((-(D * D)) / x)) := by
    have h0 := le_cdiv (D * D) x hx
    have hD := DR_pos.ne'
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    unfold fx
    rw [inv_div, le_div_iff₀ DR_pos]
    push_cast at h0 ⊢
    calc (D : ℝ) / x * D = (D : ℝ) * D / x := by ring
      _ ≤ _ := h0
  have : fx (lnLo x) = 1 - fx (-((-(D * D)) / x)) := by
    unfold lnLo; rw [fx_sub]; unfold fx; rw [div_self DR_pos.ne']
  linarith

theorem log_le_fx_lnHi {x : Int} {r : ℝ} (hr0 : 0 < r) (hr : r ≤ fx x) : Real.log r ≤ fx (lnHi x) := by
  have h1 := Real.log_le_sub_one_of_pos (lt_of_lt_of_le hr0 hr)
  have h2 := Real.log_le_log hr0 hr
  have : fx (lnHi x) = fx x - 1 := by
    unfold lnHi; rw [fx_sub]; unfold fx; rw [div_self DR_pos.ne']
  linarith

/-! ### Boxes -/

/-- Fixed-point bounds on the real and imaginary parts. -/
structure Box where
  rl : Int
  rh : Int
  il : Int
  ih : Int
  deriving DecidableEq, Repr

def Box.Has (b : Box) (z : ℂ) : Prop :=
  fx b.rl ≤ z.re ∧ z.re ≤ fx b.rh ∧ fx b.il ≤ z.im ∧ z.im ≤ fx b.ih

def bIpi (k : Int) : Box :=
  if 0 ≤ k then ⟨0, 0, k * piLo, k * piHi⟩ else ⟨0, 0, k * piHi, k * piLo⟩

def bNeg (b : Box) : Box := ⟨-b.rh, -b.rl, -b.ih, -b.il⟩
def bAdd (a b : Box) : Box := ⟨a.rl + b.rl, a.rh + b.rh, a.il + b.il, a.ih + b.ih⟩
def bSub (a b : Box) : Box := ⟨a.rl - b.rh, a.rh - b.rl, a.il - b.ih, a.ih - b.il⟩

/-- `exp` of a real box. -/
def bExp (b : Box) : Option Box :=
  if b.il = 0 ∧ b.ih = 0 then (expHi b.rh).map (fun h => ⟨expLo b.rl, h, 0, 0⟩) else none

/-- Lower-cut `ln` of a real box that excludes `0`. -/
def bLn (b : Box) : Option Box :=
  if b.il = 0 ∧ b.ih = 0 then
    if 0 < b.rl then some ⟨lnLo b.rl, lnHi b.rh, 0, 0⟩
    else if b.rh < 0 then some ⟨lnLo (-b.rh), lnHi (-b.rl), -piHi, -piLo⟩
    else none
  else none

def bnd : Sym → Option Box
  | .int n => some ⟨n * D, n * D, 0, 0⟩
  | .e => some ⟨eLo, eHi, 0, 0⟩
  | .ipi k => some (bIpi k)
  | .exp a => (bnd a).bind bExp
  | .ln a => (bnd a).bind bLn
  | .neg a => (bnd a).map bNeg
  | .add a b =>
    match bnd a, bnd b with
    | some x, some y => some (bAdd x y)
    | _, _ => none
  | .sub a b =>
    match bnd a, bnd b with
    | some x, some y => some (bSub x y)
    | _, _ => none

/-! ### Soundness of each box rule -/

theorem im_zero_of_has {b : Box} {z : ℂ} (hb : b.Has z) (h0 : b.il = 0) (h1 : b.ih = 0) :
    z.im = 0 := by
  obtain ⟨-, -, h2, h3⟩ := hb
  rw [h0, fx_zero] at h2; rw [h1, fx_zero] at h3
  linarith

theorem eq_ofReal_re {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

theorem bIpi_has (k : Int) : (bIpi k).Has ((k : ℂ) * (Real.pi * Complex.I)) := by
  have hre : ((k : ℂ) * (Real.pi * Complex.I)).re = 0 := by simp
  have him : ((k : ℂ) * (Real.pi * Complex.I)).im = k * Real.pi := by simp
  have hlo := fx_piLo
  have hhi := fx_piHi
  unfold bIpi
  split_ifs with hk
  · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre, fx_zero]
    · rw [hre, fx_zero]
    · rw [him, fx_mul_int]; exact mul_le_mul_of_nonneg_left hlo.le hkR
    · rw [him, fx_mul_int]; exact mul_le_mul_of_nonneg_left hhi.le hkR
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hk))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre, fx_zero]
    · rw [hre, fx_zero]
    · rw [him, fx_mul_int]; exact mul_le_mul_of_nonpos_left hhi.le hkR
    · rw [him, fx_mul_int]; exact mul_le_mul_of_nonpos_left hlo.le hkR

theorem bNeg_has {b : Box} {z : ℂ} (h : b.Has z) : (bNeg b).Has (-z) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bNeg, fx_neg, Complex.neg_re, Complex.neg_im] <;> linarith

theorem bAdd_has {a b : Box} {z w : ℂ} (ha : a.Has z) (hb : b.Has w) : (bAdd a b).Has (z + w) := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨g1, g2, g3, g4⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bAdd, fx_add, Complex.add_re, Complex.add_im] <;> linarith

theorem bSub_has {a b : Box} {z w : ℂ} (ha : a.Has z) (hb : b.Has w) : (bSub a b).Has (z - w) := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨g1, g2, g3, g4⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bSub, fx_sub, Complex.sub_re, Complex.sub_im] <;> linarith

theorem bExp_has {b c : Box} {z : ℂ} (hb : b.Has z) (h : bExp b = some c) :
    c.Has (Complex.exp z) := by
  unfold bExp at h
  split_ifs at h with h0
  obtain ⟨hi, hh⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hhi, rfl⟩ := hh
  have him := im_zero_of_has hb h0.1 h0.2
  obtain ⟨h1, h2, -, -⟩ := hb
  have hre : (Complex.exp z).re = Real.exp z.re := by simp [Complex.exp_re, him]
  have himz : (Complex.exp z).im = 0 := by simp [Complex.exp_im, him]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; exact le_trans (fx_expLo_le _) (Real.exp_le_exp.mpr h1)
  · rw [hre]; exact le_trans (Real.exp_le_exp.mpr h2) (exp_le_fx_expHi hhi)
  · rw [himz, fx_zero]
  · rw [himz, fx_zero]

theorem bLn_has {b c : Box} {z : ℂ} (hb : b.Has z) (h : bLn b = some c) :
    c.Has (lowerLog z) := by
  unfold bLn at h
  split_ifs at h with h0 hp hn <;> cases h
  · have him := im_zero_of_has hb h0.1 h0.2
    obtain ⟨h1, h2, -, -⟩ := hb
    have hr0 : 0 < z.re := lt_of_lt_of_le (fx_pos hp) h1
    rw [eq_ofReal_re him, lowerLog_ofReal_pos hr0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using fx_lnLo_le hp h1
    · simpa using log_le_fx_lnHi hr0 h2
    · simp [fx_zero]
    · simp [fx_zero]
  · have him := im_zero_of_has hb h0.1 h0.2
    obtain ⟨h1, h2, -, -⟩ := hb
    have hneg : 0 < -b.rh := by omega
    have hr0 : z.re < 0 := lt_of_le_of_lt h2 (by have := fx_strict hn; rwa [fx_zero] at this)
    rw [eq_ofReal_re him, lowerLog_ofReal_neg hr0]
    have hpos : 0 < -z.re := by linarith
    have hlo : fx (-b.rh) ≤ -z.re := by rw [fx_neg]; linarith
    have hhi : -z.re ≤ fx (-b.rl) := by rw [fx_neg]; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using fx_lnLo_le hneg hlo
    · simpa using log_le_fx_lnHi hpos hhi
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, fx_neg]
      linarith [fx_piHi]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, fx_neg]
      linarith [fx_piLo]

/-- **Box soundness.** -/
theorem bnd_sound : ∀ (s : Sym) {b : Box}, bnd s = some b → b.Has s.denote
  | .int n, b, h => by
    cases h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Sym.denote, fx_mulD, fx_zero]
  | .e, b, h => by
    cases h
    have hre : (Sym.e.denote).re = Real.exp 1 := by
      simp [Sym.denote, Complex.exp_re]
    have him : (Sym.e.denote).im = 0 := by
      simp [Sym.denote, Complex.exp_im]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; exact fx_eLo.le
    · rw [hre]; exact fx_eHi.le
    · rw [him, fx_zero]
    · rw [him, fx_zero]
  | .ipi k, b, h => by cases h; exact bIpi_has k
  | .exp a, b, h => by
    obtain ⟨x, hx, hb⟩ := Option.bind_eq_some_iff.mp h
    exact bExp_has (bnd_sound a hx) hb
  | .ln a, b, h => by
    obtain ⟨x, hx, hb⟩ := Option.bind_eq_some_iff.mp h
    exact bLn_has (bnd_sound a hx) hb
  | .neg a, b, h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact bNeg_has (bnd_sound a hx)
  | .add a c, b, h => by
    simp only [bnd] at h
    split at h
    next x y hx hy => cases h; exact bAdd_has (bnd_sound a hx) (bnd_sound c hy)
    next => cases h
  | .sub a c, b, h => by
    simp only [bnd] at h
    split at h
    next x y hx hy => cases h; exact bSub_has (bnd_sound a hx) (bnd_sound c hy)
    next => cases h

/-! ### What the checker asks of a box -/

/-- `0` lies outside the box. -/
def Box.nz (b : Box) : Bool :=
  decide (0 < b.rl) || decide (b.rh < 0) || decide (0 < b.il) || decide (b.ih < 0)

/-- The box is a positive real interval. -/
def Box.pos (b : Box) : Bool := decide (b.il = 0) && decide (b.ih = 0) && decide (0 < b.rl)

/-- The box is a negative real interval. -/
def Box.neg (b : Box) : Bool := decide (b.il = 0) && decide (b.ih = 0) && decide (b.rh < 0)

/-- The box lies in the strip `−π ≤ Im < π`. -/
def Box.strip (b : Box) : Bool := decide (-piLo ≤ b.il) && decide (b.ih < piLo)

theorem Box.nz_sound {b : Box} {z : ℂ} (hb : b.Has z) (h : b.nz = true) : z ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  unfold Box.nz at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  intro hz
  subst hz
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2 h3 h4
  rcases h with ((h | h) | h) | h
  · linarith [fx_pos h]
  · linarith [fx_strict h, fx_zero]
  · linarith [fx_pos h]
  · linarith [fx_strict h, fx_zero]

theorem Box.pos_sound {b : Box} {z : ℂ} (hb : b.Has z) (h : b.pos = true) :
    ∃ r : ℝ, 0 < r ∧ z = r := by
  unfold Box.pos at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, hp⟩ := h
  have him := im_zero_of_has hb h0 h1
  exact ⟨z.re, lt_of_lt_of_le (fx_pos hp) hb.1, eq_ofReal_re him⟩

theorem Box.neg_sound {b : Box} {z : ℂ} (hb : b.Has z) (h : b.neg = true) :
    ∃ r : ℝ, r < 0 ∧ z = r := by
  unfold Box.neg at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, hn⟩ := h
  have him := im_zero_of_has hb h0 h1
  have := fx_strict hn
  rw [fx_zero] at this
  exact ⟨z.re, lt_of_le_of_lt hb.2.1 this, eq_ofReal_re him⟩

theorem Box.strip_sound {b : Box} {z : ℂ} (hb : b.Has z) (h : b.strip = true) :
    -Real.pi ≤ z.im ∧ z.im < Real.pi := by
  unfold Box.strip at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, -, h3, h4⟩ := hb
  have hl := fx_mono h.1
  have hh := fx_strict h.2
  rw [fx_neg] at hl
  constructor <;> linarith [fx_piLo]

/-- `s` is provably nonzero by its box. -/
def boxNz (s : Sym) : Bool := ((bnd s).map Box.nz).getD false

/-- `s` is provably a positive real by its box. -/
def boxPos (s : Sym) : Bool := ((bnd s).map Box.pos).getD false

/-- `s` is provably a negative real by its box. -/
def boxNeg (s : Sym) : Bool := ((bnd s).map Box.neg).getD false

/-- `s` is provably in the strip `−π ≤ Im < π` by its box. -/
def boxStrip (s : Sym) : Bool := ((bnd s).map Box.strip).getD false

theorem boxNz_sound {s : Sym} (h : boxNz s = true) : s.denote ≠ 0 := by
  unfold boxNz at h
  cases hb : bnd s with
  | none => simp [hb] at h
  | some b => simp only [hb, Option.map_some, Option.getD_some] at h; exact Box.nz_sound (bnd_sound s hb) h

theorem boxPos_sound {s : Sym} (h : boxPos s = true) : ∃ r : ℝ, 0 < r ∧ s.denote = r := by
  unfold boxPos at h
  cases hb : bnd s with
  | none => simp [hb] at h
  | some b => simp only [hb, Option.map_some, Option.getD_some] at h; exact Box.pos_sound (bnd_sound s hb) h

theorem boxNeg_sound {s : Sym} (h : boxNeg s = true) : ∃ r : ℝ, r < 0 ∧ s.denote = r := by
  unfold boxNeg at h
  cases hb : bnd s with
  | none => simp [hb] at h
  | some b => simp only [hb, Option.map_some, Option.getD_some] at h; exact Box.neg_sound (bnd_sound s hb) h

theorem boxStrip_sound {s : Sym} (h : boxStrip s = true) :
    -Real.pi ≤ s.denote.im ∧ s.denote.im < Real.pi := by
  unfold boxStrip at h
  cases hb : bnd s with
  | none => simp [hb] at h
  | some b =>
    simp only [hb, Option.map_some, Option.getD_some] at h; exact Box.strip_sound (bnd_sound s hb) h

/-! ### Sanity checks (kernel-evaluated) -/

/-- `e − exp e ≠ 0`, via `exp e ≥ 15.15`. -/
example : boxNz (.sub .e (.exp .e)) = true := by decide

/-- `exp(e − ln 2) − exp e ≠ 0`. -/
example : boxNz (.sub (.exp (.sub .e (.ln (.int 2)))) (.exp .e)) = true := by decide

end Eml.Cert
