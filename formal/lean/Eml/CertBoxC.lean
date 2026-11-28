/-
  Integer layer of the complex certificate boxes.

  `D` is `2^48` and `piLo` / `piHi` are the six-digit bounds already proved in
  `CertBox`. Trig will use `KH = 4` halvings and internal scale `PS = 2^64`.
  `PS / (D · 2^KH) = 2^12`, so the scale divides the fixed point evenly. The
  reference prototype uses `KH = 12`, scale `2^96` (ratio `2^36`, also exact),
  and a twenty-digit π. That only shrinks the Taylor remainder. The bounds in
  this repository are the six-digit ones, so the coarser pair is the one that
  matches the code.

  Searches take a `Nat` fuel argument and are checked afterwards. A wrong search
  answer fails the check and falls back to a bound that is still sound.
-/
import Eml.CertBox

namespace Eml.Cert

open Eml

/-! ### Parameters -/

/-- Taylor halvings. `π / 2^KH < 1`, which the degree-4 bound needs. -/
def KH : Nat := 4

/-- Internal trig scale. -/
def PS : Int := 2 ^ 64

/-- Bisection fuel for the sharp log and arcsin. -/
def boxFuel : Nat := 16

theorem scale_exact : PS / (D * ((2 : Int) ^ KH)) = (2 : Int) ^ 12 := by
  decide

noncomputable def sc (S n : Int) : ℝ := (n : ℝ) / (S : ℝ)

theorem sc_D : sc D = fx := rfl

/-! ### Interval product -/

/-- Product of two fixed-point intervals at scale `S`, rounded outward. -/
def imul (a1 a2 b1 b2 S : Int) : Int × Int :=
  let p11 := a1 * b1
  let p12 := a1 * b2
  let p21 := a2 * b1
  let p22 := a2 * b2
  (min (min p11 p12) (min p21 p22) / S,
    -((-max (max p11 p12) (max p21 p22)) / S))

theorem mem_interval_mul_le {x a b y : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    x * y ≤ max (a * y) (b * y) := by
  by_cases hy : 0 ≤ y
  · exact le_trans (mul_le_mul_of_nonneg_right hb hy) (le_max_right _ _)
  · push_neg at hy
    exact le_trans (mul_le_mul_of_nonpos_right ha hy.le) (le_max_left _ _)

theorem min_le_mem_interval_mul {x a b y : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  by_cases hy : 0 ≤ y
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right ha hy)
  · push_neg at hy
    exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hb hy.le)

theorem mul_le_corners {x y xa xb ya yb : ℝ}
    (hxa : xa ≤ x) (hxb : x ≤ xb) (hya : ya ≤ y) (hyb : y ≤ yb) :
    x * y ≤ max (max (xa * ya) (xa * yb)) (max (xb * ya) (xb * yb)) := by
  have hy : x * y ≤ max (x * ya) (x * yb) := by
    simpa [mul_comm] using mem_interval_mul_le (x := y) (a := ya) (b := yb) (y := x) hya hyb
  have ha : x * ya ≤ max (xa * ya) (xb * ya) := mem_interval_mul_le hxa hxb
  have hb : x * yb ≤ max (xa * yb) (xb * yb) := mem_interval_mul_le hxa hxb
  have h1 : max (xa * ya) (xb * ya) ≤
      max (max (xa * ya) (xa * yb)) (max (xb * ya) (xb * yb)) := by
    apply max_le
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h2 : max (xa * yb) (xb * yb) ≤
      max (max (xa * ya) (xa * yb)) (max (xb * ya) (xb * yb)) := by
    apply max_le
    · exact le_trans (le_max_right (xa * ya) _) (le_max_left _ _)
    · exact le_trans (le_max_right (xb * ya) _) (le_max_right _ _)
  exact le_trans hy (max_le (le_trans ha h1) (le_trans hb h2))

theorem corners_le_mul {x y xa xb ya yb : ℝ}
    (hxa : xa ≤ x) (hxb : x ≤ xb) (hya : ya ≤ y) (hyb : y ≤ yb) :
    min (min (xa * ya) (xa * yb)) (min (xb * ya) (xb * yb)) ≤ x * y := by
  have hy : min (x * ya) (x * yb) ≤ x * y := by
    simpa [mul_comm] using
      min_le_mem_interval_mul (x := y) (a := ya) (b := yb) (y := x) hya hyb
  have ha : min (xa * ya) (xb * ya) ≤ x * ya := min_le_mem_interval_mul hxa hxb
  have hb : min (xa * yb) (xb * yb) ≤ x * yb := min_le_mem_interval_mul hxa hxb
  have h1 : min (min (xa * ya) (xa * yb)) (min (xb * ya) (xb * yb)) ≤
      min (xa * ya) (xb * ya) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
  have h2 : min (min (xa * ya) (xa * yb)) (min (xb * ya) (xb * yb)) ≤
      min (xa * yb) (xb * yb) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  exact le_trans (le_min (le_trans h1 ha) (le_trans h2 hb)) hy

theorem corner_real (a b S : Int) (hS : (S : ℝ) ≠ 0) :
    sc S a * sc S b = ((a * b : Int) : ℝ) / ((S : ℝ) * S) := by
  unfold sc
  push_cast
  field_simp [hS]

theorem sc_ediv_le {n S : Int} (hS : 0 < S) :
    sc S (n / S) ≤ (n : ℝ) / ((S : ℝ) * S) := by
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have h := ediv_le n S hS
  unfold sc
  refine le_trans (div_le_div_of_nonneg_right h hS0.le) ?_
  rw [div_div]

theorem sc_le_cdiv {n S : Int} (hS : 0 < S) :
    (n : ℝ) / ((S : ℝ) * S) ≤ sc S (-((-n) / S)) := by
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have h := le_cdiv n S hS
  unfold sc
  have hdiv : ((n : ℝ) / S) / S ≤ ((-((-n) / S) : Int) : ℝ) / S :=
    div_le_div_of_nonneg_right h hS0.le
  rw [div_div] at hdiv
  exact hdiv

theorem imul_sound {a1 a2 b1 b2 S : Int} (hS : 0 < S) {x y : ℝ}
    (hx1 : sc S a1 ≤ x) (hx2 : x ≤ sc S a2) (hy1 : sc S b1 ≤ y) (hy2 : y ≤ sc S b2) :
    sc S (imul a1 a2 b1 b2 S).1 ≤ x * y ∧ x * y ≤ sc S (imul a1 a2 b1 b2 S).2 := by
  have hS0 : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have hSS : (0 : ℝ) ≤ S * S := mul_nonneg (by exact_mod_cast hS.le) (by exact_mod_cast hS.le)
  set p11 : Int := a1 * b1
  set p12 : Int := a1 * b2
  set p21 : Int := a2 * b1
  set p22 : Int := a2 * b2
  set lo : Int := min (min p11 p12) (min p21 p22)
  set hi : Int := max (max p11 p12) (max p21 p22)
  have lo11 : lo ≤ p11 := by unfold lo; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have lo12 : lo ≤ p12 := by unfold lo; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have lo21 : lo ≤ p21 := by unfold lo; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have lo22 : lo ≤ p22 := by unfold lo; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hi11 : p11 ≤ hi := by unfold hi; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hi12 : p12 ≤ hi := by unfold hi; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hi21 : p21 ≤ hi := by unfold hi; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hi22 : p22 ≤ hi := by unfold hi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hpair : imul a1 a2 b1 b2 S = (lo / S, -((-hi) / S)) := by
    simp [imul, p11, p12, p21, p22, lo, hi]
  rw [hpair]
  constructor
  · refine le_trans (sc_ediv_le (n := lo) hS) ?_
    refine le_trans ?_ (corners_le_mul hx1 hx2 hy1 hy2)
    apply le_min
    · apply le_min
      · rw [corner_real a1 b1 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast lo11) hSS
      · rw [corner_real a1 b2 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast lo12) hSS
    · apply le_min
      · rw [corner_real a2 b1 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast lo21) hSS
      · rw [corner_real a2 b2 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast lo22) hSS
  · refine le_trans (mul_le_corners hx1 hx2 hy1 hy2) ?_
    refine le_trans ?_ (sc_le_cdiv (n := hi) hS)
    apply max_le
    · apply max_le
      · rw [corner_real a1 b1 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hi11) hSS
      · rw [corner_real a1 b2 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hi12) hSS
    · apply max_le
      · rw [corner_real a2 b1 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hi21) hSS
      · rw [corner_real a2 b2 S hS0]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hi22) hSS

/-! ### Interval quotient -/

/-- Quotient of two fixed-point intervals. The denominator interval is positive. -/
def idiv (a1 a2 b1 b2 : Int) : Int × Int :=
  let flo (n d : Int) := (n * D) / d
  let cei (n d : Int) := -((-(n * D)) / d)
  (min (min (flo a1 b1) (flo a1 b2)) (min (flo a2 b1) (flo a2 b2)),
    max (max (cei a1 b1) (cei a1 b2)) (max (cei a2 b1) (cei a2 b2)))

theorem fx_floor_div {a b : Int} (hb : 0 < b) :
    fx ((a * D) / b) ≤ (a : ℝ) / (b : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h := ediv_le (a * D) b hb
  unfold fx
  rw [div_le_div_iff₀ DR_pos hb0]
  have h' := (le_div_iff₀ hb0).mp h
  push_cast at h' ⊢
  exact h'

theorem div_le_fx_ceil {a b : Int} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ fx (-((-(a * D)) / b)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h := le_cdiv (a * D) b hb
  unfold fx
  rw [div_le_div_iff₀ hb0 DR_pos]
  have h' := (div_le_iff₀ hb0).mp h
  push_cast at h' ⊢
  exact h'

theorem le_max_div_den {y m m1 m2 : ℝ} (hm1 : m1 ≤ m) (hm2 : m ≤ m2) (hp : 0 < m1) :
    y / m ≤ max (y / m1) (y / m2) := by
  have hm : 0 < m := lt_of_lt_of_le hp hm1
  have hm2p : 0 < m2 := lt_of_lt_of_le hm hm2
  by_cases hy : 0 ≤ y
  · exact le_trans
      ((div_le_div_iff₀ hm hp).mpr (mul_le_mul_of_nonneg_left hm1 hy)) (le_max_left _ _)
  · push_neg at hy
    exact le_trans
      ((div_le_div_iff₀ hm hm2p).mpr (mul_le_mul_of_nonpos_left hm2 hy.le)) (le_max_right _ _)

theorem min_div_den_le {y m m1 m2 : ℝ} (hm1 : m1 ≤ m) (hm2 : m ≤ m2) (hp : 0 < m1) :
    min (y / m1) (y / m2) ≤ y / m := by
  have hm : 0 < m := lt_of_lt_of_le hp hm1
  have hm2p : 0 < m2 := lt_of_lt_of_le hm hm2
  by_cases hy : 0 ≤ y
  · exact le_trans (min_le_right _ _)
      ((div_le_div_iff₀ hm2p hm).mpr (mul_le_mul_of_nonneg_left hm2 hy))
  · push_neg at hy
    exact le_trans (min_le_left _ _)
      ((div_le_div_iff₀ hp hm).mpr (mul_le_mul_of_nonpos_left hm1 hy.le))

theorem quot_le_corners {y m xa xb ma mb : ℝ}
    (hy2 : y ≤ xb) (hm1 : ma ≤ m) (hm2 : m ≤ mb) (hp : 0 < ma) :
    y / m ≤ max (max (xa / ma) (xb / ma)) (max (xa / mb) (xb / mb)) := by
  have hm : 0 < m := lt_of_lt_of_le hp hm1
  have hmb : 0 < mb := lt_of_lt_of_le hm hm2
  have hyb : y / m ≤ xb / m :=
    (div_le_div_iff₀ hm hm).mpr (mul_le_mul_of_nonneg_right hy2 hm.le)
  have hden : xb / m ≤ max (xb / ma) (xb / mb) := le_max_div_den hm1 hm2 hp
  have h1 : xb / ma ≤ max (max (xa / ma) (xb / ma)) (max (xa / mb) (xb / mb)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have h2 : xb / mb ≤ max (max (xa / ma) (xb / ma)) (max (xa / mb) (xb / mb)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact le_trans hyb (le_trans hden (max_le h1 h2))

theorem corners_le_quot {y m xa xb ma mb : ℝ}
    (hy1 : xa ≤ y) (hm1 : ma ≤ m) (hm2 : m ≤ mb) (hp : 0 < ma) :
    min (min (xa / ma) (xb / ma)) (min (xa / mb) (xb / mb)) ≤ y / m := by
  have hm : 0 < m := lt_of_lt_of_le hp hm1
  have hya : xa / m ≤ y / m :=
    (div_le_div_iff₀ hm hm).mpr (mul_le_mul_of_nonneg_right hy1 hm.le)
  have hden : min (xa / ma) (xa / mb) ≤ xa / m := min_div_den_le hm1 hm2 hp
  have h4 : min (min (xa / ma) (xb / ma)) (min (xa / mb) (xb / mb)) ≤
      min (xa / ma) (xa / mb) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
  exact le_trans (le_trans h4 hden) hya

theorem endpoint_ratio {a b : Int} (hb : b ≠ 0) :
    fx a / fx b = (a : ℝ) / (b : ℝ) := by
  unfold fx
  field_simp [DR_pos.ne', hb]

theorem idiv_sound {a1 a2 b1 b2 : Int} {y m : ℝ}
    (hx1 : fx a1 ≤ y) (hx2 : y ≤ fx a2) (hy1 : fx b1 ≤ m) (hy2 : m ≤ fx b2)
    (hb : 0 < b1) :
    fx (idiv a1 a2 b1 b2).1 ≤ y / m ∧ y / m ≤ fx (idiv a1 a2 b1 b2).2 := by
  have hb2 : 0 < b2 := by
    have hfx : 0 < fx b2 := lt_of_lt_of_le (fx_pos hb) (le_trans hy1 hy2)
    by_contra h
    push_neg at h
    exact not_lt_of_ge (by simpa [fx_zero] using fx_mono h) hfx
  set q11 : Int := (a1 * D) / b1
  set q12 : Int := (a1 * D) / b2
  set q21 : Int := (a2 * D) / b1
  set q22 : Int := (a2 * D) / b2
  set c11 : Int := -((-(a1 * D)) / b1)
  set c12 : Int := -((-(a1 * D)) / b2)
  set c21 : Int := -((-(a2 * D)) / b1)
  set c22 : Int := -((-(a2 * D)) / b2)
  set lo : Int := min (min q11 q12) (min q21 q22)
  set hi : Int := max (max c11 c12) (max c21 c22)
  have hpair : idiv a1 a2 b1 b2 = (lo, hi) := by
    simp [idiv, q11, q12, q21, q22, c11, c12, c21, c22, lo, hi]
  have hma : 0 < fx b1 := fx_pos hb
  have h11 : fx q11 ≤ fx a1 / fx b1 := by
    unfold q11; rw [endpoint_ratio hb.ne']; exact fx_floor_div hb
  have h12 : fx q12 ≤ fx a1 / fx b2 := by
    unfold q12; rw [endpoint_ratio hb2.ne']; exact fx_floor_div hb2
  have h21 : fx q21 ≤ fx a2 / fx b1 := by
    unfold q21; rw [endpoint_ratio hb.ne']; exact fx_floor_div hb
  have h22 : fx q22 ≤ fx a2 / fx b2 := by
    unfold q22; rw [endpoint_ratio hb2.ne']; exact fx_floor_div hb2
  have k11 : fx a1 / fx b1 ≤ fx c11 := by
    unfold c11; rw [endpoint_ratio hb.ne']; exact div_le_fx_ceil hb
  have k12 : fx a1 / fx b2 ≤ fx c12 := by
    unfold c12; rw [endpoint_ratio hb2.ne']; exact div_le_fx_ceil hb2
  have k21 : fx a2 / fx b1 ≤ fx c21 := by
    unfold c21; rw [endpoint_ratio hb.ne']; exact div_le_fx_ceil hb
  have k22 : fx a2 / fx b2 ≤ fx c22 := by
    unfold c22; rw [endpoint_ratio hb2.ne']; exact div_le_fx_ceil hb2
  rw [hpair]
  constructor
  · have lo11 : lo ≤ q11 := by unfold lo; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have lo21 : lo ≤ q21 := by unfold lo; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have lo12 : lo ≤ q12 := by unfold lo; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have lo22 : lo ≤ q22 := by unfold lo; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hlo : fx lo ≤ min (min (fx a1 / fx b1) (fx a2 / fx b1))
        (min (fx a1 / fx b2) (fx a2 / fx b2)) := by
      apply le_min
      · exact le_min (le_trans (fx_mono lo11) h11) (le_trans (fx_mono lo21) h21)
      · exact le_min (le_trans (fx_mono lo12) h12) (le_trans (fx_mono lo22) h22)
    exact le_trans hlo (corners_le_quot hx1 hy1 hy2 hma)
  · have hi11 : c11 ≤ hi := by unfold hi; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hi21 : c21 ≤ hi := by unfold hi; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hi12 : c12 ≤ hi := by unfold hi; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hi22 : c22 ≤ hi := by unfold hi; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hhi : max (max (fx a1 / fx b1) (fx a2 / fx b1))
        (max (fx a1 / fx b2) (fx a2 / fx b2)) ≤ fx hi := by
      apply max_le
      · exact max_le (le_trans k11 (fx_mono hi11)) (le_trans k21 (fx_mono hi21))
      · exact max_le (le_trans k12 (fx_mono hi12)) (le_trans k22 (fx_mono hi22))
    exact le_trans (quot_le_corners hx2 hy1 hy2 hma) hhi

/-! ### Clamp into [-1, 1]

The bound needs both `-1 ≤ v` and `v ≤ 1`. A value below `-1` is not bounded by
the clamped low end, and a value above `1` is not bounded by the clamped high end.
-/

/-- Clamp a fixed-point integer into `[-D, D]`. -/
def clampU (x : Int) : Int := max (-D) (min D x)

theorem fx_one : fx D = 1 := by
  unfold fx
  exact div_self DR_pos.ne'

theorem clampU_lo {s : Int} {v : ℝ} (hs : fx s ≤ v) (hv0 : -1 ≤ v) (_hv1 : v ≤ 1) :
    fx (clampU s) ≤ v := by
  unfold clampU
  by_cases hhi : D < s
  · have : (1 : ℝ) < v := by
      have := fx_strict hhi
      rw [fx_one] at this
      exact lt_of_lt_of_le this hs
    linarith
  · push_neg at hhi
    by_cases hlo : s < -D
    · have hclamp : max (-D) (min D s) = -D := by
        rw [min_eq_right hhi, max_comm, max_eq_right (le_of_lt hlo)]
      rw [hclamp, fx_neg, fx_one]
      linarith
    · push_neg at hlo
      rw [min_eq_right hhi, max_eq_right hlo]
      exact hs

theorem clampU_hi {s : Int} {v : ℝ} (hs : v ≤ fx s) (hv0 : -1 ≤ v) (hv1 : v ≤ 1) :
    v ≤ fx (clampU s) := by
  unfold clampU
  by_cases hlo : s < -D
  · have : v < -1 := by
      have := fx_strict hlo
      rw [fx_neg, fx_one] at this
      exact lt_of_le_of_lt hs this
    linarith
  · push_neg at hlo
    by_cases hhi : D < s
    · have hclamp : max (-D) (min D s) = D := by
        rw [min_eq_left (le_of_lt hhi), max_eq_right (neg_le_self D_pos.le)]
      rw [hclamp, fx_one]
      exact hv1
    · push_neg at hhi
      rw [min_eq_right hhi, max_eq_right hlo]
      exact hs

/-! ### Square root by bisection -/

/-- Fuelled integer square-root search. Returns the low end when the fuel runs out. -/
def isqrtSearch : Nat → Int → Int → Int → Int
  | 0, lo, _, _ => lo
  | fuel + 1, lo, hi, n =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid ≤ n then isqrtSearch fuel mid hi n else isqrtSearch fuel lo mid n

/-- Lower integer square root. Falls back to `0`, which is sound for a nonnegative target. -/
def sqrtLo (n : Int) : Int :=
  let r := if n ≤ 0 then 0 else isqrtSearch 512 0 (n + 1) n
  if 0 ≤ r ∧ r * r ≤ n then r else 0

/-- Upper integer square root. Falls back to `n + D` when the search check fails. -/
def sqrtHi (n : Int) : Int :=
  let r := (if n ≤ 0 then 0 else isqrtSearch 512 0 (n + 1) n) + 1
  if 0 ≤ r ∧ n ≤ r * r then r else n + D

example : sqrtLo (D * D) = D := by decide

example : sqrtHi (D * D) = D + 1 := by decide

theorem sqrtLo_sound {n : Int} {m : ℝ} (hn : 0 ≤ n) (h : (n : ℝ) / (D : ℝ) ^ 2 ≤ m ^ 2)
    (hm : 0 ≤ m) : fx (sqrtLo n) ≤ m := by
  have _hn := hn
  set r : Int := if n ≤ 0 then 0 else isqrtSearch 512 0 (n + 1) n
  have hdef : sqrtLo n = if 0 ≤ r ∧ r * r ≤ n then r else 0 := by
    simp [sqrtLo, r]
  rw [hdef]
  split_ifs with hc
  · rcases hc with ⟨hr, hsq⟩
    have hr0 : 0 ≤ fx r := fx_nonneg hr
    have hsqR : (r : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((r * r : Int) : ℝ) ≤ n := by exact_mod_cast hsq
      simpa [pow_two] using this
    have hfx : (fx r) ^ 2 ≤ (n : ℝ) / (D : ℝ) ^ 2 := by
      unfold fx
      rw [div_pow]
      exact div_le_div_of_nonneg_right hsqR (sq_nonneg _)
    have hmd : (fx r) ^ 2 ≤ m ^ 2 := le_trans hfx h
    have habs : |fx r| ≤ |m| := (sq_le_sq).mp hmd
    rw [abs_of_nonneg hr0, abs_of_nonneg hm] at habs
    exact habs
  · rw [fx_zero]
    exact hm

theorem sqrtHi_sound {n : Int} {m : ℝ} (h : m ^ 2 ≤ (n : ℝ) / (D : ℝ) ^ 2) (hm : 0 ≤ m) :
    m ≤ fx (sqrtHi n) := by
  set r : Int := (if n ≤ 0 then 0 else isqrtSearch 512 0 (n + 1) n) + 1
  have hdef : sqrtHi n = if 0 ≤ r ∧ n ≤ r * r then r else n + D := by
    simp [sqrtHi, r]
  rw [hdef]
  split_ifs with hc
  · rcases hc with ⟨hr, hsq⟩
    have hr0 : 0 ≤ fx r := fx_nonneg hr
    have hsqR : (n : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : ((n : Int) : ℝ) ≤ r * r := by exact_mod_cast hsq
      simpa [pow_two] using this
    have hfx : (n : ℝ) / (D : ℝ) ^ 2 ≤ (fx r) ^ 2 := by
      unfold fx
      rw [div_pow]
      exact div_le_div_of_nonneg_right hsqR (sq_nonneg _)
    have hmd : m ^ 2 ≤ (fx r) ^ 2 := le_trans h hfx
    have habs : |m| ≤ |fx r| := (sq_le_sq).mp hmd
    rw [abs_of_nonneg hm, abs_of_nonneg hr0] at habs
    exact habs
  · have hD2 : (0 : ℝ) < (D : ℝ) ^ 2 := pow_pos DR_pos 2
    have hn0 : (0 : ℝ) ≤ n := by
      by_contra hlt
      push_neg at hlt
      have hneg : (n : ℝ) / (D : ℝ) ^ 2 < 0 := div_neg_of_neg_of_pos hlt hD2
      exact not_lt_of_ge (le_trans (sq_nonneg m) h) hneg
    have hnI : 0 ≤ n := by exact_mod_cast hn0
    have hmle : m ≤ Real.sqrt ((n : ℝ) / (D : ℝ) ^ 2) :=
      (Real.le_sqrt hm (div_nonneg hn0 hD2.le)).mpr h
    have hdiv : Real.sqrt ((n : ℝ) / (D : ℝ) ^ 2) = Real.sqrt (n : ℝ) / D := by
      rw [Real.sqrt_div hn0 ((D : ℝ) ^ 2), Real.sqrt_sq DR_pos.le]
    rw [hdiv] at hmle
    have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) + D := by
      by_cases hz : n = 0
      · subst hz
        simp [Real.sqrt_zero]
        exact D_pos.le
      · have hone : (1 : Int) ≤ n := by omega
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hone
        have hle : Real.sqrt (n : ℝ) ≤ n :=
          (Real.sqrt_le_left (by exact_mod_cast hnI)).mpr (by nlinarith)
        exact le_trans hle (le_add_of_nonneg_right DR_pos.le)
    have hscale : Real.sqrt (n : ℝ) / D ≤ ((n : Int) + D : ℝ) / D :=
      div_le_div_of_nonneg_right hsqrt DR_pos.le
    refine le_trans hmle (le_trans hscale ?_)
    unfold fx
    push_cast
    rfl

/-! ### Modulus of a box -/

/-- Largest real coordinate that is still away from zero, or zero if the interval meets zero. -/
def nxOf (b : Box) : Int :=
  if 0 < b.rl then b.rl else if b.rh < 0 then -b.rh else 0

/-- Same as `nxOf`, for the imaginary interval. -/
def nyOf (b : Box) : Int :=
  if 0 < b.il then b.il else if b.ih < 0 then -b.ih else 0

/-- Squared distance from zero to the far side of the zero gap, in integer units. -/
def nxny (b : Box) : Int := nxOf b * nxOf b + nyOf b * nyOf b

/-- Sum of the squared endpoint bounds. An upper bound on `D ^ 2 · ‖z‖ ^ 2`. -/
def cornerSq (b : Box) : Int :=
  max (b.rl * b.rl) (b.rh * b.rh) + max (b.il * b.il) (b.ih * b.ih)

theorem sq_le_endpoint {t a b : ℝ} (ha : a ≤ t) (hb : t ≤ b) :
    t ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
  by_cases ht : 0 ≤ t
  · have hsq : t * t ≤ b * b := mul_self_le_mul_self ht hb
    rw [← pow_two, ← pow_two] at hsq
    exact le_trans hsq (le_max_right _ _)
  · push_neg at ht
    have hsq : t * t ≤ a * a := by
      have := mul_self_le_mul_self (neg_nonneg.mpr ht.le) (neg_le_neg ha)
      simpa [neg_mul, mul_neg] using this
    rw [← pow_two, ← pow_two] at hsq
    exact le_trans hsq (le_max_left _ _)

theorem fx_sq (k : Int) : (fx k) ^ 2 = ((k * k : Int) : ℝ) / (D : ℝ) ^ 2 := by
  unfold fx
  rw [div_pow]
  push_cast
  ring

theorem max_div_right {u v c : ℝ} (hc : 0 ≤ c) : max (u / c) (v / c) = max u v / c := by
  by_cases h : u ≤ v
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hc)]
  · push_neg at h
    rw [max_eq_left h.le, max_eq_left (div_le_div_of_nonneg_right h.le hc)]

theorem re_sq_le_corner {b : Box} {z : ℂ} (hb : b.Has z) :
    z.re ^ 2 ≤ ((max (b.rl * b.rl) (b.rh * b.rh) : Int) : ℝ) / (D : ℝ) ^ 2 := by
  have h := sq_le_endpoint hb.1 hb.2.1
  rw [fx_sq, fx_sq, max_div_right (sq_nonneg _), ← Int.cast_max] at h
  exact h

theorem im_sq_le_corner {b : Box} {z : ℂ} (hb : b.Has z) :
    z.im ^ 2 ≤ ((max (b.il * b.il) (b.ih * b.ih) : Int) : ℝ) / (D : ℝ) ^ 2 := by
  have h := sq_le_endpoint hb.2.2.1 hb.2.2.2
  rw [fx_sq, fx_sq, max_div_right (sq_nonneg _), ← Int.cast_max] at h
  exact h

theorem nx_sq_le_re {b : Box} {z : ℂ} (hb : b.Has z) : (fx (nxOf b)) ^ 2 ≤ z.re ^ 2 := by
  unfold nxOf
  split_ifs with hpos hneg
  · have h0 : 0 ≤ fx b.rl := fx_nonneg (le_of_lt hpos)
    have hsq : fx b.rl * fx b.rl ≤ z.re * z.re := mul_self_le_mul_self h0 hb.1
    simpa [pow_two] using hsq
  · have hre : z.re ≤ fx b.rh := hb.2.1
    have hsq : fx (-b.rh) * fx (-b.rh) ≤ z.re * z.re := by
      have hle : fx (-b.rh) ≤ -z.re := by
        rw [fx_neg]
        exact neg_le_neg hre
      have h0 : 0 ≤ fx (-b.rh) := fx_nonneg (neg_nonneg.mpr (le_of_lt hneg))
      have := mul_self_le_mul_self h0 hle
      simpa [neg_mul, mul_neg] using this
    simpa [pow_two] using hsq
  · simp [fx_zero]
    exact sq_nonneg _

theorem ny_sq_le_im {b : Box} {z : ℂ} (hb : b.Has z) : (fx (nyOf b)) ^ 2 ≤ z.im ^ 2 := by
  unfold nyOf
  split_ifs with hpos hneg
  · have h0 : 0 ≤ fx b.il := fx_nonneg (le_of_lt hpos)
    have hsq : fx b.il * fx b.il ≤ z.im * z.im := mul_self_le_mul_self h0 hb.2.2.1
    simpa [pow_two] using hsq
  · have him : z.im ≤ fx b.ih := hb.2.2.2
    have hsq : fx (-b.ih) * fx (-b.ih) ≤ z.im * z.im := by
      have hle : fx (-b.ih) ≤ -z.im := by
        rw [fx_neg]
        exact neg_le_neg him
      have h0 : 0 ≤ fx (-b.ih) := fx_nonneg (neg_nonneg.mpr (le_of_lt hneg))
      have := mul_self_le_mul_self h0 hle
      simpa [neg_mul, mul_neg] using this
    simpa [pow_two] using hsq
  · simp [fx_zero]
    exact sq_nonneg _

theorem nxny_sq_le {b : Box} {z : ℂ} (hb : b.Has z) :
    ((nxny b : Int) : ℝ) / (D : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := by
  have hre := nx_sq_le_re hb
  have him := ny_sq_le_im hb
  rw [fx_sq] at hre
  rw [fx_sq] at him
  have hsum : ((nxOf b * nxOf b : Int) : ℝ) / (D : ℝ) ^ 2 +
      ((nyOf b * nyOf b : Int) : ℝ) / (D : ℝ) ^ 2 ≤ z.re * z.re + z.im * z.im := by
    simpa [pow_two] using add_le_add hre him
  rw [← add_div] at hsum
  have hcast : (((nxOf b * nxOf b + nyOf b * nyOf b : Int) : Int) : ℝ) =
      ((nxOf b * nxOf b : Int) : ℝ) + ((nyOf b * nyOf b : Int) : ℝ) := by
    push_cast
    ring
  rw [← hcast] at hsum
  have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  simpa [nxny, hnorm] using hsum

theorem corner_sq_ge {b : Box} {z : ℂ} (hb : b.Has z) :
    ‖z‖ ^ 2 ≤ ((cornerSq b : Int) : ℝ) / (D : ℝ) ^ 2 := by
  have hre := re_sq_le_corner hb
  have him := im_sq_le_corner hb
  have hsum : z.re ^ 2 + z.im ^ 2 ≤
      (((max (b.rl * b.rl) (b.rh * b.rh) : Int) : ℝ) +
        ((max (b.il * b.il) (b.ih * b.ih) : Int) : ℝ)) / (D : ℝ) ^ 2 := by
    rw [add_div]
    exact add_le_add hre him
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two, pow_two]
  rw [hnorm]
  refine le_trans hsum ?_
  have hcast : ((cornerSq b : Int) : ℝ) =
      ((max (b.rl * b.rl) (b.rh * b.rh) : Int) : ℝ) +
        ((max (b.il * b.il) (b.ih * b.ih) : Int) : ℝ) := by
    simp [cornerSq, Int.cast_add]
  rw [hcast]

theorem norm_bounds_of_has {b : Box} {z : ℂ} (hb : b.Has z) :
    fx (sqrtLo (nxny b)) ≤ ‖z‖ ∧ ‖z‖ ≤ fx (sqrtHi (cornerSq b)) := by
  have hlo : ((nxny b : Int) : ℝ) / (D : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := nxny_sq_le hb
  have hhi : ‖z‖ ^ 2 ≤ ((cornerSq b : Int) : ℝ) / (D : ℝ) ^ 2 := corner_sq_ge hb
  have hn : 0 ≤ nxny b := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact ⟨sqrtLo_sound hn hlo (norm_nonneg _), sqrtHi_sound hhi (norm_nonneg _)⟩

/-! ### Sharp logarithm

The bisection is untrusted. `lnSLo` / `lnSHi` keep the candidate only when
`expHi` / `expLo` certify it, and otherwise fall back to `lnLo` / `lnHi`.
-/

/-- Largest candidate `m` the fuel finds with `expHi m = some h` and `h ≤ x`. -/
def lnSearchLo : Nat → Int → Int → Int → Int
  | 0, _, lo, _ => lo
  | fuel + 1, x, lo, hi =>
    if hi ≤ lo then lo
    else
      let mid := (lo + hi + 1) / 2
      match expHi mid with
      | some h => if h ≤ x then lnSearchLo fuel x mid hi else lnSearchLo fuel x lo (mid - 1)
      | none => lnSearchLo fuel x lo (mid - 1)

/-- Smallest candidate `m` the fuel finds with `m ≤ expCap` and `x ≤ expLo m`. -/
def lnSearchHi : Nat → Int → Int → Int → Int
  | 0, _, _, hi => hi
  | fuel + 1, x, lo, hi =>
    if hi ≤ lo then hi
    else
      let mid := (lo + hi) / 2
      if mid ≤ expCap ∧ x ≤ expLo mid then lnSearchHi fuel x lo mid
      else lnSearchHi fuel x (mid + 1) hi

/-- Lower bound for `log`, sharpened by bisection when the `exp` upper bound allows it. -/
def lnSLo (x : Int) : Int :=
  let c := lnSearchLo boxFuel x (lnLo x) (min (lnHi x) expCap)
  match expHi c with
  | some h => if h ≤ x then c else lnLo x
  | none => lnLo x

/-- Upper bound for `log`, sharpened by bisection when the `exp` lower bound allows it. -/
def lnSHi (x : Int) : Int :=
  let c := lnSearchHi boxFuel x (lnLo x) (lnHi x)
  if c ≤ expCap ∧ x ≤ expLo c then c else lnHi x

theorem fx_lnSLo_le {x : Int} (hx : 0 < x) {r : ℝ} (hr : fx x ≤ r) :
    fx (lnSLo x) ≤ Real.log r := by
  dsimp only [lnSLo]
  generalize hc : lnSearchLo boxFuel x (lnLo x) (min (lnHi x) expCap) = c
  cases hE : expHi c with
  | none =>
    dsimp
    exact fx_lnLo_le hx hr
  | some h =>
    dsimp
    by_cases hh : h ≤ x
    · rw [if_pos hh]
      have hexp : Real.exp (fx c) ≤ fx h := exp_le_fx_expHi hE
      have hr0 : 0 < r := lt_of_lt_of_le (fx_pos hx) hr
      have : Real.exp (fx c) ≤ r := le_trans hexp (le_trans (fx_mono hh) hr)
      exact (Real.le_log_iff_exp_le hr0).mpr this
    · rw [if_neg hh]
      exact fx_lnLo_le hx hr

theorem log_le_fx_lnSHi {x : Int} {r : ℝ} (hr0 : 0 < r) (hr : r ≤ fx x) :
    Real.log r ≤ fx (lnSHi x) := by
  dsimp only [lnSHi]
  generalize hc : lnSearchHi boxFuel x (lnLo x) (lnHi x) = c
  by_cases hcond : c ≤ expCap ∧ x ≤ expLo c
  · rw [if_pos hcond]
    rcases hcond with ⟨_hcap, hlo⟩
    have : r ≤ Real.exp (fx c) :=
      le_trans hr (le_trans (fx_mono hlo) (fx_expLo_le c))
    exact (Real.log_le_iff_le_exp hr0).mpr this
  · rw [if_neg hcond]
    exact log_le_fx_lnHi hr0 hr

end Eml.Cert
