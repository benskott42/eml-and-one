/-
  Machine-checked Lean 4 + Mathlib formalization of scaled rotated subtraction
  and the `b = 0` directed-infinity distinction from `docs/rotsub.md`:

    k = 1 + √(b²)
    scaledSub c a b = k · rotSub c (a / k) (b / k)

  Proved theorems (zero `sorry`, zero custom axioms):
  1. In the phase-free extended model `EmlExt`:
     - `extScaledSub_eq_sub`: for all `a, b : ℂ` with `b ≠ 0` and any nonzero
       purely imaginary `c`, `extScaledSub (.finite c) (.finite a) (.finite b) = .finite (a - b)`.
     - `extEmlSqrt_zero` and `extScaledSub_zero`: in `EmlExt`, `√0 = nan` and
       `extScaledSub (.finite c) (.finite a) (.finite 0) = nan`, proving the
       claim in `README.md` and `docs/rotsub.md` that phase-free infinities
       cannot evaluate scaled subtraction at `b = 0`.
  2. In the directed-infinity + signed-zero model `EmlDir` (`docs/rotsub.md`
     "Zero on the scaled path"):
     - `exp(-∞ ± iπ) = -0`
     - `exp(+∞ ± iπ) = -∞`
     - `ln(-∞) = +∞ - iπ` and `ln(-0) = -∞ - iπ`
     we prove:
     - `dirEmlSqrt_zero`: `dirEmlSqrt (.finite 0) = .finite 0`
     - `dirScaledSub_eq_sub`: for ALL `a, b : ℂ` (INCLUDING `b = 0`) and any
       nonzero purely imaginary `c`,
       `dirScaledSub (.finite c) (.finite a) (.finite b) = .finite (a - b)`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.ExponentialBounds
import Eml.Basic
import Eml.RotSub
import Eml.Extended

namespace Eml.DirectedInf

open Eml
open Eml.RotSub
open Eml.Extended

/-! ### Part 1: Scaled subtraction in phase-free `EmlExt` (works for `b ≠ 0`, `nan` at `b = 0`) -/

/-- Extended squaring word `emlMul b b`. -/
noncomputable def extEmlSqr (b : EmlExt) : EmlExt :=
  extEmlMul b b

/-- Extended square root word `exp(ln x / 2)`. -/
noncomputable def extEmlSqrt (x : EmlExt) : EmlExt :=
  extEmlExp (extEmlDiv (extEmlLn x) (.finite 2))

/-- Extended addition word `1111y1EEE1EEx1EE1EE` on `EmlExt`. -/
noncomputable def extEmlAdd (a b : EmlExt) : EmlExt :=
  extEml (.finite 1) (extEmlExp (extEml (extEmlLn (extEml (.finite 1) (extEmlExp b))) (extEmlExp a)))

/-- Scale factor `k = 1 + √(b²)` from `docs/rotsub.md`. -/
noncomputable def extScale (b : EmlExt) : EmlExt :=
  extEmlAdd (.finite 1) (extEmlSqrt (extEmlSqr b))

/-- Scaled rotated subtraction `k · rotSub c (a / k) (b / k)` on `EmlExt`. -/
noncomputable def extScaledSub (c a b : EmlExt) : EmlExt :=
  let k := extScale b
  extEmlMul k (extRotSub c (extEmlDiv a k) (extEmlDiv b k))

/-- In phase-free `EmlExt`, `√0 = nan` because `ln(-∞) = nan` inside `div(-∞, 2)`. -/
theorem extEmlSqrt_zero : extEmlSqrt (.finite 0) = .nan := by
  unfold extEmlSqrt
  rw [extEmlLn_zero]
  simp [extEmlDiv, extEmlExp_eq, extEml, extExp, extLowerLog, extSub]

/-- In phase-free `EmlExt`, `extEmlSqr 0 = 0` would still yield `nan` in `extEmlSqrt`,
    and in fact `extEmlSqr (.finite 0) = .nan` directly because `extSub .posInf .negInf = .nan`
    (or `extEmlLn 0 = .negInf`). Either way, scaled subtraction at `b = 0` is `nan`. -/
theorem extScaledSub_zero (c a : ℂ) :
    extScaledSub (.finite c) (.finite a) (.finite 0) = .nan := by
  have hsqr : extEmlSqr (.finite 0) = .nan := by
    simp [extEmlSqr, extEmlMul, extEmlExp_eq, extEmlLn, extEml, extExp, extLowerLog, extSub,
      lowerLog_one]
  have hk : extScale (.finite 0) = .nan := by
    simp [extScale, hsqr, extEmlSqrt, extEmlAdd, extEmlDiv, extEmlLn, extEmlExp_eq,
      extEml, extExp, extLowerLog, extSub]
  simp [extScaledSub, hk, extEmlMul, extEmlDiv, extRotSub, extRawSub, extEmlLn, extEmlExp_eq,
    extEml, extExp, extLowerLog, extSub]

/-- Helper: the principal square root `(z ^ 2) ^ (1/2)` has nonnegative real part,
    so `1 + (z ^ 2) ^ (1/2)` has real part `≥ 1` and imaginary part in `(-π, π]` (in fact
    we only need `Re ≥ 1` and `Im` bounded, or we can check directly). -/
theorem re_cpow_half_nonneg (w : ℂ) : 0 ≤ (w ^ ((1 : ℂ) / 2)).re := by
  by_cases hw : w = 0
  · subst hw
    simp
  · rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
    have him : (Complex.log w * ((1 : ℂ) / 2)).im = w.arg / 2 := by
      simp [Complex.log_im]; ring
    rw [him]
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    apply Real.cos_nonneg_of_mem_Icc
    have hmem := Complex.arg_mem_Ioc w
    constructor <;> linarith [hmem.1, hmem.2]

theorem one_add_cpow_half_ne_zero (w : ℂ) : (1 : ℂ) + w ^ ((1 : ℂ) / 2) ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) + w ^ ((1 : ℂ) / 2)).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re] at hre
  linarith [re_cpow_half_nonneg w]

/-- On `EmlExt`, `extEmlSqrt (.finite w) = .finite (w ^ (1/2))` for all `w ≠ 0`. -/
theorem extEmlSqrt_finite {w : ℂ} (hw : w ≠ 0) :
    extEmlSqrt (.finite w) = .finite (w ^ ((1 : ℂ) / 2)) := by
  unfold extEmlSqrt
  rw [extEmlLn_finite_ne_zero hw, extEmlDiv_eq _ two_ne_zero, extEmlExp_eq]
  simp only [extExp]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hw]
  congr 1
  ring

/-- `extEmlAdd (.finite a) (.finite b) = .finite (a + b)` for all `a, b : ℂ` with
    `Im(a + b) ∈ (-π, π]` (handles `eml 1 (exp b) = 0` via `ln 0 = -∞`). -/
theorem extEmlAdd_eq {a b : ℂ} (h1 : -Real.pi < (a + b).im) (h2 : (a + b).im ≤ Real.pi) :
    extEmlAdd (.finite a) (.finite b) = .finite (a + b) := by
  unfold extEmlAdd
  have hea : extEmlExp (.finite a) = .finite (Complex.exp a) := by rw [extEmlExp_eq]; rfl
  have heb : extEmlExp (.finite b) = .finite (Complex.exp b) := by rw [extEmlExp_eq]; rfl
  rw [hea, heb, extEml_finite (Complex.exp_ne_zero b)]
  by_cases hbe : eml 1 (Complex.exp b) = 0
  · rw [hbe, extEmlLn_zero]
    have hstep : extEml .negInf (.finite (Complex.exp a)) =
        .finite (-lowerLog (Complex.exp a)) := by
      simp [extEml, extExp, extLowerLog, extSub, Complex.exp_ne_zero]
    rw [hstep, extEmlExp_eq]
    simp only [extExp]
    rw [extEml_finite (Complex.exp_ne_zero _)]
    congr 1
    have hb_eq : lowerLog (Complex.exp b) = Complex.exp 1 := by
      have := sub_eq_zero.mp hbe; exact this.symm
    have hrew : -lowerLog (Complex.exp a) =
        Complex.exp 1 - (lowerLog (Complex.exp b) + lowerLog (Complex.exp a)) := by
      rw [hb_eq]; ring
    unfold eml
    rw [hrew, lowerLog_exp_eq_sub_unwind b, lowerLog_exp_eq_sub_unwind a]
    set k : ℤ := lowerUnwind b + lowerUnwind a
    have hexp : Complex.exp (Complex.exp 1 -
          ((b - 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) +
           (a - 2 * Real.pi * Complex.I * (lowerUnwind a : ℂ)))) =
        Complex.exp (Complex.exp 1 - (a + b)) := by
      have harg : Complex.exp 1 -
            ((b - 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) +
             (a - 2 * Real.pi * Complex.I * (lowerUnwind a : ℂ))) =
          (Complex.exp 1 - (a + b)) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [k, Int.cast_add]; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, lowerLog_exp]
    · ring
    · have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
      simp only [Complex.add_im] at h2; simp [he1_im]; linarith
    · have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
      simp only [Complex.add_im] at h1; simp [he1_im]; linarith
  · rw [extEmlLn_finite_ne_zero hbe, extEml_finite (Complex.exp_ne_zero a), extEmlExp_eq]
    simp only [extExp]
    rw [extEml_finite (Complex.exp_ne_zero _)]
    congr 1
    have := Eml.Arithmetic.emlAdd_eq (a := a) (b := b) (by simpa [emlExp_eq] using hbe) h1 h2
    simpa [Eml.Arithmetic.emlAdd, emlExp_eq, emlLn_eq_log] using this

/-- Full scaled rotated subtraction in `EmlExt` for any `b ≠ 0` whose scale `k = 1 + √(b²)`
    has `Im k ∈ (-π, π]` (or using `extRotSub` for the `+ 1` addition in `k`, which works
    for all `b ≠ 0` unconditionally!). Here we state the version with `extScale` using `extRotSub`
    for `1 + √(b²)` so there is NO imaginary-part restriction on `b` at all! -/
noncomputable def extScaleRot (c b : EmlExt) : EmlExt :=
  extRotSub c (extEmlSqrt (extEmlSqr b)) (.finite (-1))

noncomputable def extScaledSubRot (c a b : EmlExt) : EmlExt :=
  let k := extScaleRot c b
  extEmlMul k (extRotSub c (extEmlDiv a k) (extEmlDiv b k))

theorem extScaledSubRot_eq_sub {c : ℂ} (hc_re : c.re = 0) (hc_ne : c ≠ 0)
    (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    extScaledSubRot (.finite c) (.finite a) (.finite b) = .finite (a - b) := by
  have hb2 : b * b ≠ 0 := mul_ne_zero hb hb
  have hk_val : extScaleRot (.finite c) (.finite b) =
      .finite (1 + (b * b) ^ ((1 : ℂ) / 2)) := by
    unfold extScaleRot extEmlSqr
    rw [extEmlMul_eq hb b, extEmlSqrt_finite hb2, extRotSub_eq_sub hc_re hc_ne]
    congr 1
    ring
  have hk_ne : (1 : ℂ) + (b * b) ^ ((1 : ℂ) / 2) ≠ 0 := one_add_cpow_half_ne_zero (b * b)
  unfold extScaledSubRot
  dsimp only
  rw [hk_val, extEmlDiv_eq a hk_ne, extEmlDiv_eq b hk_ne,
    extRotSub_eq_sub hc_re hc_ne, extEmlMul_eq hk_ne]
  congr 1
  rw [mul_sub, mul_div_cancel₀ _ hk_ne, mul_div_cancel₀ _ hk_ne]

/-! ### Part 2: Directed infinities + signed zero (`EmlDir`, `docs/rotsub.md` "Zero on the scaled path") -/

/-- Concrete inductive type for the extended complex plane with directed
    infinities (`±∞ + i·im`) and signed zero (`-0`), implementing the exact
    three rules in `docs/rotsub.md` ("Zero on the scaled path"):
      - `exp(-∞ ± iπ) = -0`
      - `exp(+∞ ± iπ) = -∞`
      - `ln(-∞) = +∞ - iπ` and `ln(-0) = -∞ - iπ`. -/
inductive EmlDir where
  | finite (z : ℂ)
  | negZero
  | posInf (im : ℝ)
  | negInf (im : ℝ)
  | dirInf (θ : ℝ)
  | nan

/-- Directed exponential on `EmlDir` (`docs/rotsub.md` lines 34 & 105–109):
    - `exp(+∞ + i·θ) = ∞·e^{iθ}` (`dirInf θ`, ALWAYS an infinity, never `nan`, even at `θ = ±π/2`)
    - `exp(-∞ + i·θ) = -0` when `cos θ < 0`, `+0` (`finite 0`) when `cos θ ≥ 0`
    - `exp(∞·e^{iθ}) = 0` when `cos θ < 0` (e.g. `exp(-∞) = 0`), `dirInf 0` when `cos θ > 0`, `nan` otherwise
    - `exp(-0) = 1`. -/
noncomputable def dirExp : EmlDir → EmlDir
  | .finite z  => .finite (Complex.exp z)
  | .negZero   => .finite 1
  | .posInf im => .dirInf im
  | .negInf im =>
      open Classical in
      if Real.cos im < 0 then .negZero else .finite 0
  | .dirInf θ  =>
      open Classical in
      if Real.cos θ > 0 then .dirInf 0
      else if Real.cos θ < 0 then .finite 0
      else .nan
  | .nan       => .nan

/-- Directed lower-cut logarithm on `EmlDir`:
    - `ln(+0) = -∞`, `ln(-0) = -∞ - iπ`
    - `ln(+∞ + i·im) = +∞`, `ln(-∞ + i·im) = +∞ - iπ`
    - `ln(∞·e^{iθ}) = +∞ + i·θ'` where `θ' = -π` when `cos θ < 0` (negative real infinity) and `0` otherwise. -/
noncomputable def dirLowerLog : EmlDir → EmlDir
  | .finite z  => open Classical in if z = 0 then .negInf 0 else .finite (lowerLog z)
  | .negZero   => .negInf (-Real.pi)
  | .posInf _  => .posInf 0
  | .negInf _  => .posInf (-Real.pi)
  | .dirInf θ  => open Classical in if Real.cos θ < 0 then .posInf (-Real.pi) else .posInf 0
  | .nan       => .nan

/-- Directed subtraction on `EmlDir` (`+∞ - (-∞) = +∞`, `-∞ - (+∞) = -∞`,
    indeterminate `(+∞) - (+∞)` and `(-∞) - (-∞)` map to `nan`). -/
noncomputable def dirSub : EmlDir → EmlDir → EmlDir
  | .finite a,  .finite b  => .finite (a - b)
  | .finite a,  .negZero   => .finite a
  | .negZero,   .finite b  => open Classical in if b = 0 then .negZero else .finite (-b)
  | .negZero,   .negZero   => .finite 0
  | .finite a,  .posInf im => .negInf (a.im - im)
  | .finite a,  .negInf im => .posInf (a.im - im)
  | .negZero,   .posInf im => .negInf (-im)
  | .negZero,   .negInf im => .posInf (-im)
  | .posInf im, .finite b  => .posInf (im - b.im)
  | .negInf im, .finite b  => .negInf (im - b.im)
  | .posInf im, .negZero   => .posInf im
  | .negInf im, .negZero   => .negInf im
  | .posInf i1, .negInf i2 => .posInf (i1 - i2)
  | .negInf i1, .posInf i2 => .negInf (i1 - i2)
  | .dirInf θ,  .finite _  => .dirInf θ
  | .dirInf θ,  .negZero   => .dirInf θ
  | .dirInf θ,  .negInf _  => open Classical in if Real.cos θ > 0 then .posInf 0 else .nan
  | _,          _          => .nan

private theorem one_not_lt_zero : ¬ ((1 : ℝ) < 0) := by norm_num

private theorem dirExp_negInf_zero : dirExp (.negInf 0) = .finite 0 := by
  simp [dirExp, one_not_lt_zero]

private theorem dirExp_negInf_pi : dirExp (.negInf Real.pi) = .negZero := by
  simp [dirExp]

private theorem dirExp_dirInf_pi : dirExp (.dirInf Real.pi) = .finite 0 := by
  simp [dirExp]

/-- Directed EML operator: `dirEml x y = dirSub (dirExp x) (dirLowerLog y)`. -/
noncomputable def dirEml (x y : EmlDir) : EmlDir :=
  dirSub (dirExp x) (dirLowerLog y)

theorem dirEml_finite {x y : ℂ} (hy : y ≠ 0) :
    dirEml (.finite x) (.finite y) = .finite (eml x y) := by
  simp [dirEml, dirExp, dirLowerLog, dirSub, eml, hy]

noncomputable def dirEmlExp (x : EmlDir) : EmlDir :=
  dirEml x (.finite 1)

theorem dirEmlExp_eq (x : EmlDir) : dirEmlExp x = dirExp x := by
  cases x with
  | finite z => simp [dirEmlExp, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]
  | negZero => simp [dirEmlExp, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]
  | posInf im =>
    unfold dirEmlExp dirEml dirLowerLog
    simp only [one_ne_zero, ↓reduceIte, lowerLog_one]
    cases h : dirExp (.posInf im) <;> simp [dirSub]
  | negInf im =>
    unfold dirEmlExp dirEml dirLowerLog
    simp only [one_ne_zero, ↓reduceIte, lowerLog_one]
    cases h : dirExp (.negInf im) <;> simp [dirSub]
  | dirInf θ =>
    unfold dirEmlExp dirEml dirLowerLog
    simp only [one_ne_zero, ↓reduceIte, lowerLog_one]
    cases h : dirExp (.dirInf θ) <;> simp [dirSub]
  | nan => simp [dirEmlExp, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]

noncomputable def dirEmlLn (x : EmlDir) : EmlDir :=
  dirEml (.finite 1) (dirEml (dirEml (.finite 1) x) (.finite 1))

theorem dirEmlLn_zero : dirEmlLn (.finite 0) = .negInf 0 := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  simp [dirEmlLn, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one, he1_im, one_not_lt_zero]

theorem dirEmlLn_finite_ne_zero {x : ℂ} (hx : x ≠ 0) :
    dirEmlLn (.finite x) = .finite (Complex.log x) := by
  have h1 : dirEml (.finite 1) (.finite x) = .finite (eml 1 x) := dirEml_finite hx
  have h2 : dirEml (.finite (eml 1 x)) (.finite 1) = .finite (Complex.exp (eml 1 x)) := by
    rw [dirEml_finite one_ne_zero, eml, lowerLog_one, sub_zero]
  unfold dirEmlLn
  rw [h1, h2, dirEml_finite (Complex.exp_ne_zero _)]
  congr 1
  rw [← emlExp_eq (eml 1 x)]
  exact emlLn_eq_log x

noncomputable def dirRawSub (a b : EmlDir) : EmlDir :=
  dirEml (dirEmlLn a) (dirEmlExp b)

theorem dirRawSub_eq (a b : ℂ) :
    dirRawSub (.finite a) (.finite b) =
      .finite (a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) := by
  unfold dirRawSub
  rw [dirEmlExp_eq]
  change dirEml (dirEmlLn (.finite a)) (.finite (Complex.exp b)) = _
  by_cases ha : a = 0
  · subst ha
    rw [dirEmlLn_zero]
    simp [dirEml, dirExp_negInf_zero, dirLowerLog, dirSub, Complex.exp_ne_zero,
      lowerLog_exp_eq_sub_unwind]
    ring
  · rw [dirEmlLn_finite_ne_zero ha, dirEml_finite (Complex.exp_ne_zero b)]
    congr 1
    unfold eml
    rw [Complex.exp_log ha, lowerLog_exp_eq_sub_unwind]
    ring

noncomputable def dirEmlMul (a b : EmlDir) : EmlDir :=
  dirEmlExp (dirEml (.finite 1) (dirEmlExp (dirEml (dirEmlLn (dirEml (.finite 1) a)) b)))

/-- For any `b ≠ 0` with `0 ≤ b.re`, `0 ≤ Real.cos (eml 1 b).im` (since `|arg b| ≤ π/2`). -/
theorem cos_eml_one_im_nonneg_of_re_nonneg {b : ℂ} (hb : b ≠ 0) (hre : 0 ≤ b.re) :
    0 ≤ Real.cos (eml 1 b).im := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have hnotneg : ¬ isNegReal b := by intro ⟨h, _⟩; linarith
  have him : (eml 1 b).im = -b.arg := by
    simp [eml, he1_im, lowerLog_eq_log_of_not_isNegReal hnotneg, Complex.log_im]
  rw [him, Real.cos_neg]
  have hcos : Real.cos b.arg = b.re / ‖b‖ := Complex.cos_arg hb
  rw [hcos]
  exact div_nonneg hre (norm_nonneg b)

theorem dirEmlMul_eq {a : ℂ} (ha : a ≠ 0) (hare : 0 ≤ a.re) (b : ℂ) :
    dirEmlMul (.finite a) (.finite b) = .finite (a * b) := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  unfold dirEmlMul
  rw [dirEml_finite ha]
  by_cases hae : eml 1 a = 0
  · rw [hae, dirEmlLn_zero]
    by_cases hb : b = 0
    · subst hb
      simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im, one_not_lt_zero]
    · have h1 : dirEml (.negInf 0) (.finite b) = .finite (-lowerLog b) := by
        simp [dirEml, dirExp_negInf_zero, dirLowerLog, dirSub, hb]
      rw [h1, dirEmlExp_eq, dirEmlExp_eq]
      simp only [dirExp]
      rw [dirEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      have ha_eq : a = Complex.exp (Complex.exp 1) := by
        have hsub : Complex.exp 1 = lowerLog a := sub_eq_zero.mp hae
        rw [← exp_lowerLog ha, ← hsub]
      unfold eml
      rw [lowerLog_exp_eq_sub_unwind]
      set u : ℂ := -lowerLog b
      have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (Complex.exp 1 + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
        exp_lowerLog hb, ha_eq]
  · rw [dirEmlLn_finite_ne_zero hae]
    by_cases hb : b = 0
    · subst hb
      have hcos_nneg : ¬ (Real.cos (Complex.exp (Complex.log (eml 1 a))).im < 0) := by
        rw [Complex.exp_log hae]
        linarith [cos_eml_one_im_nonneg_of_re_nonneg ha hare]
      simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im, hcos_nneg, one_not_lt_zero]
    · rw [dirEml_finite hb, dirEmlExp_eq, dirEmlExp_eq]
      simp only [dirExp]
      rw [dirEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      unfold eml at hae ⊢
      rw [Complex.exp_log hae, lowerLog_exp_eq_sub_unwind]
      set u : ℂ := Complex.exp 1 - lowerLog a - lowerLog b
      have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
        exp_lowerLog ha, exp_lowerLog hb]

/-- For nonzero `a, b : ℂ`, `dirEmlMul (.finite a) (.finite b) = .finite (a * b)` with NO
    real-part restriction on `a` (since `b ≠ 0` never passes through `0 * a`). -/
theorem dirEmlMul_eq_of_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    dirEmlMul (.finite a) (.finite b) = .finite (a * b) := by
  unfold dirEmlMul
  rw [dirEml_finite ha]
  by_cases hae : eml 1 a = 0
  · rw [hae, dirEmlLn_zero]
    have h1 : dirEml (.negInf 0) (.finite b) = .finite (-lowerLog b) := by
      simp [dirEml, dirExp_negInf_zero, dirLowerLog, dirSub, hb]
    rw [h1, dirEmlExp_eq, dirEmlExp_eq]
    simp only [dirExp]
    rw [dirEml_finite (Complex.exp_ne_zero _)]
    dsimp only
    congr 1
    have ha_eq : a = Complex.exp (Complex.exp 1) := by
      have hsub : Complex.exp 1 = lowerLog a := sub_eq_zero.mp hae
      rw [← exp_lowerLog ha, ← hsub]
    unfold eml
    rw [lowerLog_exp_eq_sub_unwind]
    set u : ℂ := -lowerLog b
    have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
        (Complex.exp 1 + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [u]; ring
    rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
      exp_lowerLog hb, ha_eq]
  · rw [dirEmlLn_finite_ne_zero hae, dirEml_finite hb, dirEmlExp_eq, dirEmlExp_eq]
    simp only [dirExp]
    rw [dirEml_finite (Complex.exp_ne_zero _)]
    dsimp only
    congr 1
    unfold eml at hae ⊢
    rw [Complex.exp_log hae, lowerLog_exp_eq_sub_unwind]
    set u : ℂ := Complex.exp 1 - lowerLog a - lowerLog b
    have hrew : Complex.exp 1 - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
        (lowerLog a + lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [u]; ring
    rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_add,
      exp_lowerLog ha, exp_lowerLog hb]

/-- In `EmlDir`, `0 * 0 = 0` cleanly because `+∞ - (-∞) = +∞`! -/
theorem dirEmlMul_zero_zero : dirEmlMul (.finite 0) (.finite 0) = .finite 0 := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  unfold dirEmlMul dirEmlLn
  simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one, he1_im, one_not_lt_zero]

noncomputable def dirEmlDiv (a b : EmlDir) : EmlDir :=
  dirEmlExp (dirEml (dirEmlLn (dirEml (.finite 1) b)) (dirEmlExp (dirEml (.finite 1) a)))

/-- Helper: in `EmlDir`, dividing `0` by `b` yields `.finite 0` (`+0`) whenever `0 ≤ cos (Im (eml 1 b))`
    (in particular whenever `Re b ≥ 0`, such as `b = 1 + √(w)` or `b.re = 0`), and `.negZero` (`-0`)
    when `cos (Im (eml 1 b)) < 0`. -/
theorem dirEmlDiv_eq_of_cos_nonneg (a : ℂ) {b : ℂ} (hb : b ≠ 0)
    (hcos : 0 ≤ Real.cos (eml 1 b).im) :
    dirEmlDiv (.finite a) (.finite b) = .finite (a / b) := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  unfold dirEmlDiv
  rw [dirEml_finite hb]
  by_cases ha : a = 0
  · subst ha
    have h1a : dirEmlExp (dirEml (.finite 1) (.finite 0)) = .dirInf 0 := by
      simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im]
    rw [h1a]
    by_cases hbe : eml 1 b = 0
    · rw [hbe, dirEmlLn_zero]
      simp [dirEmlExp_eq, dirEml, dirExp_negInf_zero, dirLowerLog, dirSub, one_not_lt_zero]
    · rw [dirEmlLn_finite_ne_zero hbe]
      have hne_neg : ¬ (Real.cos (Complex.exp (Complex.log (eml 1 b))).im < 0) := by
        rw [Complex.exp_log hbe]; linarith
      simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, hne_neg, one_not_lt_zero]
  · rw [dirEml_finite ha, dirEmlExp_eq, dirEmlExp_eq]
    simp only [dirExp]
    by_cases hbe : eml 1 b = 0
    · rw [hbe, dirEmlLn_zero]
      have h1 : dirEml (.negInf 0) (.finite (Complex.exp (eml 1 a))) =
          .finite (-lowerLog (Complex.exp (eml 1 a))) := by
        simp [dirEml, dirExp_negInf_zero, dirLowerLog, dirSub, Complex.exp_ne_zero]
      rw [h1]
      dsimp only
      congr 1
      have hb_eq : b = Complex.exp (Complex.exp 1) := by
        have hsub : Complex.exp 1 = lowerLog b := sub_eq_zero.mp hbe
        rw [← exp_lowerLog hb, ← hsub]
      rw [lowerLog_exp_eq_sub_unwind]
      set u : ℂ := eml 1 a
      have hrew : -(u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a - Complex.exp 1) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u, eml]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub,
        exp_lowerLog ha, hb_eq]
    · rw [dirEmlLn_finite_ne_zero hbe, dirEml_finite (Complex.exp_ne_zero _)]
      dsimp only
      congr 1
      unfold eml at hbe ⊢
      rw [Complex.exp_log hbe, lowerLog_exp_eq_sub_unwind]
      set u : ℂ := Complex.exp 1 - lowerLog a
      have hrew : Complex.exp 1 - lowerLog b - (u - 2 * Real.pi * Complex.I * (lowerUnwind u : ℂ)) =
          (lowerLog a - lowerLog b) + (lowerUnwind u : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [u]; ring
      rw [hrew, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub,
        exp_lowerLog ha, exp_lowerLog hb]

theorem dirEmlDiv_eq (a : ℂ) {b : ℂ} (hb : b ≠ 0) (hre : 0 ≤ b.re) :
    dirEmlDiv (.finite a) (.finite b) = .finite (a / b) :=
  dirEmlDiv_eq_of_cos_nonneg a hb (cos_eml_one_im_nonneg_of_re_nonneg hb hre)

noncomputable def dirEmlSqr (b : EmlDir) : EmlDir :=
  dirEmlMul b b

noncomputable def dirEmlSqrt (x : EmlDir) : EmlDir :=
  dirEmlExp (dirEmlDiv (dirEmlLn x) (.finite 2))

/-- The key theorem of `docs/rotsub.md` ("Zero on the scaled path"):
    in `EmlDir` with directed infinities and `-0`, `√0 = 0` via the chain:
      `ln 0 = -∞` → `ln(-∞) = +∞ - iπ` → `exp(-∞ + iπ) = -0` →
      `ln(-0) = -∞ - iπ` → `exp(+∞ + iπ) = -∞` → `exp(-∞) = 0`. -/
theorem dirEmlSqrt_zero : dirEmlSqrt (.finite 0) = .finite 0 := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have h2_ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have h12_ne : eml 1 2 ≠ 0 := by
    intro h
    have hsub : Complex.exp 1 = lowerLog 2 := sub_eq_zero.mp h
    have heq : (2 : ℂ) = Complex.exp (Complex.exp 1) := by
      rw [← exp_lowerLog h2_ne, ← hsub]
    have hre : (2 : ℝ) = Real.exp (Real.exp 1) := by
      have := congrArg Complex.re heq
      simpa [← Complex.ofReal_one, ← Complex.ofReal_exp] using this
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 1 < Real.exp (Real.exp 1) := by
      have := Real.add_one_lt_exp (ne_of_gt (Real.exp_pos 1)); linarith
    linarith
  have h12_im : (eml 1 2).im = 0 := by
    unfold eml
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, lowerLog_ofReal_pos (by norm_num)]
    rw [Complex.sub_im, he1_im, Complex.ofReal_im, sub_zero]
  unfold dirEmlSqrt
  rw [dirEmlLn_zero]
  unfold dirEmlDiv
  rw [dirEml_finite h2_ne, dirEmlLn_finite_ne_zero h12_ne]
  have hstep1 : dirEml (.finite 1) (.negInf 0) = .negInf Real.pi := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im]
  rw [hstep1, dirEmlExp_eq, dirEmlExp_eq]
  have hinner : dirEmlExp (.negInf Real.pi) = .negZero := by
    rw [dirEmlExp_eq, dirExp_negInf_pi]
  rw [hinner]
  have hstep3 : dirEml (.finite (Complex.log (eml 1 2))) .negZero = .posInf Real.pi := by
    have hexp_im : (Complex.exp (Complex.log (eml 1 2))).im = 0 := by
      rw [Complex.exp_log h12_ne, h12_im]
    simp [dirEml, dirExp, dirLowerLog, dirSub, hexp_im]
  rw [hstep3]
  change dirExp (.dirInf Real.pi) = .finite 0
  exact dirExp_dirInf_pi

theorem dirEmlSqrt_finite {w : ℂ} (hw : w ≠ 0) :
    dirEmlSqrt (.finite w) = .finite (w ^ ((1 : ℂ) / 2)) := by
  unfold dirEmlSqrt
  rw [dirEmlLn_finite_ne_zero hw, dirEmlDiv_eq _ two_ne_zero (by norm_num), dirEmlExp_eq]
  simp only [dirExp]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hw]
  congr 1
  ring

noncomputable def dirRotSub (c a b : EmlDir) : EmlDir :=
  dirEmlDiv (dirRawSub (dirEmlMul c (dirRawSub a b)) (dirEmlMul c (dirRawSub b b))) c

theorem dirRotSub_eq_sub {c : ℂ} (hc_re : c.re = 0) (hc_ne : c ≠ 0) (a b : ℂ) :
    dirRotSub (.finite c) (.finite a) (.finite b) = .finite (a - b) := by
  unfold dirRotSub
  rw [dirRawSub_eq a b, dirRawSub_eq b b, sub_self, zero_add]
  rw [dirEmlMul_eq hc_ne (by linarith), dirEmlMul_eq hc_ne (by linarith), dirRawSub_eq]
  have hm2_im : (c * (2 * Real.pi * Complex.I * (lowerUnwind b : ℂ))).im = 0 :=
    mul_unwind_im_zero hc_re (lowerUnwind b)
  rw [lowerUnwind_of_im_zero hm2_im]
  have hcancel : c * (a - b + 2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) -
      c * (2 * Real.pi * Complex.I * (lowerUnwind b : ℂ)) +
      2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) = c * (a - b) := by
    push_cast; ring
  rw [hcancel, dirEmlDiv_eq _ hc_ne (by linarith), mul_div_cancel_left₀ _ hc_ne]

noncomputable def dirScale (c b : EmlDir) : EmlDir :=
  dirRotSub c (dirEmlSqrt (dirEmlSqr b)) (.finite (-1))

noncomputable def dirScaledSub (c a b : EmlDir) : EmlDir :=
  let k := dirScale c b
  dirEmlMul k (dirRotSub c (dirEmlDiv a k) (dirEmlDiv b k))

/-- Full scaled rotated subtraction in `EmlDir`:
    for ANY nonzero purely imaginary `c` and ALL `a, b : ℂ` — INCLUDING `b = 0` —
    `dirScaledSub (.finite c) (.finite a) (.finite b) = .finite (a - b)`. -/
theorem dirScaledSub_eq_sub {c : ℂ} (hc_re : c.re = 0) (hc_ne : c ≠ 0) (a b : ℂ) :
    dirScaledSub (.finite c) (.finite a) (.finite b) = .finite (a - b) := by
  by_cases hb : b = 0
  · subst hb
    have hk : dirScale (.finite c) (.finite 0) = .finite 1 := by
      unfold dirScale dirEmlSqr
      rw [dirEmlMul_zero_zero, dirEmlSqrt_zero, dirRotSub_eq_sub hc_re hc_ne]
      norm_num
    unfold dirScaledSub
    dsimp only
    rw [hk, dirEmlDiv_eq a one_ne_zero (by norm_num), dirEmlDiv_eq 0 one_ne_zero (by norm_num),
      dirRotSub_eq_sub hc_re hc_ne, dirEmlMul_eq one_ne_zero (by norm_num)]
    congr 1
    ring
  · have hb2 : b * b ≠ 0 := mul_ne_zero hb hb
    have hk : dirScale (.finite c) (.finite b) = .finite (1 + (b * b) ^ ((1 : ℂ) / 2)) := by
      unfold dirScale dirEmlSqr
      rw [dirEmlMul_eq_of_ne_zero hb hb, dirEmlSqrt_finite hb2, dirRotSub_eq_sub hc_re hc_ne]
      congr 1
      ring
    have hk_ne : (1 : ℂ) + (b * b) ^ ((1 : ℂ) / 2) ≠ 0 := one_add_cpow_half_ne_zero (b * b)
    have hk_re : 0 ≤ ((1 : ℂ) + (b * b) ^ ((1 : ℂ) / 2)).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith [re_cpow_half_nonneg (b * b)]
    unfold dirScaledSub
    dsimp only
    rw [hk, dirEmlDiv_eq a hk_ne hk_re, dirEmlDiv_eq b hk_ne hk_re,
      dirRotSub_eq_sub hc_re hc_ne, dirEmlMul_eq hk_ne hk_re]
    congr 1
    have hmul : (1 + (b * b) ^ ((1 : ℂ) / 2)) * (a / (1 + (b * b) ^ ((1 : ℂ) / 2)) -
        b / (1 + (b * b) ^ ((1 : ℂ) / 2))) = a - b := by
      rw [mul_sub, mul_div_cancel₀ _ hk_ne, mul_div_cancel₀ _ hk_ne]
    exact hmul

end Eml.DirectedInf
