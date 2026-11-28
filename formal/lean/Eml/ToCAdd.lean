import Eml.ToCSqrt
import Eml.ToCClean

namespace Eml
open Eml Eml.DirectedInf Eml.AppSub Eml.AppOps
set_option linter.unnecessarySeqFocus false


/-- `shortSub H v` sees `H` and `v` only through `exp`. -/
theorem shortSub_congr {H H' v v' : EmlDir} (hH : dirExp H = dirExp H') (hv : dirExp v = dirExp v') :
    shortSub H v = shortSub H' v' := by
  unfold shortSub dirEml
  rw [dirEmlExp_eq, dirEmlExp_eq, hH, hv]

theorem toC_mul_of_toC {u w : EmlDir} {p q : ℂ} (hu : toC u = some p) (hw : toC w = some q) :
    toC (dirEmlMul u w) = some (p * q) := by
  rcases toC_eq hu with rfl | ⟨rfl, rfl⟩ <;> rcases toC_eq hw with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlMul p q
  · rw [mul_zero]; exact toC_dirEmlMul_negZero p
  · rw [dirEmlMul_negZero_left]; exact toC_dirEmlMul 0 q
  · rw [dirEmlMul_negZero_left, mul_zero]; exact toC_dirEmlMul_negZero 0

theorem sqrt_of_toC {u : EmlDir} {p : ℂ} (hu : toC u = some p) :
    dirEmlSqrt u = .finite (p ^ ((1 : ℂ) / 2)) := by
  rcases toC_eq hu with rfl | ⟨rfl, rfl⟩
  · exact dirEmlSqrt_all p
  · rw [dirEmlSqrt_negZero', Complex.zero_cpow (by norm_num)]

theorem toC_div_of_toC {u : EmlDir} {p κ : ℂ} (hu : toC u = some p) (hκ : κ ≠ 0) :
    toC (dirEmlDiv u (.finite κ)) = some (p / κ) := by
  rcases toC_eq hu with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlDiv p hκ
  · rw [zero_div]; exact toC_dirEmlDiv_negZero_left hκ

theorem toC_dirSub_finite {Z : EmlDir} {z : ℂ} (hZ : toC Z = some z) (l : ℂ) :
    toC (dirSub Z (.finite l)) = some (z - l) := by
  rcases toC_eq hZ with rfl | ⟨rfl, rfl⟩
  · rfl
  · by_cases hl : l = 0
    · subst hl; simp [dirSub, toC]
    · simp [dirSub, hl, toC]

theorem toC_shortSub {H v : EmlDir} {h β : ℂ} (hH : toC (dirExp H) = some h) (hv : toC v = some β) :
    toC (shortSub H v) = some (h - lowerLog (Complex.exp β)) := by
  unfold shortSub dirEml
  rw [dirEmlExp_eq, dirExp_of_toC hv]
  simp only [dirLowerLog, if_neg (Complex.exp_ne_zero β)]
  exact toC_dirSub_finite hH _

/-- `iπ · T` depends only on `toC T` (`iπ · (−0) = +0`, landed). -/
theorem mul_ipi_of_toC {T : EmlDir} {t : ℂ} (hT : toC T = some t) :
    dirEmlMul (.finite (Real.pi * Complex.I)) T = .finite (Real.pi * Complex.I * t) := by
  have hc_re : ((Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have hc_ne : (Real.pi : ℂ) * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases toC_eq hT with rfl | ⟨rfl, rfl⟩
  · exact dirEmlMul_eq hc_ne (le_of_eq hc_re.symm) t
  · rw [dirEmlMul_ipi_negZero, mul_zero]

/-- **The general rotation `appSubGen` is exactly `a − b` for operands read by `toC`** (any of them may be `−0`). -/
theorem appSubGen_of_toC {x yk yb : EmlDir} {a bk b : ℂ}
    (hx : toC x = some a) (hk : toC yk = some bk) (hb : toC yb = some b) :
    appSubGen x yk yb = .finite (a - b) := by
  rw [← appSubGen_finite a bk b]
  unfold appSubGen
  dsimp only
  have hK : shortSub (sqrtBody (dirEmlSqr yk)) dirCNegOne =
      shortSub (sqrtBody (dirEmlSqr (.finite bk))) dirCNegOne := by
    apply shortSub_congr _ rfl
    rw [← dirEmlExp_eq, ← dirEmlExp_eq]
    show dirEmlSqrt _ = dirEmlSqrt _
    unfold dirEmlSqr
    rw [sqrt_of_toC (toC_mul_of_toC hk hk), sqrt_of_toC (toC_mul_of_toC rfl rfl)]
  obtain ⟨s, hs_re, hK'⟩ := appScale_finite bk
  have hκ : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [hK, hK', dirCIpi_eq]
  have hb1 : toC (dirEmlDiv yb (.finite (s + 1))) = some (b / (s + 1)) := toC_div_of_toC hb hκ
  have hb1' : toC (dirEmlDiv (.finite b) (.finite (s + 1))) = some (b / (s + 1)) := toC_div_of_toC rfl hκ
  have hTx : toC (shortSub (divBody x (.finite (s + 1))) (dirEmlDiv yb (.finite (s + 1)))) =
      some (a / (s + 1) - lowerLog (Complex.exp (b / (s + 1)))) :=
    toC_shortSub (by rw [← dirEmlExp_eq]; exact toC_div_of_toC hx hκ) hb1
  have hTx' : toC (shortSub (divBody (.finite a) (.finite (s + 1))) (dirEmlDiv (.finite b) (.finite (s + 1)))) =
      some (a / (s + 1) - lowerLog (Complex.exp (b / (s + 1)))) :=
    toC_shortSub (by rw [← dirEmlExp_eq]; exact toC_div_of_toC rfl hκ) hb1'
  have hTy : toC (shortSub (divBody yb (.finite (s + 1))) (dirEmlDiv yb (.finite (s + 1)))) =
      some (b / (s + 1) - lowerLog (Complex.exp (b / (s + 1)))) :=
    toC_shortSub (by rw [← dirEmlExp_eq]; exact hb1) hb1
  have hTy' : toC (shortSub (divBody (.finite b) (.finite (s + 1))) (dirEmlDiv (.finite b) (.finite (s + 1)))) =
      some (b / (s + 1) - lowerLog (Complex.exp (b / (s + 1)))) :=
    toC_shortSub (by rw [← dirEmlExp_eq]; exact hb1') hb1'
  have hmid : shortSub (mulBody (.finite (Real.pi * Complex.I))
        (shortSub (divBody x (.finite (s + 1))) (dirEmlDiv yb (.finite (s + 1)))))
        (dirEmlMul (.finite (Real.pi * Complex.I))
          (shortSub (divBody yb (.finite (s + 1))) (dirEmlDiv yb (.finite (s + 1))))) =
      shortSub (mulBody (.finite (Real.pi * Complex.I))
        (shortSub (divBody (.finite a) (.finite (s + 1))) (dirEmlDiv (.finite b) (.finite (s + 1)))))
        (dirEmlMul (.finite (Real.pi * Complex.I))
          (shortSub (divBody (.finite b) (.finite (s + 1))) (dirEmlDiv (.finite b) (.finite (s + 1))))) := by
    apply shortSub_congr
    · rw [← dirEmlExp_eq, ← dirEmlExp_eq]
      show dirEmlMul _ _ = dirEmlMul _ _
      rw [mul_ipi_of_toC hTx, mul_ipi_of_toC hTx']
    · rw [mul_ipi_of_toC hTy, mul_ipi_of_toC hTy']
  rw [hmid]

theorem appSub_of_toC {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    appSub v w = .finite (a - b) :=
  appSubGen_of_toC hv hw hw

theorem appAdd_of_toC {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    appAdd v w = .finite (a + b) := by
  unfold appAdd
  rw [dirCNegOne_eq_negOne, appSubGen_of_toC hv hw (toC_mul_of_toC rfl hw)]
  congr 1; ring

/-- `sub_correct_toC` without `hv0`, `hw0` (exact form, as landed). -/
theorem sub_correct_toC' {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    evalTok (.finite 1) v w dirEml appSubToks [] = some [.finite (a - b)] := by
  rw [appSubToks_eval, appSub_of_toC hv hw]

/-- `add_correct_toC` without `hv0`, `hw0` (exact form, as landed). -/
theorem add_correct_toC' {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    evalTok (.finite 1) v w dirEml addToks [] = some [.finite (a + b)] := by
  rw [addToks_eval, appAdd_of_toC hv hw]



theorem sub_correct_toC {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    evalTok (.finite 1) v w dirEml appSubToks [] = some [.finite (a - b)] :=
  sub_correct_toC' hv hw

theorem add_correct_toC {v w : EmlDir} {a b : ℂ} (hv : toC v = some a) (hw : toC w = some b) :
    evalTok (.finite 1) v w dirEml addToks [] = some [.finite (a + b)] :=
  add_correct_toC' hv hw
end Eml
