import Eml.AppOps

namespace Eml
open Eml Eml.DirectedInf Eml.AppSub Eml.AppOps

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
theorem one_nlt : ¬ ((1 : ℝ) < 0) := by norm_num

/-- ln of any `posInf` forgets its phase. -/
theorem dirEmlLn_posInf (ψ : ℝ) : dirEmlLn (.posInf ψ) = .posInf 0 := by
  simp [dirEmlLn, dirEml, dirExp, dirLowerLog, dirSub, he1_im, lowerLog_one, one_nlt, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, dirEmlExp_eq]

theorem dirEml_one_zeroLike (v : EmlDir) (hv : v = .finite 0 ∨ v = .negZero) :
    ∃ ψ, dirEml (.finite 1) v = .posInf ψ := by
  rcases hv with rfl | rfl <;> simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im, one_nlt, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, dirEmlExp_eq]

/-- L2: the first slot of `mul` cannot see the sign of zero. -/
theorem dirEmlMul_negZero_left (b : EmlDir) : dirEmlMul .negZero b = dirEmlMul (.finite 0) b := by
  obtain ⟨ψ, h1⟩ := dirEml_one_zeroLike .negZero (Or.inr rfl)
  obtain ⟨ψ', h2⟩ := dirEml_one_zeroLike (.finite 0) (Or.inl rfl)
  unfold dirEmlMul; rw [h1, h2, dirEmlLn_posInf, dirEmlLn_posInf]

/-- L1 (item 6): `0 · c = +0` for every finite `c`. -/
theorem dirEmlMul_zero_left' (c : ℂ) : dirEmlMul (.finite 0) (.finite c) = .finite 0 := by
  obtain ⟨ψ, h1⟩ := dirEml_one_zeroLike (.finite 0) (Or.inl rfl)
  unfold dirEmlMul; rw [h1, dirEmlLn_posInf]
  by_cases hc : c = 0
  · subst hc; simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im, lowerLog_one, one_nlt, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, dirEmlExp_eq]
  · simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im, lowerLog_one, hc, one_nlt, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, dirEmlExp_eq]

theorem tail_negInf (c : ℂ) (θ : ℝ) :
    toC (dirEmlExp (dirEml (.finite 1) (dirEmlExp (dirSub (.finite c) (.negInf θ))))) = some 0 := by
  simp only [dirSub, dirEmlExp_eq, dirExp, dirEml, dirLowerLog]
  split_ifs <;> simp [toC, dirSub, dirExp, he1_im] <;> split_ifs <;> simp [toC]

/-- D1: the second slot at `−0` still gives a zero. -/
theorem toC_dirEmlMul_negZero (a : ℂ) : toC (dirEmlMul (.finite a) .negZero) = some 0 := by
  unfold dirEmlMul
  by_cases ha : a = 0
  · subst ha
    obtain ⟨ψ, h1⟩ := dirEml_one_zeroLike (.finite 0) (Or.inl rfl)
    rw [h1, dirEmlLn_posInf]
    simp [dirEmlExp_eq, dirEml, dirExp, dirLowerLog, dirSub, he1_im, lowerLog_one, toC, one_nlt, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi, dirEmlExp_eq]
  · rw [dirEml_finite ha]
    rw [show dirEml (dirEmlLn (.finite (eml 1 a))) .negZero
        = dirSub (dirExp (dirEmlLn (.finite (eml 1 a)))) (dirLowerLog .negZero) from rfl,
      dirExp_dirEmlLn_finite]
    simp only [dirLowerLog]
    exact tail_negInf _ _

/-- D1': same with `+0` (landed `toC_dirEmlMul_zero_right`) — so `mul` is `toC`-blind in slot 2. -/
theorem toC_dirEmlMul_zeroLike (a : ℂ) (v : EmlDir) (hv : toC v = some 0) :
    toC (dirEmlMul (.finite a) v) = some 0 := by
  rcases toC_eq hv with h | ⟨h, -⟩
  · subst h; exact toC_dirEmlMul_zero_right a
  · subst h; exact toC_dirEmlMul_negZero a


/-! ### div -/

/-- The divisor slot of `div` cannot see the sign of zero (exact). -/
theorem dirEmlDiv_negZero_right (a : EmlDir) : dirEmlDiv a .negZero = dirEmlDiv a (.finite 0) := by
  obtain ⟨ψ, h1⟩ := dirEml_one_zeroLike .negZero (Or.inr rfl)
  obtain ⟨ψ', h2⟩ := dirEml_one_zeroLike (.finite 0) (Or.inl rfl)
  unfold dirEmlDiv; rw [h1, h2, dirEmlLn_posInf, dirEmlLn_posInf]

/-- `(−0) / b` is a zero for `b ≠ 0` (it can be `−0`). -/
theorem toC_dirEmlDiv_negZero_left {b : ℂ} (hb : b ≠ 0) :
    toC (dirEmlDiv .negZero (.finite b)) = some 0 := by
  unfold dirEmlDiv
  rw [dirEml_finite hb, dirEml_one_negZero, dirEmlExp_eq (.posInf _)]
  rw [show dirEml (dirEmlLn (.finite (eml 1 b))) (dirExp (.posInf Real.pi))
      = dirSub (dirExp (dirEmlLn (.finite (eml 1 b)))) (dirLowerLog (dirExp (.posInf Real.pi))) from rfl,
    dirExp_dirEmlLn_finite]
  simp [dirExp, dirLowerLog, dirSub, Real.cos_pi, dirEmlExp_eq]
  split_ifs <;> simp [toC]

theorem toC_dirEmlDiv_zeroLike_left {v : EmlDir} {b : ℂ} (hv : toC v = some 0) (hb : b ≠ 0) :
    toC (dirEmlDiv v (.finite b)) = some 0 := by
  rcases toC_eq hv with h | ⟨h, -⟩
  · subst h; exact toC_dirEmlDiv_zero_left hb
  · subst h; exact toC_dirEmlDiv_negZero_left hb

/-! ### `c · (−∞)` does not see the phase `0` vs `π` (for `c ≠ 0`) -/

theorem dirEmlMul_negInf_pi {c : ℂ} (hc : c ≠ 0) :
    dirEmlMul (.finite c) (.negInf Real.pi) = dirEmlMul (.finite c) (.negInf 0) := by
  unfold dirEmlMul
  rw [dirEml_finite hc]
  have hd : ∀ θ : ℝ, dirEml (dirEmlLn (.finite (eml 1 c))) (.negInf θ)
      = dirSub (dirExp (dirEmlLn (.finite (eml 1 c)))) (dirLowerLog (.negInf θ)) := fun _ => rfl
  rw [hd, hd, dirExp_dirEmlLn_finite]
  have h1 : dirLowerLog (.negInf Real.pi) = .posInf Real.pi := by simp [dirLowerLog, Real.pi_pos]
  have h2 : dirLowerLog (.negInf 0) = .posInf (-Real.pi) := by simp [dirLowerLog]
  rw [h1, h2]
  simp only [dirSub]
  have hcos : Real.cos ((eml 1 c).im - Real.pi) = Real.cos ((eml 1 c).im - -Real.pi) := by
    rw [Real.cos_sub_pi, sub_neg_eq_add, Real.cos_add_pi]
  have : dirEmlExp (.negInf ((eml 1 c).im - Real.pi)) = dirEmlExp (.negInf ((eml 1 c).im - -Real.pi)) := by
    simp only [dirEmlExp_eq, dirExp, hcos]
  rw [this]

/-! ### raw subtraction: `ln(±0)` then `exp` again -/

theorem dirRawSub_negZero_left (b : ℂ) (hb : lowerLog (Complex.exp b) ≠ 0) :
    dirRawSub .negZero (.finite b) = dirRawSub (.finite 0) (.finite b) := by
  unfold dirRawSub
  rw [dirEmlLn_negZero, dirEmlLn_zero, dirEmlExp_eq]
  simp [dirEml, dirExp, dirLowerLog, dirSub, Real.cos_pi, Real.cos_zero, one_nlt, Complex.exp_ne_zero, hb]

theorem appRot_negZero (b : ℂ) (hb : lowerLog (Complex.exp b) ≠ 0) :
    appRot .negZero (.finite b) = appRot (.finite 0) (.finite b) := by
  unfold appRot; rw [dirRawSub_negZero_left b hb]

theorem lowerLog_exp_ne {b : ℂ} (him : b.im = 0) (hb : b ≠ 0) : lowerLog (Complex.exp b) ≠ 0 := by
  rw [lowerLog_exp_of_im_zero him]; exact hb

/-! ### Cleaned `_correct_toC` statements: no `≠ −0` hypotheses -/

theorem mul_correct_toC' {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) :
    valueOf (evalTok (.finite 1) v w dirEml mulToks []) = some (a * b) := by
  rw [mulToks_eval]; show toC _ = _
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩ <;> rcases toC_eq hw with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlMul a b
  · rw [mul_zero]; exact toC_dirEmlMul_negZero a
  · rw [dirEmlMul_negZero_left]; exact toC_dirEmlMul 0 b
  · rw [dirEmlMul_negZero_left, mul_zero]; exact toC_dirEmlMul_negZero 0

theorem div_correct_toC' {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) (hb : b ≠ 0) :
    valueOf (evalTok (.finite 1) v w dirEml divToks []) = some (a / b) := by
  rw [toC_of_ne_zero hw hb, divToks_eval]; show toC _ = _
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlDiv a hb
  · rw [zero_div]; exact toC_dirEmlDiv_negZero_left hb

theorem neg_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    valueOf (evalTok (.finite 1) v y dirEml negToks []) = some (-a) := by
  rw [negToks_eval, dirCNegOne_eq_negOne]; show toC _ = _
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [toC_dirEmlMul]; simp
  · rw [neg_zero]; exact toC_dirEmlMul_negZero _

theorem twoMul_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    valueOf (evalTok (.finite 1) v y dirEml twoMulToks []) = some (2 * a) := by
  rw [twoMulToks_eval, dirCTwo_eq_two]; show toC _ = _
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlMul 2 a
  · rw [mul_zero]; exact toC_dirEmlMul_negZero _

theorem divTwo_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    valueOf (evalTok (.finite 1) v y dirEml divTwoToks []) = some (a / 2) := by
  rw [divTwoToks_eval, dirCTwo_eq_two]; show toC _ = _
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · exact toC_dirEmlDiv a two_ne_zero
  · rw [zero_div]; exact toC_dirEmlDiv_negZero_left two_ne_zero

theorem eml_one_two_im : (eml 1 2).im = 0 := by
  rw [eml, Complex.sub_im, he1_im, lowerLog_eq_log_of_not_isNegReal]
  · rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.log_im, Complex.arg_ofReal_of_nonneg (by norm_num)]; simp
  · simp [isNegReal]

/-- `twoMul(−0) = −0` exactly: the exact-form `twoMul_correct_toC` cannot drop `hv0`. -/
theorem twoMul_negZero : dirEmlMul dirCTwo .negZero = .negZero := by
  rw [dirCTwo_eq_two]
  unfold dirEmlMul
  rw [dirEml_finite two_ne_zero]
  rw [show dirEml (dirEmlLn (.finite (eml 1 2))) .negZero
      = dirSub (dirExp (dirEmlLn (.finite (eml 1 2)))) (dirLowerLog .negZero) from rfl,
    dirExp_dirEmlLn_finite]
  simp [dirSub, dirLowerLog, dirEmlExp_eq, dirExp, dirEml, eml_one_two_im, he1_im, Real.cos_pi,
    Real.sin_pi, lowerLog_one, one_nlt]

/-- `(−0)/2 = −0` exactly: same for `divTwo`. -/
theorem divTwo_negZero : dirEmlDiv .negZero dirCTwo = .negZero := by
  rw [dirCTwo_eq_two]
  unfold dirEmlDiv
  rw [dirEml_finite two_ne_zero, dirEml_one_negZero, dirEmlExp_eq (.posInf _)]
  rw [show dirEml (dirEmlLn (.finite (eml 1 2))) (dirExp (.posInf Real.pi))
      = dirSub (dirExp (dirEmlLn (.finite (eml 1 2)))) (dirLowerLog (dirExp (.posInf Real.pi))) from rfl,
    dirExp_dirEmlLn_finite]
  simp [dirExp, dirLowerLog, dirSub, Real.cos_pi, dirEmlExp_eq, eml_one_two_im]

theorem sq_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml sqToks [] = some [.finite (a ^ 2)] := by
  rw [sqToks_eval]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [dirEmlSq]
  · rw [dirEmlLn_negZero, dirCTwo_eq_two, dirEmlMul_negInf_pi two_ne_zero, ← dirEmlLn_zero,
      ← dirCTwo_eq_two, dirEmlSq]

theorem cube_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml cubeToks [] = some [.finite (a ^ 3)] := by
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · exact cube_correct_finite hv (by simp) y
  · rw [cubeToks_eval, dirEmlLn_negZero, dirConst_three,
      dirEmlMul_negInf_pi (by norm_num), ← dirEmlLn_zero, ← dirConst_three, ← cubeToks_eval]
    exact cube_correct_finite (v := .finite 0) rfl (by simp) y

theorem pow_correct_toC' {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) (ha : a ≠ 0) :
    evalTok (.finite 1) v w dirEml powToks [] = some [.finite (a ^ b)] := by
  rw [toC_of_ne_zero hv ha, powToks_eval]
  rcases toC_eq hw with rfl | ⟨rfl, rfl⟩
  · rw [dirEmlPow ha]
  · rw [dirEmlMul_negZero_left, dirEmlPow ha]

theorem expE_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml expEToks [] = some [.finite (Complex.exp a)] := by
  rw [expEToks_eval]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [dirEmlExpE]
  · rw [dirEmlMul_negZero_left, dirEmlExpE]

theorem mulTwo_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml mulTwoToks [] = some [.finite (a * 2)] := by
  rw [mulTwoToks_eval]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [dirEmlMulTwo]
  · rw [dirEmlMul_negZero_left, dirEmlMulTwo]

theorem subOne_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml subOneToks [] = some [.finite (a - 1)] := by
  rw [subOneToks_eval]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [appRot_finite]
  · rw [appRot_negZero 1 (lowerLog_exp_ne (by simp) one_ne_zero), appRot_finite]

theorem addOne_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml addOneToks [] = some [.finite (a + 1)] := by
  rw [addOneToks_eval, dirCNegOne_eq_negOne]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [appRot_finite, sub_neg_eq_add]
  · rw [appRot_negZero (-1) (lowerLog_exp_ne (by simp) (by norm_num)),
      appRot_finite, sub_neg_eq_add]

theorem subTwo_correct_toC' {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml subTwoToks [] = some [.finite (a - 2)] := by
  rw [subTwoToks_eval, dirCTwo_eq_two]
  rcases toC_eq hv with rfl | ⟨rfl, rfl⟩
  · rw [appRot_finite]
  · rw [appRot_negZero 2 (lowerLog_exp_ne (by simp) two_ne_zero), appRot_finite]


/-! ### sinh / cosh without the `≠ 0` hypotheses -/

theorem dirEmlMul_of_toC_left {P : EmlDir} {p c : ℂ} (h : toC P = some p) (hc : c ≠ 0) :
    dirEmlMul P (.finite c) = .finite (p * c) := by
  by_cases hp : p = 0
  · subst hp
    rcases toC_eq h with rfl | ⟨rfl, -⟩
    · rw [zero_mul, dirEmlMul_zero_left']
    · rw [dirEmlMul_negZero_left, zero_mul, dirEmlMul_zero_left']
  · rw [toC_of_ne_zero h hp, dirEmlMul_eq_of_ne_zero hp hc]

theorem sinh_correct' (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml sinhToks [] = some [.finite (Complex.sinh a)] := by
  have htwo : evalTok (.finite 1) (.finite a) y dirEml sinhTwoX [] = some [.finite (a + a)] := by
    rw [sinhTwoX, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hneg : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst sinhTwoX [.one] negToks) [] =
      some [dirEmlMul (.finite (-1)) (.finite (a + a))] := by
    rw [evalAt htwo (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne]
  have hexp : evalTok (.finite 1) (.finite a) y dirEml sinhEm2 [] =
      some [.finite (Complex.exp (-(a + a)))] := by
    rw [sinhEm2, evalAt hneg (evalTok_oneTok _ _),
      exp_correct_toC (by rw [toC_dirEmlMul, neg_one_mul])]
  have hgap : evalTok (.finite 1) (.finite a) y dirEml sinhGap [] =
      some [.finite (1 - Complex.exp (-(a + a)))] := by
    rw [sinhGap, evalAt (evalTok_oneTok _ _) hexp, appSubToks_eval, appSub_finite]
  have hexpa : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] expToks) [] =
      some [.finite (Complex.exp a)] := by
    rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
    rfl
  rw [sinhToks, evalAt (by rw [sinhProd, evalAt hexpa hgap, mulToks_eval]) (halfToks_eval _ _),
    mulToks_eval, dirCHalf_eq, dirEmlMul_of_toC_left (toC_dirEmlMul _ _) (by norm_num), sinh_formula]

theorem cosh_correct' (a : ℂ) (y : EmlDir) :
    evalTok (.finite 1) (.finite a) y dirEml coshToks [] = some [.finite (Complex.cosh a)] := by
  have htwo : evalTok (.finite 1) (.finite a) y dirEml sinhTwoX [] = some [.finite (a + a)] := by
    rw [sinhTwoX, evalAt (evalTok_x _ _) (evalTok_x _ _), addToks_eval, appAdd_finite]
  have hneg2 : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst sinhTwoX [.one] negToks) [] =
      some [dirEmlMul (.finite (-1)) (.finite (a + a))] := by
    rw [evalAt htwo (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne]
  have hexp : evalTok (.finite 1) (.finite a) y dirEml coshEm2 [] =
      some [.finite (Complex.exp (-(a + a)))] := by
    rw [coshEm2, sinhEm2, evalAt hneg2 (evalTok_oneTok _ _),
      exp_correct_toC (by rw [toC_dirEmlMul, neg_one_mul])]
  have hneg : evalTok (.finite 1) (.finite a) y dirEml coshNeg [] =
      some [.finite (-Complex.exp (-(a + a)))] := by
    rw [coshNeg, evalAt hexp (evalTok_oneTok _ _), negToks_eval, dirCNegOne_eq_negOne,
      dirEmlMul_eq_of_ne_zero (by norm_num) (Complex.exp_ne_zero _), neg_one_mul]
  have hgap : evalTok (.finite 1) (.finite a) y dirEml coshGap [] =
      some [.finite (1 - -Complex.exp (-(a + a)))] := by
    rw [coshGap, evalAt (evalTok_oneTok _ _) hneg, appSubToks_eval, appSub_finite]
  have hexpa : evalTok (.finite 1) (.finite a) y dirEml (Tok.subst [.x] [.one] expToks) [] =
      some [.finite (Complex.exp a)] := by
    rw [evalAt (evalTok_x _ _) (evalTok_oneTok _ _), expToks_eval, dirEmlExp_eq]
    rfl
  rw [coshToks, evalAt (by rw [coshProd, evalAt hexpa hgap, mulToks_eval]) (halfToks_eval _ _),
    mulToks_eval, dirCHalf_eq, dirEmlMul_of_toC_left (toC_dirEmlMul _ _) (by norm_num), cosh_formula]


theorem mul_correct_toC {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) :
    valueOf (evalTok (.finite 1) v w dirEml mulToks []) = some (a * b) :=
  mul_correct_toC' hv hw

theorem div_correct_toC {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) (hb : b ≠ 0) :
    valueOf (evalTok (.finite 1) v w dirEml divToks []) = some (a / b) :=
  div_correct_toC' hv hw hb

theorem neg_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    valueOf (evalTok (.finite 1) v y dirEml negToks []) = some (-a) :=
  neg_correct_toC' hv y

theorem sq_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml sqToks [] = some [.finite (a ^ 2)] :=
  sq_correct_toC' hv y

theorem cube_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml cubeToks [] = some [.finite (a ^ 3)] :=
  cube_correct_toC' hv y

theorem pow_correct_toC {v w : EmlDir} {a b : ℂ}
    (hv : toC v = some a) (hw : toC w = some b) (ha : a ≠ 0) :
    evalTok (.finite 1) v w dirEml powToks [] = some [.finite (a ^ b)] :=
  pow_correct_toC' hv hw ha

theorem expE_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml expEToks [] = some [.finite (Complex.exp a)] :=
  expE_correct_toC' hv y

theorem mulTwo_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml mulTwoToks [] = some [.finite (a * 2)] :=
  mulTwo_correct_toC' hv y

theorem subOne_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml subOneToks [] = some [.finite (a - 1)] :=
  subOne_correct_toC' hv y

theorem addOne_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml addOneToks [] = some [.finite (a + 1)] :=
  addOne_correct_toC' hv y

theorem subTwo_correct_toC {v : EmlDir} {a : ℂ} (hv : toC v = some a) (y : EmlDir) :
    evalTok (.finite 1) v y dirEml subTwoToks [] = some [.finite (a - 2)] :=
  subTwo_correct_toC' hv y
end Eml
