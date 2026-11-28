/-
  The calculator's own `x − y` circuit, proved correct.

  For general operands the compiler lowers `x − y` (`lib/eml/lowering.ts`:
  `buildSub` → `scaledRot`) to a 565-token circuit,

    k · rotSub(x/k, y/k),   k = √(y²) − (−1),   rotSub(a, b) = (c·(a − b) − c·(b − b)) / c,

  with the rotation constant `c = iπ` (the K 21 word `111111E1EEEE11E1E1EEE`), each
  inner `−` the raw subtraction word, and the `subOfExp` shortcut `eml(H, exp v)`
  wherever the left operand is a word `exp H`. Its `mul`, `div`, `sqrt`, `sqr`, `sub`
  and `−1` words are token for token `dirEmlMul`, `dirEmlDiv`, `dirEmlSqrt`,
  `dirEmlSqr`, `dirRawSub` and `dirCNegOne`.

  * `appSubToks_eval`: the token list evaluates (by unfolding alone) to `appSub x y`.
  * `shortSub_eq`: the shortcut is the raw subtraction whenever `exp H` is finite. It is
    not true for every `EmlDir` value (an infinity at an arbitrary angle does not come
    back from `exp ∘ ln`), but all four uses in this circuit have `exp H` finite.
  * `dirCIpi_eq`: the K 21 word is `iπ` in `EmlDir`.
  * `appSub_correct`: for all `a b : ℂ`, `b = 0` included, the circuit evaluates to
    `a − b` in `EmlDir` (directed infinities and signed zero).
  * `Tok.subst` and `evalTok_subst`: replacing the `x` and `y` slots of a word by
    sub-words evaluates as that word on the sub-words' results. The trigonometric
    words are built this way, rather than by unfolding a token list with `rfl`.

  `appSubToks` is checked against what the compiler emits for `x − y` by check 115
  and by `scripts/lean-bridge-check.ts` (`APP_SUB_WORD` in `lib/eml/export.ts`).

  Zero `sorry`, zero custom axioms.
-/
import Eml.DirectedInf

namespace Eml.AppSub

open Eml Eml.DirectedInf

/-! ### Tokens with two variables -/

/-- RPN tokens: `1`, the variables `x` and `y`, and the `eml` gate. -/
inductive Tok where
  | one
  | x
  | y
  | gate
  deriving DecidableEq, Repr

/-- Stack evaluation of a token list (the `evalRpn` of `Eml.Binary`, with variables). -/
def evalTok {α : Type} (one x y : α) (op : α → α → α) : List Tok → List α → Option (List α)
  | [], st => some st
  | .one :: rest, st => evalTok one x y op rest (one :: st)
  | .x :: rest, st => evalTok one x y op rest (x :: st)
  | .y :: rest, st => evalTok one x y op rest (y :: st)
  | .gate :: rest, b :: a :: st => evalTok one x y op rest (op a b :: st)
  | .gate :: _, _ => none

/-- Replace the variables of a template by token lists. `1` and the gate stay put. -/
def Tok.subst (X Y : List Tok) : List Tok → List Tok
  | [] => []
  | .x :: rest => X ++ Tok.subst X Y rest
  | .y :: rest => Y ++ Tok.subst X Y rest
  | t :: rest => t :: Tok.subst X Y rest

theorem evalTok_append {α : Type} (one x y : α) (op : α → α → α) (A B : List Tok) (st : List α) :
    evalTok one x y op (A ++ B) st = (evalTok one x y op A st).bind (evalTok one x y op B) := by
  induction A generalizing st with
  | nil => rfl
  | cons t rest ih =>
    cases t with
    | one => exact ih (one :: st)
    | x => exact ih (x :: st)
    | y => exact ih (y :: st)
    | gate =>
      cases st with
      | nil => rfl
      | cons b st1 =>
        cases st1 with
        | nil => rfl
        | cons a st2 => exact ih (op a b :: st2)

/-- A token list that returns `pre` on `base` returns `pre` in front of any extra stack,
    and never reads that extra stack. -/
theorem evalTok_detach {α : Type} (one x y : α) (op : α → α → α) :
    ∀ (A : List Tok) (base extra : List α) {pre : List α},
      evalTok one x y op A base = some pre →
      evalTok one x y op A (base ++ extra) = some (pre ++ extra)
  | [], _, extra, _, h => by
      simp [evalTok] at h
      subst h
      rfl
  | .one :: rest, base, extra, _, h => by
      simp [evalTok] at h
      simpa [evalTok, List.cons_append] using evalTok_detach one x y op rest (one :: base) extra h
  | .x :: rest, base, extra, _, h => by
      simp [evalTok] at h
      simpa [evalTok, List.cons_append] using evalTok_detach one x y op rest (x :: base) extra h
  | .y :: rest, base, extra, _, h => by
      simp [evalTok] at h
      simpa [evalTok, List.cons_append] using evalTok_detach one x y op rest (y :: base) extra h
  | .gate :: rest, base, extra, _, h => by
      cases base with
      | nil => simp [evalTok] at h
      | cons b base1 =>
        cases base1 with
        | nil => simp [evalTok] at h
        | cons a base2 =>
          simp [evalTok] at h
          simpa [evalTok, List.cons_append] using
            evalTok_detach one x y op rest (op a b :: base2) extra h

theorem evalTok_stack {α : Type} (one x y : α) (op : α → α → α) (A : List Tok) (st : List α) {v : α}
    (h : evalTok one x y op A [] = some [v]) :
    evalTok one x y op A st = some (v :: st) := by
  simpa using evalTok_detach one x y op A [] st h

theorem evalTok_subst {α : Type} (one x y : α) (op : α → α → α) (X Y T : List Tok) {vx vy : α}
    (hX : evalTok one x y op X [] = some [vx]) (hY : evalTok one x y op Y [] = some [vy])
    (st : List α) :
    evalTok one x y op (Tok.subst X Y T) st = evalTok one vx vy op T st := by
  induction T generalizing st with
  | nil => rfl
  | cons t rest ih =>
    cases t with
    | one =>
      simp only [Tok.subst, evalTok]
      exact ih (one :: st)
    | x =>
      rw [Tok.subst, evalTok_append, evalTok_stack _ _ _ _ _ _ hX]
      simpa [evalTok] using ih (vx :: st)
    | y =>
      rw [Tok.subst, evalTok_append, evalTok_stack _ _ _ _ _ _ hY]
      simpa [evalTok] using ih (vy :: st)
    | gate =>
      cases st with
      | nil => rfl
      | cons b st1 =>
        cases st1 with
        | nil => rfl
        | cons a st2 =>
          simp only [Tok.subst, evalTok]
          exact ih (op a b :: st2)

/-- What the calculator compiles `x − y` to: 565 tokens, `1`, `x`, `y` and `E` (gate),
    `APP_SUB_WORD` in `lib/eml/export.ts`. The bridge checks this list against the compiler.
    1111111111111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEE
    E1EE111111111E1EEEE11E1E1EEEEE1EE11111111111E1EEEE11E1E1EEEEE1EE111111111111EEE1
    EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1xE1EE1111111
    11111EEE1EE11EE1EEEE1EE1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1
    EE1E1EEE1EE1111111111E1EEEE11E1E1EEEEE1EE111111111111EEE1EE11EE1EEEE1EE1111111yE
    E1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1EE111111111111EEE1EE11EE1EEEE1EE
    1111111yEE1EEyE1EE1EE1EEE1EE1E11111E1EEEE11EE1EEEE1EE1yE1EE1E1EEE1EE1E1EEE1EE1EE
    1EE1E -/
def appSubToks : List Tok :=
  [.one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one,
    .gate, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .y, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .one, .one, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .one, .gate, .one, .gate, .one, .gate, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one, .one,
    .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one, .gate,
    .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one,
    .one, .y, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate,
    .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .x, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .one, .one, .one, .one, .one, .one, .y, .gate, .gate, .one, .gate, .gate,
    .y, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .one, .gate, .gate, .one, .gate, .one, .one, .one, .one, .one, .gate, .one,
    .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .y, .gate, .one, .gate, .gate, .one, .gate,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate, .one,
    .one, .gate, .one, .gate, .one, .gate, .gate, .gate, .gate, .gate, .one, .gate,
    .gate, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one, .one,
    .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .gate, .gate, .one,
    .gate, .gate, .gate, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one,
    .one, .one, .y, .gate, .gate, .one, .gate, .gate, .y, .gate, .one, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one,
    .gate, .one, .one, .one, .one, .one, .gate, .one, .gate, .gate, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .y, .gate, .one, .gate, .gate, .one, .one, .one, .one, .one, .one,
    .one, .one, .one, .one, .one, .one, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .gate, .gate, .one, .gate, .gate, .gate, .gate, .one, .gate, .gate,
    .one, .one, .one, .one, .one, .one, .one, .y, .gate, .gate, .one, .gate,
    .gate, .y, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .one, .gate, .gate, .one, .gate, .one, .one, .one, .one, .one, .gate,
    .one, .gate, .gate, .gate, .gate, .one, .one, .gate, .gate, .one, .gate, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .y, .gate, .one, .gate, .gate, .one,
    .gate, .one, .gate, .gate, .gate, .one, .gate, .gate, .one, .gate, .one, .gate,
    .gate, .gate, .one, .gate, .gate, .one, .gate, .gate, .one, .gate, .gate, .one,
    .gate]


/-! ### The circuit, piece by piece -/

/-- `dirEmlDiv a b = exp (divBody a b)`. -/
noncomputable def divBody (a b : EmlDir) : EmlDir :=
  dirEml (dirEmlLn (dirEml (.finite 1) b)) (dirEmlExp (dirEml (.finite 1) a))

/-- `dirEmlMul a b = exp (mulBody a b)`. -/
noncomputable def mulBody (a b : EmlDir) : EmlDir :=
  dirEml (.finite 1) (dirEmlExp (dirEml (dirEmlLn (dirEml (.finite 1) a)) b))

/-- `dirEmlSqrt w = exp (sqrtBody w)`. -/
noncomputable def sqrtBody (w : EmlDir) : EmlDir :=
  dirEmlDiv (dirEmlLn w) dirCTwo

/-- The compiler's `subOfExp`: for a left operand `exp H`, `eml(H, exp v)`. -/
noncomputable def shortSub (H v : EmlDir) : EmlDir :=
  dirEml H (dirEmlExp v)

/-- The K 21 word `111111E1EEEE11E1E1EEE` (through `ln 0`). -/
noncomputable def dirCIpi : EmlDir :=
  dirEml (.finite 1)
    (dirEml (dirEml (.finite 1) (dirEml (.finite 1)
      (dirEml (.finite 1) (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)))))
      (dirEml (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1)))

/-- The compiled scaled rotation `x − yb`, in the order `lowering.ts` builds it, with the
    scale `k = √(yk²) − (−1)` taken from `yk` (`scaledRot`'s `kFrom`). The compiler's
    `x − y` is `appSubGen x y y`, and its `x + y` is `appSubGen x y ((−1)·y)`. -/
noncomputable def appSubGen (x yk yb : EmlDir) : EmlDir :=
  let k := shortSub (sqrtBody (dirEmlSqr yk)) dirCNegOne
  let b1 := dirEmlDiv yb k
  dirEmlMul k
    (dirEmlDiv
      (shortSub (mulBody dirCIpi (shortSub (divBody x k) b1))
        (dirEmlMul dirCIpi (shortSub (divBody yb k) b1)))
      dirCIpi)

/-- The compiled `x − y`. -/
noncomputable def appSub (x y : EmlDir) : EmlDir := appSubGen x y y

set_option maxRecDepth 100000 in
/-- The token list is that circuit, by unfolding alone. -/
theorem appSubToks_eval (x y : EmlDir) :
    evalTok (.finite 1) x y dirEml appSubToks [] = some [appSub x y] := by
  rfl

/-! ### The shortcut -/

theorem dirExp_dirEmlLn_finite (w : ℂ) : dirExp (dirEmlLn (.finite w)) = .finite w := by
  by_cases hw : w = 0
  · subst hw
    rw [dirEmlLn_zero]
    simp [dirExp]
  · rw [dirEmlLn_finite_ne_zero hw]
    simp [dirExp, Complex.exp_log hw]

/-- `eml(H, exp v) = eml(ln(exp H), exp v)` whenever `exp H` is finite. -/
theorem shortSub_eq {H : EmlDir} {w : ℂ} (hH : dirExp H = .finite w) (v : EmlDir) :
    shortSub H v = dirRawSub (dirEmlExp H) v := by
  unfold shortSub dirRawSub
  rw [dirEmlExp_eq H, hH]
  unfold dirEml
  rw [dirExp_dirEmlLn_finite, hH]

/-! ### `iπ` in `EmlDir` -/

theorem dirCIpi_eq : dirCIpi = .finite (Real.pi * Complex.I) := by
  have he1_im : (Complex.exp (1 : ℂ)).im = 0 := by rw [Complex.exp_im]; simp
  have h0 : dirEml (.finite 1) (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) =
      .finite 0 := by
    rw [dirEml_finite one_ne_zero, dirEml_finite one_ne_zero,
      dirEml_finite (by rw [eml, lowerLog_one, sub_zero]; exact Complex.exp_ne_zero _)]
    congr 1; exact cZero_eq_zero
  have hnegInf : dirEml (.finite 1) (dirEml (.finite 1) (.finite 0)) = .negInf 0 := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, he1_im]
  have htree : dirEml (dirEml (dirEml (.finite 1) (.finite 1)) (.finite 1)) (.finite 1) =
      .finite (Complex.exp (Complex.exp (Complex.exp 1))) := by
    simp [dirEml, dirExp, dirLowerLog, dirSub, lowerLog_one]
  unfold dirCIpi
  rw [h0, hnegInf, htree]
  have hee_im : (Complex.exp (Complex.exp (1 : ℂ))).im = 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hinner : dirEml (.negInf 0) (.finite (Complex.exp (Complex.exp (Complex.exp 1)))) =
      .finite (-Complex.exp (Complex.exp 1)) := by
    have h10 : ¬ ((1 : ℝ) < 0) := by norm_num
    simp [dirEml, dirExp, dirLowerLog, dirSub, Complex.exp_ne_zero, lowerLog_exp_of_im_zero hee_im, h10]
  rw [hinner]
  have hneg_ee : -Real.exp (Real.exp 1) < 0 := by linarith [Real.exp_pos (Real.exp 1)]
  have hcast_ee : -Complex.exp (Complex.exp (1 : ℂ)) = ((-Real.exp (Real.exp 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp]; push_cast; rfl
  have hne : -Complex.exp (Complex.exp (1 : ℂ)) ≠ 0 := by
    rw [hcast_ee]; exact Complex.ofReal_ne_zero.mpr (ne_of_lt hneg_ee)
  rw [dirEml_finite hne]
  congr 1
  unfold eml
  rw [hcast_ee, lowerLog_ofReal_neg hneg_ee, neg_neg, Real.log_exp]
  rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
  ring

/-! ### The compiled `x − y` is `x − y` -/

/-- The scale `√(yk²) − (−1)` is `s + 1` with `0 ≤ Re s` (`s = 0` at `yk = 0`, through `−0` and
    directed infinities). -/
theorem appScale_finite (bk : ℂ) : ∃ s : ℂ, 0 ≤ s.re ∧
    shortSub (sqrtBody (dirEmlSqr (.finite bk))) dirCNegOne = .finite (s + 1) := by
  obtain ⟨s, hs, hs_re⟩ : ∃ s : ℂ, dirEmlSqrt (dirEmlSqr (.finite bk)) = .finite s ∧ 0 ≤ s.re := by
    by_cases hb : bk = 0
    · subst hb
      exact ⟨0, by unfold dirEmlSqr; rw [dirEmlMul_zero_zero, dirEmlSqrt_zero], le_refl _⟩
    · refine ⟨(bk * bk) ^ ((1 : ℂ) / 2), ?_, re_cpow_half_nonneg (bk * bk)⟩
      unfold dirEmlSqr
      rw [dirEmlMul_eq_of_ne_zero hb hb, dirEmlSqrt_finite (mul_ne_zero hb hb)]
  refine ⟨s, hs_re, ?_⟩
  have hH : dirExp (sqrtBody (dirEmlSqr (.finite bk))) = .finite s := by
    rw [← dirEmlExp_eq]; exact hs
  rw [shortSub_eq hH, dirEmlExp_eq, hH, dirCNegOne_eq_negOne, dirRawSub_eq,
    lowerUnwind_of_im_zero (by simp)]
  congr 1
  push_cast
  ring

/-- With a finite scale source `bk` and finite operands, the compiled rotation is `a − b`. -/
theorem appSubGen_finite (a bk b : ℂ) :
    appSubGen (.finite a) (.finite bk) (.finite b) = .finite (a - b) := by
  set c : ℂ := Real.pi * Complex.I with hc
  have hc_re : c.re = 0 := by simp [c]
  have hc_ne : c ≠ 0 := by simp [c, Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨s, hs_re, hk⟩ := appScale_finite bk
  have hk_re : 0 ≤ (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hk_ne : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  unfold appSubGen
  dsimp only
  rw [hk, dirCIpi_eq]
  -- The two inner shortcuts: x/k and y/k are finite.
  have hx : dirExp (divBody (.finite a) (.finite (s + 1))) = .finite (a / (s + 1)) := by
    rw [← dirEmlExp_eq]; exact dirEmlDiv_eq a hk_ne hk_re
  have hy : dirExp (divBody (.finite b) (.finite (s + 1))) = .finite (b / (s + 1)) := by
    rw [← dirEmlExp_eq]; exact dirEmlDiv_eq b hk_ne hk_re
  rw [shortSub_eq hx, shortSub_eq hy]
  -- The outer shortcut: c · (x/k − y/k) is finite.
  have hm : dirExp (mulBody (.finite c)
      (dirRawSub (dirEmlExp (divBody (.finite a) (.finite (s + 1))))
        (dirEmlDiv (.finite b) (.finite (s + 1))))) =
      .finite (c * (a / (s + 1) - b / (s + 1) +
        2 * Real.pi * Complex.I * (lowerUnwind (b / (s + 1)) : ℂ))) := by
    rw [← dirEmlExp_eq]
    show dirEmlMul (.finite c) (dirRawSub (dirEmlDiv (.finite a) (.finite (s + 1)))
      (dirEmlDiv (.finite b) (.finite (s + 1)))) = _
    rw [dirEmlDiv_eq a hk_ne hk_re, dirEmlDiv_eq b hk_ne hk_re, dirRawSub_eq,
      dirEmlMul_eq hc_ne (le_of_eq hc_re.symm)]
  rw [shortSub_eq hm]
  -- What is left is Lean's scaled rotated subtraction with this scale.
  show dirEmlMul (.finite (s + 1)) (dirRotSub (.finite c) (dirEmlDiv (.finite a) (.finite (s + 1)))
    (dirEmlDiv (.finite b) (.finite (s + 1)))) = _
  rw [dirEmlDiv_eq a hk_ne hk_re, dirEmlDiv_eq b hk_ne hk_re, dirRotSub_eq_sub hc_re hc_ne,
    dirEmlMul_eq hk_ne hk_re]
  congr 1
  rw [mul_sub, mul_div_cancel₀ _ hk_ne, mul_div_cancel₀ _ hk_ne]

theorem appSub_finite (a b : ℂ) : appSub (.finite a) (.finite b) = .finite (a - b) :=
  appSubGen_finite a b b

/-- **The calculator's `x − y` circuit computes `a − b`** for every `a b : ℂ`, in `EmlDir`. -/
theorem appSub_correct (a b : ℂ) :
    evalTok (.finite 1) (.finite a) (.finite b) dirEml appSubToks [] = some [.finite (a - b)] := by
  rw [appSubToks_eval, appSub_finite]

end Eml.AppSub
