import Eml.CertDir
import Eml.AppOps

import Eml.Extended

namespace Eml
open Eml Eml.Cert Eml.DirectedInf
set_option maxRecDepth 100000

def bits_ten' : List Bool := [true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, true, false, false, true, false]

def sTen : Sym := (Sym.exp (Sym.sub (Sym.e) (Sym.sub (Sym.sub (Sym.e) (Sym.ln (Sym.sub (Sym.e) (Sym.sub (Sym.sub (Sym.e) (Sym.int 1)) (Sym.sub (Sym.e) (Sym.sub (Sym.neg (Sym.exp (Sym.sub (Sym.e) (Sym.sub (Sym.e) (Sym.ln (Sym.neg (Sym.sub (Sym.e) (Sym.int 3)))))))) (Sym.int 1))))))) (Sym.ln (Sym.int 2)))))

theorem certifyDir_ten : certifyDir bits_ten' = some (.fin sTen) := by decide +kernel

theorem dirConst_eq_dir {bits : List Bool} {s : Sym} (h : certifyDir bits = some (.fin s)) :
    dirConst bits = .finite s.denote := by
  obtain ⟨v, hv, hd⟩ := certifyDir_sound h
  unfold dirConst; rw [hv]; exact hd

theorem exp_one_ne_three : Complex.exp 1 ≠ 3 := by
  intro h
  have h1 : (Complex.exp 1).re = Real.exp 1 := by rw [← Complex.ofReal_one, ← Complex.ofReal_exp]; rfl
  have h2 := congrArg Complex.re h
  rw [h1] at h2
  norm_num at h2
  linarith [Real.exp_one_lt_d9]

theorem sTen_denote : sTen.denote = 10 := by
  simp only [sTen, Sym.denote]
  set E := Complex.exp 1
  have hne : -(E - ((3 : ℤ) : ℂ)) ≠ 0 := by
    push_cast; intro h; exact exp_one_ne_three (by linear_combination -h)
  have h1 : Complex.exp (E - (E - lowerLog (-(E - ((3 : ℤ) : ℂ))))) = 3 - E := by
    rw [sub_sub_cancel, exp_lowerLog hne]; push_cast; ring
  rw [h1]
  have h2 : E - (E - ((1 : ℤ) : ℂ) - (E - (-(3 - E) - ((1 : ℤ) : ℂ)))) = 5 := by push_cast; ring
  rw [h2]
  have h3 : E - (E - lowerLog 5 - lowerLog ((2 : ℤ) : ℂ)) = lowerLog 5 + lowerLog 2 := by push_cast; ring
  rw [h3, Complex.exp_add, exp_lowerLog (by norm_num), exp_lowerLog (by norm_num)]
  norm_num

theorem dirConst_ten : dirConst bits_ten' = .finite 10 := by
  rw [dirConst_eq_dir certifyDir_ten, sTen_denote]



def bits_pi' : List Bool := [true, true, true, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false]
def sPi : Sym := (Sym.exp (Sym.sub (Sym.ln (Sym.ipi 1)) (Sym.exp (Sym.sub (Sym.sub (Sym.e) (Sym.ln (Sym.int 2))) (Sym.sub (Sym.e) (Sym.ln (Sym.ipi 1)))))))

theorem certifyDir_pi : certifyDir bits_pi' = some (.fin sPi) := by decide +kernel

theorem sPi_denote : sPi.denote = (Real.pi : ℂ) := by
  simp only [sPi, Sym.denote]
  set E := Complex.exp 1
  set L := lowerLog (((1 : ℤ) : ℂ) * (Real.pi * Complex.I))
  have hpi : ((1 : ℤ) : ℂ) * (Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hL : Complex.exp L = Real.pi * Complex.I := by rw [exp_lowerLog hpi]; push_cast; ring
  have h1 : E - lowerLog ((2 : ℤ) : ℂ) - (E - L) = L - lowerLog 2 := by push_cast; ring
  have h2 : Complex.exp (L - lowerLog 2) = Real.pi * Complex.I / 2 := by
    rw [Complex.exp_sub, hL, exp_lowerLog (by norm_num)]
  rw [h1, h2, Complex.exp_sub, hL]
  have hI : Complex.exp (Real.pi * Complex.I / 2) = Complex.I := by
    rw [show (Real.pi : ℂ) * Complex.I / 2 = Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_pi_div_two_mul_I
  rw [hI]
  field_simp

theorem dirConst_pi : dirConst bits_pi' = .finite (Real.pi : ℂ) := by
  rw [dirConst_eq_dir certifyDir_pi, sPi_denote]


/-- The landed `Extended.bits_pi` is the compiler's `pi` word. -/
theorem bits_pi_eq : Eml.Extended.bits_pi = bits_pi' := by decide

theorem certifyDir_bits_pi : certifyDir Eml.Extended.bits_pi = some (.fin sPi) := by
  rw [bits_pi_eq]; exact certifyDir_pi

theorem dirConst_bits_pi : dirConst Eml.Extended.bits_pi = .finite (Real.pi : ℂ) := by
  rw [bits_pi_eq]; exact dirConst_pi

end Eml
