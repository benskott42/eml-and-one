/-
  Axiom audit for every main theorem in `Eml`.
  Run with `lake env lean AxiomCheck.lean` (and enforced in CI):
  every theorem must depend ONLY on Lean's standard axioms
  `[propext, Classical.choice, Quot.sound]` (zero `sorryAx`, zero custom axioms).
-/
import Eml

-- Core complex EML & unwinding (`Eml.Basic`)
#print axioms Eml.lowerLog_exp
#print axioms Eml.exp_lowerLog
#print axioms Eml.lowerLog_exp_eq_sub_unwind
#print axioms Eml.log_exp_eq_sub_principalUnwind
#print axioms Eml.cE_eq_exp_one
#print axioms Eml.cZero_eq_zero
#print axioms Eml.emlExp_eq
#print axioms Eml.emlLn_eq_log
#print axioms Eml.append0xc_eq
#print axioms Eml.rawSub_eq_sub_add_unwind
#print axioms Eml.rawSub_eq

-- Genuine `eml`-word arithmetic (`Eml.Arithmetic`)
#print axioms Eml.Arithmetic.emlMul_eq
#print axioms Eml.Arithmetic.emlDiv_eq
#print axioms Eml.Arithmetic.emlInv_eq
#print axioms Eml.Arithmetic.emlAdd_eq

-- Rotated subtraction (`Eml.RotSub`, `Eml.Extended`, `Eml.DirectedInf`)
#print axioms Eml.RotSub.rotSub_eq_sub
#print axioms Eml.Extended.extRotSub_eq_sub
#print axioms Eml.DirectedInf.extEmlSqrt_zero
#print axioms Eml.DirectedInf.extScaledSub_zero
#print axioms Eml.DirectedInf.extScaledSubRot_eq_sub
#print axioms Eml.DirectedInf.dirEmlSqrt_zero
#print axioms Eml.DirectedInf.dirScaledSub_eq_sub

-- Concrete `ln 0`-free RPN constant records (`Eml.Records`)
#print axioms Eml.Records.evalRpn_negOne_strict
#print axioms Eml.Records.evalRpn_two
#print axioms Eml.Records.evalRpn_ipi_strict
#print axioms Eml.Records.evalRpn_ln2
#print axioms Eml.Records.evalRpn_three
#print axioms Eml.Records.evalRpn_four
#print axioms Eml.Records.evalRpn_negThree
#print axioms Eml.Records.evalRpn_twoThirds
#print axioms Eml.Records.evalRpn_negThird

-- Extended-domain (`ln 0 = -∞`) RPN constant records (`Eml.Extended`)
#print axioms Eml.Extended.evalRpn_0x7d0
#print axioms Eml.Extended.evalRpn_0x7d0c
#print axioms Eml.Extended.evalRpn_0x1fa1a8
#print axioms Eml.Extended.evalRpn_0x1fa1a8c
#print axioms Eml.Extended.evalRpn_half
#print axioms Eml.Extended.evalRpn_negHalf
#print axioms Eml.Extended.evalRpn_third
#print axioms Eml.Extended.evalRpn_i
#print axioms Eml.Extended.extCPi_eq_pi

-- Binary encoding, full bijection, and RPN soundness (`Eml.Binary`, `Eml.TreeBijection`, `Eml.RpnSoundness`)
#print axioms Eml.Binary.valid_program_odd_length
#print axioms Eml.TreeBijection.toRpn_injective
#print axioms Eml.TreeBijection.toRpn_fromRpn
#print axioms Eml.TreeBijection.fromRpn_toRpn
#print axioms Eml.TreeBijection.evalRpn_eq_eval_fromRpn
#print axioms Eml.RpnSoundness.valid_program_evals_singleton

-- Genuine `eml`-word transcendental, circular, hyperbolic & logistic functions (`Eml.Transcendental`)
#print axioms Eml.Transcendental.emlPow_eq
#print axioms Eml.Transcendental.emlSqrt_eq
#print axioms Eml.Transcendental.emlLogBase_eq
#print axioms Eml.Transcendental.extEmlNeg_eq
#print axioms Eml.Transcendental.extEmlAddRot_eq
#print axioms Eml.Transcendental.extEmlCosh_eq
#print axioms Eml.Transcendental.extEmlSinh_eq
#print axioms Eml.Transcendental.extEmlTanh_eq
#print axioms Eml.Transcendental.extEmlSigma_eq
#print axioms Eml.Transcendental.extEmlCos_eq
#print axioms Eml.Transcendental.extEmlSin_eq
#print axioms Eml.Transcendental.extEmlTan_eq
#print axioms Eml.Transcendental.extEmlPow_eq
#print axioms Eml.Transcendental.extEmlLogBase_eq
