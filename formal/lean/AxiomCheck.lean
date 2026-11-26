/-
  Axiom-audit file: prints the axiom dependencies of every main theorem across
  the formalization. Every theorem must depend ONLY on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — never `sorryAx` or any custom axiom.
-/
import Eml

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
#print axioms Eml.Arithmetic.emlMul_eq
#print axioms Eml.Arithmetic.emlDiv_eq
#print axioms Eml.Arithmetic.emlInv_eq
#print axioms Eml.Arithmetic.emlAdd_eq
#print axioms Eml.RotSub.rotSub_eq_sub
#print axioms Eml.Extended.extRotSub_eq_sub
#print axioms Eml.Records.evalRpn_negOne_strict
#print axioms Eml.Records.evalRpn_two
#print axioms Eml.Records.evalRpn_ipi_strict
#print axioms Eml.Records.evalRpn_ln2
#print axioms Eml.Records.evalRpn_three
#print axioms Eml.Extended.evalRpn_0x7d0
#print axioms Eml.Extended.evalRpn_0x7d0c
#print axioms Eml.Extended.evalRpn_0x1fa1a8
#print axioms Eml.Extended.evalRpn_0x1fa1a8c
#print axioms Eml.Binary.valid_program_odd_length
#print axioms Eml.TreeBijection.toRpn_injective
#print axioms Eml.RpnSoundness.valid_program_evals_singleton
#print axioms Eml.Transcendental.emlPow_eq
#print axioms Eml.Transcendental.emlSqrt_eq
#print axioms Eml.Transcendental.emlLogBase_eq
