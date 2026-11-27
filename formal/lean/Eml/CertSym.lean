/-
  The symbolic language of the certificate checker (`Eml.Cert`): closed values
  built from integers, `e`, integer multiples of `iπ`, `exp`, the lower-cut `ln`,
  negation, addition and subtraction.
-/
import Eml.Basic

namespace Eml.Cert

open Eml

/-- Symbolic closed values produced by the certificate checker. -/
inductive Sym where
  | int (n : Int)
  | e
  /-- `k · iπ` -/
  | ipi (k : Int)
  | exp (a : Sym)
  /-- Lower-cut logarithm (`lowerLog`, `Im ∈ [−π, π)`). -/
  | ln (a : Sym)
  | neg (a : Sym)
  | add (a b : Sym)
  | sub (a b : Sym)
  deriving DecidableEq, Repr

/-- Complex value of a symbolic expression. -/
noncomputable def Sym.denote : Sym → ℂ
  | .int n => (n : ℂ)
  | .e => Complex.exp 1
  | .ipi k => (k : ℂ) * (Real.pi * Complex.I)
  | .exp a => Complex.exp a.denote
  | .ln a => lowerLog a.denote
  | .neg a => -a.denote
  | .add a b => a.denote + b.denote
  | .sub a b => a.denote - b.denote

end Eml.Cert
