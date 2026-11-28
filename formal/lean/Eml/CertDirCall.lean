import Eml.CertDir
import Eml.CertExt
open Eml.Cert

namespace Eml

set_option maxRecDepth 100000

def w_half : List Bool := [true, true, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, true, false, false, false, true, false]
def w_i : List Bool := [true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false]
def w_negi : List Bool := [true, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false, true, false, false]
def w_twoi : List Bool := [true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false]
def w_pi : List Bool := [true, true, true, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false]
def w_ten : List Bool := [true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, true, false, false, true, false]
def w_tenI : List Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, true, false, false, true, false, false, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false]

set_option maxHeartbeats 0
open Sym in
theorem half_dir : certifyDir w_half = some (.fin (.exp (.sub .e (.ln (.add (.exp .e) (.exp .e)))))) := by decide +kernel
theorem ten_dir : (certifyDir w_ten).isSome = true := by decide +kernel
theorem pi_dir : (certifyDir w_pi).isSome = true := by decide +kernel
theorem i_dir : (certifyDir w_i).isSome = true := by decide +kernel
theorem negi_dir : (certifyDir w_negi).isSome = true := by decide +kernel
theorem twoi_dir : (certifyDir w_twoi).isSome = true := by decide +kernel
theorem tenI_dir : (certifyDir w_tenI).isSome = true := by decide +kernel

end Eml
