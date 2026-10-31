import NativeTrust
import BerryEsseen.Upper0423.Covers.Data.DW170
import BO_D170_All
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth BerryEsseen.Upper0423.Covers.Data.DW170 0 (config := { split := 1, trace := true })
