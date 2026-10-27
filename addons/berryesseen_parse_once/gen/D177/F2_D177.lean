import NativeTrust
import BerryEsseen.Upper0423.Covers.Data.DW177
import BO_D177_All
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth BerryEsseen.Upper0423.Covers.Data.DW177 0 (config := { split := 1, trace := true })
