import NativeTrust
import StrRepl
import BerryEsseen.Upper0423.Covers.Data.DW21
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BerryEsseen.Upper0423.Native
def tokensNR (s : String) : List String := (s.splitOn " ").filter fun t => !t.isEmpty
theorem p0 : (BerryEsseen.Upper0423.Covers.Data.DW21.data.utf8ByteSize > 0) = true := by kdecide (config := { native := false, trace := true })
