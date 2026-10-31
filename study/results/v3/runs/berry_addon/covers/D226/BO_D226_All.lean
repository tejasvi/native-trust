import NativeTrust
import BO_D226_Parse
import BO_D226_L0
import BO_D226_L1
import BO_D226_L2
import BO_D226_L3
import BO_D226_L4
import BO_D226_L5
import BO_D226_L6
import BO_D226_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D226 BerryEsseen.Upper0423.Covers.Data.DW226.accepted
attribute [kernel_fact] BerryOpt.D226.final
#print axioms BerryOpt.D226.final
