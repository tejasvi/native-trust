import NativeTrust
import BO_D110_Parse
import BO_D110_L0
import BO_D110_L1
import BO_D110_L2
import BO_D110_L3
import BO_D110_L4
import BO_D110_L5
import BO_D110_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D110 BerryEsseen.Upper0423.Covers.Data.DW110.accepted
attribute [kernel_fact] BerryOpt.D110.final
#print axioms BerryOpt.D110.final
