import NativeTrust
import BO_D65_Parse
import BO_D65_L0
import BO_D65_L1
import BO_D65_L2
import BO_D65_L3
import BO_D65_L4
import BO_D65_L5
import BO_D65_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D65 BerryEsseen.Upper0423.Covers.Data.DW65.accepted
attribute [kernel_fact] BerryOpt.D65.final
#print axioms BerryOpt.D65.final
