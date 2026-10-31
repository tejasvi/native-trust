import NativeTrust
import BO_D7_Parse
import BO_D7_L0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D7 BerryEsseen.Upper0423.Covers.Data.DW7.accepted
attribute [kernel_fact] BerryOpt.D7.final
#print axioms BerryOpt.D7.final
