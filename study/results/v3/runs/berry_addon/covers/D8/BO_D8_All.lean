import NativeTrust
import BO_D8_Parse
import BO_D8_L0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D8 BerryEsseen.Upper0423.Covers.Data.DW8.accepted
attribute [kernel_fact] BerryOpt.D8.final
#print axioms BerryOpt.D8.final
