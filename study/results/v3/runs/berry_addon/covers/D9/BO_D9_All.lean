import NativeTrust
import BO_D9_Parse
import BO_D9_L0
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D9 BerryEsseen.Upper0423.Covers.Data.DW9.accepted
attribute [kernel_fact] BerryOpt.D9.final
#print axioms BerryOpt.D9.final
