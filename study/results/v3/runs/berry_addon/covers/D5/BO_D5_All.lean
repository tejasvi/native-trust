import NativeTrust
import BO_D5_Parse
import BO_D5_L0
import BO_D5_L1
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D5 BerryEsseen.Upper0423.Covers.Data.DW5.accepted
attribute [kernel_fact] BerryOpt.D5.final
#print axioms BerryOpt.D5.final
