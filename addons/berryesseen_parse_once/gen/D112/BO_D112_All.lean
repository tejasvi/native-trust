import NativeTrust
import BO_D112_Parse
import BO_D112_L0
import BO_D112_L1
import BO_D112_L2
import BO_D112_L3
import BO_D112_L4
import BO_D112_L5
import BO_D112_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D112 BerryEsseen.Upper0423.Covers.Data.DW112.accepted
attribute [kernel_fact] BerryOpt.D112.final
#print axioms BerryOpt.D112.final
