import NativeTrust
import BO_D140_Parse
import BO_D140_L0
import BO_D140_L1
import BO_D140_L2
import BO_D140_L3
import BO_D140_L4
import BO_D140_L5
import BO_D140_L6
import BO_D140_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D140 BerryEsseen.Upper0423.Covers.Data.DW140.accepted
attribute [kernel_fact] BerryOpt.D140.final
#print axioms BerryOpt.D140.final
