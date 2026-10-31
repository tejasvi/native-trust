import NativeTrust
import BO_D90_Parse
import BO_D90_L0
import BO_D90_L1
import BO_D90_L2
import BO_D90_L3
import BO_D90_L4
import BO_D90_L5
import BO_D90_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D90 BerryEsseen.Upper0423.Covers.Data.DW90.accepted
attribute [kernel_fact] BerryOpt.D90.final
#print axioms BerryOpt.D90.final
