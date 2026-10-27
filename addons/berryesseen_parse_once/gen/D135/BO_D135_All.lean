import NativeTrust
import BO_D135_Parse
import BO_D135_L0
import BO_D135_L1
import BO_D135_L2
import BO_D135_L3
import BO_D135_L4
import BO_D135_L5
import BO_D135_L6
import BO_D135_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D135 BerryEsseen.Upper0423.Covers.Data.DW135.accepted
attribute [kernel_fact] BerryOpt.D135.final
#print axioms BerryOpt.D135.final
