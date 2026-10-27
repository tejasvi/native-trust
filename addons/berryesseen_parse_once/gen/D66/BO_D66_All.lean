import NativeTrust
import BO_D66_Parse
import BO_D66_L0
import BO_D66_L1
import BO_D66_L2
import BO_D66_L3
import BO_D66_L4
import BO_D66_L5
import BO_D66_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D66 BerryEsseen.Upper0423.Covers.Data.DW66.accepted
attribute [kernel_fact] BerryOpt.D66.final
#print axioms BerryOpt.D66.final
