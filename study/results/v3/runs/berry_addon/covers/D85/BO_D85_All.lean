import NativeTrust
import BO_D85_Parse
import BO_D85_L0
import BO_D85_L1
import BO_D85_L2
import BO_D85_L3
import BO_D85_L4
import BO_D85_L5
import BO_D85_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D85 BerryEsseen.Upper0423.Covers.Data.DW85.accepted
attribute [kernel_fact] BerryOpt.D85.final
#print axioms BerryOpt.D85.final
