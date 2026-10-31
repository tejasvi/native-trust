import NativeTrust
import BO_D107_Parse
import BO_D107_L0
import BO_D107_L1
import BO_D107_L2
import BO_D107_L3
import BO_D107_L4
import BO_D107_L5
import BO_D107_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D107 BerryEsseen.Upper0423.Covers.Data.DW107.accepted
attribute [kernel_fact] BerryOpt.D107.final
#print axioms BerryOpt.D107.final
