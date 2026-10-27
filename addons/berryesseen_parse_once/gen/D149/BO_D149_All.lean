import NativeTrust
import BO_D149_Parse
import BO_D149_L0
import BO_D149_L1
import BO_D149_L2
import BO_D149_L3
import BO_D149_L4
import BO_D149_L5
import BO_D149_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D149 BerryEsseen.Upper0423.Covers.Data.DW149.accepted
attribute [kernel_fact] BerryOpt.D149.final
#print axioms BerryOpt.D149.final
