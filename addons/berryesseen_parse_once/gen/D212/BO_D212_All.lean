import NativeTrust
import BO_D212_Parse
import BO_D212_L0
import BO_D212_L1
import BO_D212_L2
import BO_D212_L3
import BO_D212_L4
import BO_D212_L5
import BO_D212_L6
import BO_D212_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D212 BerryEsseen.Upper0423.Covers.Data.DW212.accepted
attribute [kernel_fact] BerryOpt.D212.final
#print axioms BerryOpt.D212.final
