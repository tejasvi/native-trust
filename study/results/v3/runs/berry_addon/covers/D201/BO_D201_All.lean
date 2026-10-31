import NativeTrust
import BO_D201_Parse
import BO_D201_L0
import BO_D201_L1
import BO_D201_L2
import BO_D201_L3
import BO_D201_L4
import BO_D201_L5
import BO_D201_L6
import BO_D201_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D201 BerryEsseen.Upper0423.Covers.Data.DW201.accepted
attribute [kernel_fact] BerryOpt.D201.final
#print axioms BerryOpt.D201.final
