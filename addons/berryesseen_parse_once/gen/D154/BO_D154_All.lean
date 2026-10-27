import NativeTrust
import BO_D154_Parse
import BO_D154_L0
import BO_D154_L1
import BO_D154_L2
import BO_D154_L3
import BO_D154_L4
import BO_D154_L5
import BO_D154_L6
import BO_D154_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D154 BerryEsseen.Upper0423.Covers.Data.DW154.accepted
attribute [kernel_fact] BerryOpt.D154.final
#print axioms BerryOpt.D154.final
