import NativeTrust
import BO_D193_Parse
import BO_D193_L0
import BO_D193_L1
import BO_D193_L2
import BO_D193_L3
import BO_D193_L4
import BO_D193_L5
import BO_D193_L6
import BO_D193_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D193 BerryEsseen.Upper0423.Covers.Data.DW193.accepted
attribute [kernel_fact] BerryOpt.D193.final
#print axioms BerryOpt.D193.final
