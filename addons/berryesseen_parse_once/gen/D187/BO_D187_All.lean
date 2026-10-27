import NativeTrust
import BO_D187_Parse
import BO_D187_L0
import BO_D187_L1
import BO_D187_L2
import BO_D187_L3
import BO_D187_L4
import BO_D187_L5
import BO_D187_L6
import BO_D187_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D187 BerryEsseen.Upper0423.Covers.Data.DW187.accepted
attribute [kernel_fact] BerryOpt.D187.final
#print axioms BerryOpt.D187.final
