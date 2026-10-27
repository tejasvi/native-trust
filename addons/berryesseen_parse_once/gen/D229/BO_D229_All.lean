import NativeTrust
import BO_D229_Parse
import BO_D229_L0
import BO_D229_L1
import BO_D229_L2
import BO_D229_L3
import BO_D229_L4
import BO_D229_L5
import BO_D229_L6
import BO_D229_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D229 BerryEsseen.Upper0423.Covers.Data.DW229.accepted
attribute [kernel_fact] BerryOpt.D229.final
#print axioms BerryOpt.D229.final
