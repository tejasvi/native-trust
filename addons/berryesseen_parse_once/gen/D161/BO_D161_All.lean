import NativeTrust
import BO_D161_Parse
import BO_D161_L0
import BO_D161_L1
import BO_D161_L2
import BO_D161_L3
import BO_D161_L4
import BO_D161_L5
import BO_D161_L6
import BO_D161_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D161 BerryEsseen.Upper0423.Covers.Data.DW161.accepted
attribute [kernel_fact] BerryOpt.D161.final
#print axioms BerryOpt.D161.final
