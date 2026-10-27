import NativeTrust
import BO_D182_Parse
import BO_D182_L0
import BO_D182_L1
import BO_D182_L2
import BO_D182_L3
import BO_D182_L4
import BO_D182_L5
import BO_D182_L6
import BO_D182_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D182 BerryEsseen.Upper0423.Covers.Data.DW182.accepted
attribute [kernel_fact] BerryOpt.D182.final
#print axioms BerryOpt.D182.final
