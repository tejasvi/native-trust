import NativeTrust
import BO_D87_Parse
import BO_D87_L0
import BO_D87_L1
import BO_D87_L2
import BO_D87_L3
import BO_D87_L4
import BO_D87_L5
import BO_D87_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D87 BerryEsseen.Upper0423.Covers.Data.DW87.accepted
attribute [kernel_fact] BerryOpt.D87.final
#print axioms BerryOpt.D87.final
