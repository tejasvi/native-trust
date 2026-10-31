import NativeTrust
import BO_D143_Parse
import BO_D143_L0
import BO_D143_L1
import BO_D143_L2
import BO_D143_L3
import BO_D143_L4
import BO_D143_L5
import BO_D143_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D143 BerryEsseen.Upper0423.Covers.Data.DW143.accepted
attribute [kernel_fact] BerryOpt.D143.final
#print axioms BerryOpt.D143.final
