import NativeTrust
import BO_D217_Parse
import BO_D217_L0
import BO_D217_L1
import BO_D217_L2
import BO_D217_L3
import BO_D217_L4
import BO_D217_L5
import BO_D217_L6
import BO_D217_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D217 BerryEsseen.Upper0423.Covers.Data.DW217.accepted
attribute [kernel_fact] BerryOpt.D217.final
#print axioms BerryOpt.D217.final
