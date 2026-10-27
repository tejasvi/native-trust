import NativeTrust
import BO_D152_Parse
import BO_D152_L0
import BO_D152_L1
import BO_D152_L2
import BO_D152_L3
import BO_D152_L4
import BO_D152_L5
import BO_D152_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D152 BerryEsseen.Upper0423.Covers.Data.DW152.accepted
attribute [kernel_fact] BerryOpt.D152.final
#print axioms BerryOpt.D152.final
