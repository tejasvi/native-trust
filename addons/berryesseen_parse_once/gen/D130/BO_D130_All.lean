import NativeTrust
import BO_D130_Parse
import BO_D130_L0
import BO_D130_L1
import BO_D130_L2
import BO_D130_L3
import BO_D130_L4
import BO_D130_L5
import BO_D130_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D130 BerryEsseen.Upper0423.Covers.Data.DW130.accepted
attribute [kernel_fact] BerryOpt.D130.final
#print axioms BerryOpt.D130.final
