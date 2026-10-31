import NativeTrust
import BO_D84_Parse
import BO_D84_L0
import BO_D84_L1
import BO_D84_L2
import BO_D84_L3
import BO_D84_L4
import BO_D84_L5
import BO_D84_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D84 BerryEsseen.Upper0423.Covers.Data.DW84.accepted
attribute [kernel_fact] BerryOpt.D84.final
#print axioms BerryOpt.D84.final
