import NativeTrust
import BO_D205_Parse
import BO_D205_L0
import BO_D205_L1
import BO_D205_L2
import BO_D205_L3
import BO_D205_L4
import BO_D205_L5
import BO_D205_L6
import BO_D205_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D205 BerryEsseen.Upper0423.Covers.Data.DW205.accepted
attribute [kernel_fact] BerryOpt.D205.final
#print axioms BerryOpt.D205.final
