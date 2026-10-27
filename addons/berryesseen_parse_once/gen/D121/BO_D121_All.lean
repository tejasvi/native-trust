import NativeTrust
import BO_D121_Parse
import BO_D121_L0
import BO_D121_L1
import BO_D121_L2
import BO_D121_L3
import BO_D121_L4
import BO_D121_L5
import BO_D121_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D121 BerryEsseen.Upper0423.Covers.Data.DW121.accepted
attribute [kernel_fact] BerryOpt.D121.final
#print axioms BerryOpt.D121.final
