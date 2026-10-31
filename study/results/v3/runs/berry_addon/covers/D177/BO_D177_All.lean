import NativeTrust
import BO_D177_Parse
import BO_D177_L0
import BO_D177_L1
import BO_D177_L2
import BO_D177_L3
import BO_D177_L4
import BO_D177_L5
import BO_D177_L6
import BO_D177_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D177 BerryEsseen.Upper0423.Covers.Data.DW177.accepted
attribute [kernel_fact] BerryOpt.D177.final
#print axioms BerryOpt.D177.final
