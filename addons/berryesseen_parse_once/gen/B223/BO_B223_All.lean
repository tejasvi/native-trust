import NativeTrust
import BO_B223_Parse
import BO_B223_L0
import BO_B223_L1
import BO_B223_L2
import BO_B223_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.B223 BerryEsseen.Upper0423.Covers.Data.BE223.accepted
attribute [kernel_fact] BerryOpt.B223.final
#print axioms BerryOpt.B223.final
