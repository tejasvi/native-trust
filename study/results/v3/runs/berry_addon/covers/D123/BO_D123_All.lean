import NativeTrust
import BO_D123_Parse
import BO_D123_L0
import BO_D123_L1
import BO_D123_L2
import BO_D123_L3
import BO_D123_L4
import BO_D123_L5
import BO_D123_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D123 BerryEsseen.Upper0423.Covers.Data.DW123.accepted
attribute [kernel_fact] BerryOpt.D123.final
#print axioms BerryOpt.D123.final
