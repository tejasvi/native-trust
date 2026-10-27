import NativeTrust
import BO_D105_Parse
import BO_D105_L0
import BO_D105_L1
import BO_D105_L2
import BO_D105_L3
import BO_D105_L4
import BO_D105_L5
import BO_D105_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D105 BerryEsseen.Upper0423.Covers.Data.DW105.accepted
attribute [kernel_fact] BerryOpt.D105.final
#print axioms BerryOpt.D105.final
