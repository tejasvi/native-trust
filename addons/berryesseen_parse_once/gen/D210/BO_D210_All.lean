import NativeTrust
import BO_D210_Parse
import BO_D210_L0
import BO_D210_L1
import BO_D210_L2
import BO_D210_L3
import BO_D210_L4
import BO_D210_L5
import BO_D210_L6
import BO_D210_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D210 BerryEsseen.Upper0423.Covers.Data.DW210.accepted
attribute [kernel_fact] BerryOpt.D210.final
#print axioms BerryOpt.D210.final
