import NativeTrust
import BO_D162_Parse
import BO_D162_L0
import BO_D162_L1
import BO_D162_L2
import BO_D162_L3
import BO_D162_L4
import BO_D162_L5
import BO_D162_L6
import BO_D162_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D162 BerryEsseen.Upper0423.Covers.Data.DW162.accepted
attribute [kernel_fact] BerryOpt.D162.final
#print axioms BerryOpt.D162.final
