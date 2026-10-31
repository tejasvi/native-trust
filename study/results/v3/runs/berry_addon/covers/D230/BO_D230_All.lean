import NativeTrust
import BO_D230_Parse
import BO_D230_L0
import BO_D230_L1
import BO_D230_L2
import BO_D230_L3
import BO_D230_L4
import BO_D230_L5
import BO_D230_L6
import BO_D230_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D230 BerryEsseen.Upper0423.Covers.Data.DW230.accepted
attribute [kernel_fact] BerryOpt.D230.final
#print axioms BerryOpt.D230.final
