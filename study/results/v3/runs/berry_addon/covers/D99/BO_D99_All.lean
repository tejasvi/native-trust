import NativeTrust
import BO_D99_Parse
import BO_D99_L0
import BO_D99_L1
import BO_D99_L2
import BO_D99_L3
import BO_D99_L4
import BO_D99_L5
import BO_D99_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D99 BerryEsseen.Upper0423.Covers.Data.DW99.accepted
attribute [kernel_fact] BerryOpt.D99.final
#print axioms BerryOpt.D99.final
