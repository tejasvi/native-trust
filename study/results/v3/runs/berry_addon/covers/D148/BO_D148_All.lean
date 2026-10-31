import NativeTrust
import BO_D148_Parse
import BO_D148_L0
import BO_D148_L1
import BO_D148_L2
import BO_D148_L3
import BO_D148_L4
import BO_D148_L5
import BO_D148_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D148 BerryEsseen.Upper0423.Covers.Data.DW148.accepted
attribute [kernel_fact] BerryOpt.D148.final
#print axioms BerryOpt.D148.final
