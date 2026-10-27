import NativeTrust
import BO_D75_Parse
import BO_D75_L0
import BO_D75_L1
import BO_D75_L2
import BO_D75_L3
import BO_D75_L4
import BO_D75_L5
import BO_D75_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D75 BerryEsseen.Upper0423.Covers.Data.DW75.accepted
attribute [kernel_fact] BerryOpt.D75.final
#print axioms BerryOpt.D75.final
