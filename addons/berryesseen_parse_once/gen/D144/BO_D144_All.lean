import NativeTrust
import BO_D144_Parse
import BO_D144_L0
import BO_D144_L1
import BO_D144_L2
import BO_D144_L3
import BO_D144_L4
import BO_D144_L5
import BO_D144_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D144 BerryEsseen.Upper0423.Covers.Data.DW144.accepted
attribute [kernel_fact] BerryOpt.D144.final
#print axioms BerryOpt.D144.final
