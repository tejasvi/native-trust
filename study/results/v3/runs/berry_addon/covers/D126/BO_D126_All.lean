import NativeTrust
import BO_D126_Parse
import BO_D126_L0
import BO_D126_L1
import BO_D126_L2
import BO_D126_L3
import BO_D126_L4
import BO_D126_L5
import BO_D126_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D126 BerryEsseen.Upper0423.Covers.Data.DW126.accepted
attribute [kernel_fact] BerryOpt.D126.final
#print axioms BerryOpt.D126.final
