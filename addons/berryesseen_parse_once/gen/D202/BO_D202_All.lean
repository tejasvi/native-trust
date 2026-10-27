import NativeTrust
import BO_D202_Parse
import BO_D202_L0
import BO_D202_L1
import BO_D202_L2
import BO_D202_L3
import BO_D202_L4
import BO_D202_L5
import BO_D202_L6
import BO_D202_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D202 BerryEsseen.Upper0423.Covers.Data.DW202.accepted
attribute [kernel_fact] BerryOpt.D202.final
#print axioms BerryOpt.D202.final
