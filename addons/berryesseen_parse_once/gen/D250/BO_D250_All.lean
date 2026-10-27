import NativeTrust
import BO_D250_Parse
import BO_D250_L0
import BO_D250_L1
import BO_D250_L2
import BO_D250_L3
import BO_D250_L4
import BO_D250_L5
import BO_D250_L6
import BO_D250_L7
import BO_D250_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D250 BerryEsseen.Upper0423.Covers.Data.DW250.accepted
attribute [kernel_fact] BerryOpt.D250.final
#print axioms BerryOpt.D250.final
