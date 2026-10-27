import NativeTrust
import BO_D251_Parse
import BO_D251_L0
import BO_D251_L1
import BO_D251_L2
import BO_D251_L3
import BO_D251_L4
import BO_D251_L5
import BO_D251_L6
import BO_D251_L7
import BO_D251_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D251 BerryEsseen.Upper0423.Covers.Data.DW251.accepted
attribute [kernel_fact] BerryOpt.D251.final
#print axioms BerryOpt.D251.final
