import NativeTrust
import BO_D139_Parse
import BO_D139_L0
import BO_D139_L1
import BO_D139_L2
import BO_D139_L3
import BO_D139_L4
import BO_D139_L5
import BO_D139_L6
import BO_D139_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D139 BerryEsseen.Upper0423.Covers.Data.DW139.accepted
attribute [kernel_fact] BerryOpt.D139.final
#print axioms BerryOpt.D139.final
