import NativeTrust
import BO_D215_Parse
import BO_D215_L0
import BO_D215_L1
import BO_D215_L2
import BO_D215_L3
import BO_D215_L4
import BO_D215_L5
import BO_D215_L6
import BO_D215_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D215 BerryEsseen.Upper0423.Covers.Data.DW215.accepted
attribute [kernel_fact] BerryOpt.D215.final
#print axioms BerryOpt.D215.final
