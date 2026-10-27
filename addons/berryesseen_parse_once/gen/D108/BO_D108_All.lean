import NativeTrust
import BO_D108_Parse
import BO_D108_L0
import BO_D108_L1
import BO_D108_L2
import BO_D108_L3
import BO_D108_L4
import BO_D108_L5
import BO_D108_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D108 BerryEsseen.Upper0423.Covers.Data.DW108.accepted
attribute [kernel_fact] BerryOpt.D108.final
#print axioms BerryOpt.D108.final
