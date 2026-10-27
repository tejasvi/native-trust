import NativeTrust
import BO_D232_Parse
import BO_D232_L0
import BO_D232_L1
import BO_D232_L2
import BO_D232_L3
import BO_D232_L4
import BO_D232_L5
import BO_D232_L6
import BO_D232_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D232 BerryEsseen.Upper0423.Covers.Data.DW232.accepted
attribute [kernel_fact] BerryOpt.D232.final
#print axioms BerryOpt.D232.final
