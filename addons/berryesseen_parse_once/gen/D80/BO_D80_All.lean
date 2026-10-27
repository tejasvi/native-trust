import NativeTrust
import BO_D80_Parse
import BO_D80_L0
import BO_D80_L1
import BO_D80_L2
import BO_D80_L3
import BO_D80_L4
import BO_D80_L5
import BO_D80_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D80 BerryEsseen.Upper0423.Covers.Data.DW80.accepted
attribute [kernel_fact] BerryOpt.D80.final
#print axioms BerryOpt.D80.final
