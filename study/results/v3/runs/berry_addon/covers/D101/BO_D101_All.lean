import NativeTrust
import BO_D101_Parse
import BO_D101_L0
import BO_D101_L1
import BO_D101_L2
import BO_D101_L3
import BO_D101_L4
import BO_D101_L5
import BO_D101_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D101 BerryEsseen.Upper0423.Covers.Data.DW101.accepted
attribute [kernel_fact] BerryOpt.D101.final
#print axioms BerryOpt.D101.final
