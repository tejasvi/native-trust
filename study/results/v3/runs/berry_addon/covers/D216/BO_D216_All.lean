import NativeTrust
import BO_D216_Parse
import BO_D216_L0
import BO_D216_L1
import BO_D216_L2
import BO_D216_L3
import BO_D216_L4
import BO_D216_L5
import BO_D216_L6
import BO_D216_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D216 BerryEsseen.Upper0423.Covers.Data.DW216.accepted
attribute [kernel_fact] BerryOpt.D216.final
#print axioms BerryOpt.D216.final
