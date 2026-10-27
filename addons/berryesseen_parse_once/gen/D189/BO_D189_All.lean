import NativeTrust
import BO_D189_Parse
import BO_D189_L0
import BO_D189_L1
import BO_D189_L2
import BO_D189_L3
import BO_D189_L4
import BO_D189_L5
import BO_D189_L6
import BO_D189_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D189 BerryEsseen.Upper0423.Covers.Data.DW189.accepted
attribute [kernel_fact] BerryOpt.D189.final
#print axioms BerryOpt.D189.final
