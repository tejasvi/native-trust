import NativeTrust
import BO_D207_Parse
import BO_D207_L0
import BO_D207_L1
import BO_D207_L2
import BO_D207_L3
import BO_D207_L4
import BO_D207_L5
import BO_D207_L6
import BO_D207_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D207 BerryEsseen.Upper0423.Covers.Data.DW207.accepted
attribute [kernel_fact] BerryOpt.D207.final
#print axioms BerryOpt.D207.final
