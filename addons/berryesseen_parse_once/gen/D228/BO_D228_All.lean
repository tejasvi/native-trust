import NativeTrust
import BO_D228_Parse
import BO_D228_L0
import BO_D228_L1
import BO_D228_L2
import BO_D228_L3
import BO_D228_L4
import BO_D228_L5
import BO_D228_L6
import BO_D228_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D228 BerryEsseen.Upper0423.Covers.Data.DW228.accepted
attribute [kernel_fact] BerryOpt.D228.final
#print axioms BerryOpt.D228.final
