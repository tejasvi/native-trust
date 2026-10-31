import NativeTrust
import BVS
import Model.CompositeHeader
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option bvs4.workdir "/home/ntbuild/v3/sweeps/bvs/facts/s_Natuvea_tacenta_core_tacenta_model/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/v3/sweeps/bvs/facts/s_Natuvea_tacenta_core_tacenta_model/G_Model_CompositeHeader_1.progress"
bvs5_fact Model.CompositeHeader 1
