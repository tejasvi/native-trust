import VB23_S0
import VB23_S1
import VB23_S2
import VB23_S3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/b/VB23_Final.progress"
bvs6_assemble Veir.Passes.InstructionSelection.Proofs 23
