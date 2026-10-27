import VB15_S0
import VB15_S1
import VB15_S2
import VB15_S3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/b/VB15_Final.progress"
bvs6_assemble Veir.Passes.InstructionSelection.Proofs 15
