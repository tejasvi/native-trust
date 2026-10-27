import VB83_S0
import VB83_S1
import VB83_S2
import VB83_S3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/b/VB83_Final.progress"
bvs6_assemble Veir.Passes.InstructionSelection.Proofs 83
