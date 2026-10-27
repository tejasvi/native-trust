import VB73_S0
import VB73_S1
import VB73_S2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/b0/VB73_Final.progress"
bvs6_assemble Veir.Passes.InstructionSelection.Proofs 73
