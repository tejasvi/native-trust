import NativeTrust
import BVS
import Veir.Passes.InstructionSelection.Proofs
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option bvs4.workdir "/home/ntbuild/v3/sweeps/bvs/facts/s_opencompl_veir/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/v3/sweeps/bvs/facts/s_opencompl_veir/G_Veir_Passes_InstructionSelection_Proofs_98.progress"
bvs5_fact Veir.Passes.InstructionSelection.Proofs 98
