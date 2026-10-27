import GroupCmd
import Proofs.Serialization
/-! B08 group (2): the two `bv_decide` facts of `Model.CompositeHeader` (tacenta-model) and the fact of
`Proofs.Serialization` (tacenta-proofs) converted together; `decode_encode` and `decode_encode_composite` are rebuilt
with the rebuilt `Model.CompositeHeader` theorems. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/veir/sat"
set_option bvs4.log "/home/ntbuild/work_bvscale/groups/GNatuvea.progress"
bvs5_group "Model.CompositeHeader:0,1" "Proofs.Serialization:0"
