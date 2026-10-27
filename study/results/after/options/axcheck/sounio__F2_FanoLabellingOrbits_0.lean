import NativeTrust
import FanoLabellingOrbits
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth FanoLabellingOrbits 0 (config := { stage := true, trace := true })

#print axioms _ktr.sounio__F2_FanoLabellingOrbits_0.Sounio.FanoLabellingOrbits.lagrange_consistency._kernel.native_decide.ax_1_1
