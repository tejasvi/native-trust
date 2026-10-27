import NativeTrust
import FanoLabellingOrbits
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth FanoLabellingOrbits 2 (config := { stage := true, trace := true })

#print axioms _ktr.sounio__F2_FanoLabellingOrbits_2.Sounio.FanoLabellingOrbits.fano_labelling_orbits_count._kernel.native_decide.ax_1_1
