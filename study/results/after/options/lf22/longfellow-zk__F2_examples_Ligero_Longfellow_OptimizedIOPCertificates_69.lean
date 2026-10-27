import NativeTrust
import examples.Ligero.Longfellow.OptimizedIOPCertificates
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 69 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })
