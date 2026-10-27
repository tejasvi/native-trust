import NativeTrust
import denote.gpt_ly4_regen.Goal31Bridge
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth denote.gpt_ly4_regen.Goal31Bridge 27 (config := { split := 8 })
