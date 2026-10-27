import NativeTrust
import FormalConjectures.OEIS.«115366»
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth FormalConjectures.OEIS.«115366» 0 (config := { csimp := true, trace := true })
