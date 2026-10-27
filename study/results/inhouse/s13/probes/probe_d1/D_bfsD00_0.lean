import NativeTrust
import S45Final.Main.Bfs.D00C000
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth S45Final.Main.Bfs.D00C000 0 (config := { split := 8, trace := true })
