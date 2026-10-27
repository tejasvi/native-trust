import NativeTrust
import Zcash.Snark.Fixtures.PostNu63
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth Zcash.Snark.Fixtures.PostNu63 10 (config := { stage := true, trace := true })

#print axioms _ktr.s_zcash_ironwood__F2_Zcash_Snark_Fixtures_PostNu63_10.Zcash.Snark.PostNu63Fixture.captures_use_same_ursG._kernel.native_decide.ax_1_1
