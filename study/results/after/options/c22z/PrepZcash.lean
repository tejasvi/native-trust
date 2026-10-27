import NativeTrust
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
stage_native_axiom_nth Zcash.Snark.Fixtures.SingleAction.Honest.Fixture 6 (config := { csimp := true, trace := true })
stage_native_axiom_nth Zcash.Snark.Fixtures.MultiAction.Honest.Fixture 2 (config := { csimp := true, trace := true })
stage_native_axiom_nth Zcash.Snark.Fixtures.SingleAction.Random.Fixture 3 (config := { csimp := true, trace := true })
stage_native_axiom_nth Zcash.Snark.Fixtures.MultiAction.Random.Fixture 1 (config := { csimp := true, trace := true })
