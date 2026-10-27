import NativeTrust
import StrRepl
import CedarRepl
import UnitTest.Decimal
import UnitTest.IPAddr
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
#kernel_blockers_nth UnitTest.Decimal 1
#kernel_blockers_nth UnitTest.Decimal 6
#kernel_blockers_nth UnitTest.Decimal 4
#kernel_blockers_nth UnitTest.Decimal 0
#kernel_blockers_nth UnitTest.Decimal 5
#kernel_blockers_nth UnitTest.Decimal 7
#kernel_blockers_nth UnitTest.Decimal 2
#kernel_blockers_nth UnitTest.Decimal 3
#kernel_blockers_nth UnitTest.IPAddr 7
#kernel_blockers_nth UnitTest.IPAddr 4
#kernel_blockers_nth UnitTest.IPAddr 5
#kernel_blockers_nth UnitTest.IPAddr 2
#kernel_blockers_nth UnitTest.IPAddr 6
#kernel_blockers_nth UnitTest.IPAddr 3
#kernel_blockers_nth UnitTest.IPAddr 0
#kernel_blockers_nth UnitTest.IPAddr 1
prove_native_axiom_nth UnitTest.Decimal 1 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 6 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 4 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 0 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 5 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 7 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 2 (config := { split := 8 })
prove_native_axiom_nth UnitTest.Decimal 3 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 7 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 4 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 5 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 2 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 6 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 3 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 0 (config := { split := 8 })
prove_native_axiom_nth UnitTest.IPAddr 1 (config := { split := 8 })
