import NativeTrust
import LidoSRv3.Tests.TopupKeccakOracleMutants
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_0
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_1
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_2
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_3
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_4
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_5
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_6
import F2_LidoSRv3_Tests_TopupKeccakOracleMutants_7
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 0 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 1 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 2 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 3 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 4 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 5 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 6 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.TopupKeccakOracleMutants 7 (config := { split := 8, trace := true })
