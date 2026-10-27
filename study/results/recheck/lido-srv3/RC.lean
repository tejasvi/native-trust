import NativeTrust
import LidoSRv3.Tests.AccountPackedWordsMutants
import LidoSRv3.Tests.AllocCapacityPhase3Mutants
import LidoSRv3.Tests.AllocationTxMutants
import LidoSRv3.Tests.EthWorldMutants
import LidoSRv3.Tests.MinFirstAmountTxMutants
import LidoSRv3.Tests.SanityEnvelopeMutants
import LidoSRv3.Tests.TopupKeccakOracleMutants
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth LidoSRv3.Tests.MinFirstAmountTxMutants 2 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.MinFirstAmountTxMutants 4 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 11 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 12 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.MinFirstAmountTxMutants 1 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 27 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.AccountPackedWordsMutants 0 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 13 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.AllocCapacityPhase3Mutants 0 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 6 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.TopupKeccakOracleMutants 5 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 19 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 14 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 0 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 2 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 3 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 8 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 8 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 4 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 2 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.TopupKeccakOracleMutants 7 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 21 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 0 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.AccountPackedWordsMutants 1 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.AllocationTxMutants 1 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.MinFirstAmountTxMutants 5 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 10 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.EthWorldMutants 12 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.TopupKeccakOracleMutants 0 (config := { split := 8 })
prove_native_axiom_nth LidoSRv3.Tests.SanityEnvelopeMutants 13 (config := { split := 8 })
