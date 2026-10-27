import NativeTrust
import KernelFactsClean
import Clean.Circomlib.CompConstant
import Clean.Circomlib.CompConstantLemmas
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Examples.FemtoCairo.Plonky3TestData
import Clean.Utils.Primes
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 30 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 10 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 17 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 12 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 60 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 37 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 25 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 61 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 24 (config := { split := 8 })
prove_native_axiom_nth Clean.Circomlib.CompConstant 0 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 48 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 6 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 2 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 63 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 21 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 1 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 49 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 16 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 50 (config := { split := 8 })
prove_native_axiom_nth Clean.Utils.Primes 5 (config := { split := 8 })
prove_native_axiom_nth Clean.Utils.Primes 9 (config := { split := 8 })
prove_native_axiom_nth Clean.Utils.Primes 1 (config := { split := 8 })
prove_native_axiom_nth Clean.Circomlib.CompConstantLemmas 1 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 31 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 9 (config := { split := 8 })
prove_native_axiom_nth Clean.Utils.Primes 2 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3MemoryTestData 17 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 20 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 3 (config := { split := 8 })
prove_native_axiom_nth Clean.Examples.FemtoCairo.Plonky3TestData 45 (config := { split := 8 })
