import NativeTrust
import M31DyadicWeightLaws.Arithmetic
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 5 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 6 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 8 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 0 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 3 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 2 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 7 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 1 (config := { split := 8 })
prove_native_axiom_nth M31DyadicWeightLaws.Arithmetic 4 (config := { split := 8 })
