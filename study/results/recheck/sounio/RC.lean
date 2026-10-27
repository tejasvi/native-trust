import NativeTrust
import ClaimStatusInterval
import OntologyAlignmentRepair
import OntologyClaimStatus
import OntologyELClosureVerified
import OntologyELPlus
import OntologyELPlusClosureComplete
import OntologyELPlusNormalization
import OntologyELReasoner
import OntologyEvolutionRepair
import OntologyMinimalRepair
import OntologyRepairEquivalence
import OntologyRepairTies
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth OntologyELPlusNormalization 0 (config := { split := 8 })
prove_native_axiom_nth OntologyELReasoner 5 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlus 6 (config := { split := 8 })
prove_native_axiom_nth OntologyEvolutionRepair 4 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlusClosureComplete 2 (config := { split := 8 })
prove_native_axiom_nth OntologyEvolutionRepair 1 (config := { split := 8 })
prove_native_axiom_nth ClaimStatusInterval 5 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlus 2 (config := { split := 8 })
prove_native_axiom_nth ClaimStatusInterval 1 (config := { split := 8 })
prove_native_axiom_nth OntologyMinimalRepair 6 (config := { split := 8 })
prove_native_axiom_nth OntologyRepairTies 1 (config := { split := 8 })
prove_native_axiom_nth OntologyEvolutionRepair 0 (config := { split := 8 })
prove_native_axiom_nth OntologyClaimStatus 0 (config := { split := 8 })
prove_native_axiom_nth OntologyELClosureVerified 3 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlus 1 (config := { split := 8 })
prove_native_axiom_nth OntologyELClosureVerified 0 (config := { split := 8 })
prove_native_axiom_nth OntologyELReasoner 7 (config := { split := 8 })
prove_native_axiom_nth OntologyELClosureVerified 6 (config := { split := 8 })
prove_native_axiom_nth OntologyELReasoner 2 (config := { split := 8 })
prove_native_axiom_nth OntologyMinimalRepair 8 (config := { split := 8 })
prove_native_axiom_nth OntologyRepairEquivalence 2 (config := { split := 8 })
prove_native_axiom_nth OntologyEvolutionRepair 3 (config := { split := 8 })
prove_native_axiom_nth OntologyMinimalRepair 5 (config := { split := 8 })
prove_native_axiom_nth ClaimStatusInterval 6 (config := { split := 8 })
prove_native_axiom_nth OntologyAlignmentRepair 2 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlusClosureComplete 0 (config := { split := 8 })
prove_native_axiom_nth OntologyELReasoner 8 (config := { split := 8 })
prove_native_axiom_nth OntologyELPlus 4 (config := { split := 8 })
prove_native_axiom_nth OntologyRepairEquivalence 1 (config := { split := 8 })
prove_native_axiom_nth OntologyMinimalRepair 9 (config := { split := 8 })
