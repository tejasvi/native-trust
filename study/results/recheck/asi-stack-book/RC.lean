import NativeTrust
import AsiStackProofs.ArtifactRealityRefinement
import AsiStackProofs.Authority
import AsiStackProofs.AuthorityEffectRefinement
import AsiStackProofs.CoilAttentionMemory
import AsiStackProofs.ContextTransactionRefinement
import AsiStackProofs.EvidenceTransitionRefinement
import AsiStackProofs.FailureRecoveryRefinement
import AsiStackProofs.GovernedOperations
import AsiStackProofs.GovernedOperationsRefinement
import AsiStackProofs.GovernedWorldModels
import AsiStackProofs.HumanAIOrganizations
import AsiStackProofs.HumanFactorsOversight
import AsiStackProofs.IntentExecutionRefinement
import AsiStackProofs.OpenEndedImprovementRefinement
import AsiStackProofs.ProofCarryingContracts
import AsiStackProofs.Replacement
import AsiStackProofs.ResourceEconomics
import AsiStackProofs.ResourceEconomicsRefinement
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth AsiStackProofs.FailureRecoveryRefinement 6 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.FailureRecoveryRefinement 7 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ContextTransactionRefinement 0 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.OpenEndedImprovementRefinement 2 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedWorldModels 11 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.EvidenceTransitionRefinement 2 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ProofCarryingContracts 4 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedWorldModels 0 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.Authority 16 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.HumanFactorsOversight 1 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.AuthorityEffectRefinement 9 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.HumanAIOrganizations 7 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ContextTransactionRefinement 2 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedOperationsRefinement 5 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedWorldModels 6 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedOperations 2 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ResourceEconomics 1 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.FailureRecoveryRefinement 9 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.Replacement 4 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedWorldModels 14 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.Authority 20 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ProofCarryingContracts 0 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.HumanAIOrganizations 12 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ArtifactRealityRefinement 0 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.CoilAttentionMemory 0 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.IntentExecutionRefinement 6 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.ResourceEconomicsRefinement 1 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.HumanAIOrganizations 10 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.CoilAttentionMemory 1 (config := { split := 8 })
prove_native_axiom_nth AsiStackProofs.GovernedOperations 7 (config := { split := 8 })
