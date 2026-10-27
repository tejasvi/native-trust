import NativeTrust
import denote.gpt_ly4_regen.Goal122Bridge
import denote.gpt_ly4_regen.Goal125Bridge
import denote.gpt_ly4_regen.Goal144Bridge
import denote.gpt_ly4_regen.Goal147Bridge
import denote.gpt_ly4_regen.Goal159Bridge
import denote.gpt_ly4_regen.Goal177Bridge
import denote.gpt_ly4_regen.Goal23Bridge
import denote.gpt_ly4_regen.Goal244Bridge
import denote.gpt_ly4_regen.Goal310Bridge
import denote.gpt_ly4_regen.Goal31Bridge
import denote.gpt_ly4_regen.Goal58Bridge
import denote.gpt_ly4_regen.Goal78Bridge
import denote.gpt_ly4_regen.Goal94Bridge
import denote.yoco_goals.CanonicalGoal3L13Routing
import denote.yoco_goals.CanonicalGoal3L15Routing
import denote.yoco_goals.CanonicalGoal3L23Routing
import denote.yoco_goals.CanonicalKVCacheOrdinaryDown
import denote.yoco_goals.CanonicalL10OrdinaryAttention
import denote.yoco_goals.CanonicalL12AttentionComposition
import denote.yoco_goals.CanonicalL12ZigzagEntry
import denote.yoco_goals.CanonicalL15AttentionComposition
import denote.yoco_goals.CanonicalL17KVGraph
import denote.yoco_goals.CanonicalL18AttentionComposition
import denote.yoco_goals.CanonicalL18KVGraph
import denote.yoco_goals.CanonicalL19Output
import denote.yoco_goals.CanonicalL20KVGraph
import denote.yoco_goals.CanonicalL23Expert
import denote.yoco_goals.CanonicalL2OrdinaryAttention
import denote.yoco_goals.CanonicalL3OrdinaryAttention
import denote.yoco_goals.L0OrdinaryMoEDown
import denote.yoco_goals.L16ZigzagMoEOutput
import denote.yoco_goals.L1OrdinaryMoEGraphReductions
import denote.yoco_goals.L1OrdinaryQKV
import denote.yoco_goals.L2OrdinaryMoEBoundary
import denote.yoco_goals.L2OrdinaryMoEDown
import denote.yoco_goals.L3OrdinaryMoEBoundary
import denote.yoco_goals.L3OrdinaryMoEGraphReductions
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth denote.gpt_ly4_regen.Goal94Bridge 54 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalGoal3L23Routing 21 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal310Bridge 4 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L16ZigzagMoEOutput 4 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL18AttentionComposition 26 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal78Bridge 21 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L1OrdinaryQKV 134 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL19Output 39 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal125Bridge 3 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL3OrdinaryAttention 70 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal177Bridge 21 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL23Expert 7 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal31Bridge 27 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL12ZigzagEntry 19 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL17KVGraph 127 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL12AttentionComposition 45 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L3OrdinaryMoEBoundary 32 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalGoal3L13Routing 10 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L2OrdinaryMoEDown 55 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL18KVGraph 52 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal147Bridge 19 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L1OrdinaryMoEGraphReductions 73 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL2OrdinaryAttention 214 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal122Bridge 6 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal23Bridge 6 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L0OrdinaryMoEDown 182 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L3OrdinaryMoEGraphReductions 218 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL20KVGraph 11 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal244Bridge 10 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL10OrdinaryAttention 123 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal159Bridge 49 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalKVCacheOrdinaryDown 5 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal58Bridge 31 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L2OrdinaryMoEBoundary 39 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL3OrdinaryAttention 49 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalGoal3L15Routing 28 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL20KVGraph 224 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.CanonicalL15AttentionComposition 66 (config := { split := 8 })
prove_native_axiom_nth denote.gpt_ly4_regen.Goal144Bridge 65 (config := { split := 8 })
prove_native_axiom_nth denote.yoco_goals.L1OrdinaryMoEGraphReductions 250 (config := { split := 8 })
