import NativeTrust
import Cpc.Proofs.Closed.IsClosedRec
import Cpc.Proofs.RuleSupport.BvDivPow2Support
import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecShift
import Cpc.Proofs.Rules.Bool_not_ite_elim
import Cpc.Proofs.Rules.Bv_ashr_by_const_0
import Cpc.Proofs.Rules.Bv_ashr_zero
import Cpc.Proofs.Rules.Bv_commutative_comp
import Cpc.Proofs.Rules.Bv_ite_const_children_2
import Cpc.Proofs.Rules.Bv_ite_merge_then_if
import Cpc.Proofs.Rules.Bv_lshr_by_const_0
import Cpc.Proofs.Rules.Bv_sge_eliminate
import Cpc.Proofs.Rules.Bv_sgt_eliminate
import Cpc.Proofs.Rules.Bv_shl_zero
import Cpc.Proofs.Rules.Bv_sle_eliminate
import Cpc.Proofs.Rules.Bv_udiv_zero
import Cpc.Proofs.Rules.Bv_uge_eliminate
import Cpc.Proofs.Rules.Bv_ugt_eliminate
import Cpc.Proofs.Rules.Ite_then_true
import Cpc.Proofs.Rules.Uf_int2bv_bv2nat
import Cpc.Proofs.Rules.Uf_sbv_to_int_elim
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 79 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 589 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 464 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_sgt_eliminate 7 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 400 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_shl_zero 19 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Closed.IsClosedRec 119 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ugt_eliminate 0 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecShift 2 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_udiv_zero 2 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 26 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ite_const_children_2 5 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_sge_eliminate 8 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_commutative_comp 2 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 523 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_sgt_eliminate 9 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Closed.IsClosedRec 140 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_uge_eliminate 10 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Closed.IsClosedRec 159 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 517 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Ite_then_true 0 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_sle_eliminate 7 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 346 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ashr_zero 8 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.RuleSupport.BvDivPow2Support 0 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ashr_by_const_0 19 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 535 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ugt_eliminate 20 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 556 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_sle_eliminate 5 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_lshr_by_const_0 18 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Closed.IsClosedRec 93 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Closed.IsClosedRec 149 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 184 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 312 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 273 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Uf_sbv_to_int_elim 0 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Uf_int2bv_bv2nat 10 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bool_not_ite_elim 189 (config := { split := 8 })
prove_native_axiom_nth Cpc.Proofs.Rules.Bv_ite_merge_then_if 0 (config := { split := 8 })
