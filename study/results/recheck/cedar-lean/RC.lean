import NativeTrust
import Cedar.Data.Int64
import Cedar.Thm.SymCC.Data.Ext
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 7 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 2 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 0 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 6 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 1 (config := { split := 8 })
prove_native_axiom_nth Cedar.Data.Int64 0 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 4 (config := { split := 8 })
prove_native_axiom_nth Cedar.Data.Int64 1 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 3 (config := { split := 8 })
prove_native_axiom_nth Cedar.Thm.SymCC.Data.Ext 5 (config := { split := 8 })
