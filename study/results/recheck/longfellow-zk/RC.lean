import NativeTrust
import Lfzk.CertifiedV7
import Lfzk.CompiledV7S
import Lfzk.LigeroV1RowsV7
import Lfzk.TwoFieldV7Rows
import examples.Ligero.Longfellow.AdaptiveCountCertificates
import examples.Ligero.Longfellow.AdaptiveHashCertificates
import examples.Ligero.Longfellow.OptimizedIOPCertificates
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 114 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 70 (config := { split := 8 })
prove_native_axiom_nth Lfzk.TwoFieldV7Rows 4 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 133 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 4 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveCountCertificates 4 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 116 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 236 (config := { split := 8 })
prove_native_axiom_nth Lfzk.CertifiedV7 61 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 149 (config := { split := 8 })
prove_native_axiom_nth Lfzk.CompiledV7S 8 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 130 (config := { split := 8 })
prove_native_axiom_nth Lfzk.TwoFieldV7Rows 0 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 108 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 196 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 78 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 55 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 204 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 104 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 125 (config := { split := 8 })
prove_native_axiom_nth Lfzk.CertifiedV7 42 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 39 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 186 (config := { split := 8 })
prove_native_axiom_nth Lfzk.CertifiedV7 20 (config := { split := 8 })
prove_native_axiom_nth Lfzk.LigeroV1RowsV7 8 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 27 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.OptimizedIOPCertificates 4 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 61 (config := { split := 8 })
prove_native_axiom_nth Lfzk.LigeroV1RowsV7 2 (config := { split := 8 })
prove_native_axiom_nth examples.Ligero.Longfellow.AdaptiveHashCertificates 231 (config := { split := 8 })
