import NativeTrust
import Strata.Languages.Core.Factory
import StrataTest.DL.SMT.DenoteTests
import StrataTest.DL.SMT.EncoderTests
import StrataTest.Languages.Core.Tests.Logic.Hoare
import StrataTest.Languages.Core.Tests.Logic.HoareCall
import StrataTest.Languages.Core.Tests.Logic.HoareUnstructured
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.Hoare 17 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.Hoare 70 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 8 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.Hoare 7 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 18 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 12 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.Hoare 28 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 0 (config := { split := 8 })
prove_native_axiom_nth Strata.Languages.Core.Factory 2 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 20 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.DenoteTests 0 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.HoareUnstructured 11 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.HoareCall 7 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 5 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 10 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.HoareUnstructured 44 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 9 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.HoareCall 16 (config := { split := 8 })
prove_native_axiom_nth StrataTest.DL.SMT.EncoderTests 11 (config := { split := 8 })
prove_native_axiom_nth StrataTest.Languages.Core.Tests.Logic.HoareUnstructured 19 (config := { split := 8 })
