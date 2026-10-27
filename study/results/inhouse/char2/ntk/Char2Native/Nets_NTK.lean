import Char2Comp.NetData
import Char2Comp.NetCheck
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! The comb-network certificates (A1, A2, B1, B2, E) of Char2Comp/NetData.lean, by `native_decide`. -/
namespace Char2
namespace Net

theorem n2_1_1_0_ok : netOK 2 1 1 0 n2_1_1_0_N n2_1_1_0_tau n2_1_1_0_x n2_1_1_0_A1 n2_1_1_0_A2 n2_1_1_0_B1 n2_1_1_0_B2 n2_1_1_0_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n2_1_1_1_ok : netOK 2 1 1 1 n2_1_1_1_N n2_1_1_1_tau n2_1_1_1_x n2_1_1_1_A1 n2_1_1_1_A2 n2_1_1_1_B1 n2_1_1_1_B2 n2_1_1_1_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n2_2_1_0_ok : netOK 2 2 1 0 n2_2_1_0_N n2_2_1_0_tau n2_2_1_0_x n2_2_1_0_A1 n2_2_1_0_A2 n2_2_1_0_B1 n2_2_1_0_B2 n2_2_1_0_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n2_2_1_1_ok : netOK 2 2 1 1 n2_2_1_1_N n2_2_1_1_tau n2_2_1_1_x n2_2_1_1_A1 n2_2_1_1_A2 n2_2_1_1_B1 n2_2_1_1_B2 n2_2_1_1_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n2_2_1_2_ok : netOK 2 2 1 2 n2_2_1_2_N n2_2_1_2_tau n2_2_1_2_x n2_2_1_2_A1 n2_2_1_2_A2 n2_2_1_2_B1 n2_2_1_2_B2 n2_2_1_2_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n3_1_1_0_ok : netOK 3 1 1 0 n3_1_1_0_N n3_1_1_0_tau n3_1_1_0_x n3_1_1_0_A1 n3_1_1_0_A2 n3_1_1_0_B1 n3_1_1_0_B2 n3_1_1_0_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n3_1_1_1_ok : netOK 3 1 1 1 n3_1_1_1_N n3_1_1_1_tau n3_1_1_1_x n3_1_1_1_A1 n3_1_1_1_A2 n3_1_1_1_B1 n3_1_1_1_B2 n3_1_1_1_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n5_1_1_0_ok : netOK 5 1 1 0 n5_1_1_0_N n5_1_1_0_tau n5_1_1_0_x n5_1_1_0_A1 n5_1_1_0_A2 n5_1_1_0_B1 n5_1_1_0_B2 n5_1_1_0_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem n5_1_1_1_ok : netOK 5 1 1 1 n5_1_1_1_N n5_1_1_1_tau n5_1_1_1_x n5_1_1_1_A1 n5_1_1_1_A2 n5_1_1_1_B1 n5_1_1_1_B2 n5_1_1_1_E = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end Net
end Char2
