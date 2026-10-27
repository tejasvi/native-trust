import NativeTrust.KernelFirst
import Std.Data.HashMap

/-! `import NativeTrust.KernelFirst`: every `native_decide`/`decide +native` tries `decide +kernel`
first (budget `nativeTrust.kernelHeartbeats`) and uses compiled evaluation only when the kernel does
not prove the goal. -/

set_option Elab.async false

theorem kf_sum : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

theorem kf_native : (List.range 50).foldl (· + ·) 0 = 1225 := by decide +native

theorem kf_two : (List.range 10).length = 10 ∧ (List.range 20).length = 20 := by
  constructor <;> native_decide

/-- a `partial` function: no kernel definition, compiled evaluation -/
partial def countDown (n : Nat) : Nat := if n = 0 then 0 else countDown (n - 1)

theorem kf_partial : countDown 5 = 0 := by native_decide

/-- `HashMap` (platform word size): compiled evaluation -/
def squares : Std.HashMap Nat Nat := (List.range 10).foldl (fun m i => m.insert i (i * i)) {}

theorem kf_hashmap : squares[3]? = some 9 := by native_decide

/-- over the budget: compiled evaluation -/
theorem kf_budget : (List.range 100000).foldl (· + ·) 0 = 4999950000 := by native_decide

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

/-- well-founded recursion: plain kernel evaluation cannot run it, compiled evaluation -/
theorem kf_wf : lexAck 2 3 = 9 := by native_decide

/-- a false goal still fails as before -/
example : (List.range 10).length = 11 := by native_decide

-- switched off
set_option nativeTrust.kernelFirst false in
theorem kf_off : (List.range 10).length = 10 := by native_decide

/-- plain `decide` is untouched -/
theorem kf_decide : (List.range 10).length = 10 := by decide

#print axioms kf_sum
#print axioms kf_native
#print axioms kf_two
#print axioms kf_partial
#print axioms kf_hashmap
#print axioms kf_budget
#print axioms kf_wf
#print axioms kf_off
#print axioms kf_decide
#kernel_first_summary
