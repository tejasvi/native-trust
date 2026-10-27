import NativeTrust.KernelFirstLite

/-! `import NativeTrust.KernelFirstLite`: every `native_decide` and `decide +native` written without
further configuration first tries `decide +kernel` within 2000 thousand heartbeats, and runs the
original call, Lean's native path, only when the kernel does not prove the goal. A call that falls
back gets the same native axiom as without the switch. There are no options, no reasons and no
summary (see `NativeTrust.KernelFirst`). -/

set_option Elab.async false

theorem kl_sum : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

theorem kl_native : (List.range 50).foldl (· + ·) 0 = 1225 := by decide +native

theorem kl_two : (List.range 10).length = 10 ∧ (List.range 20).length = 20 := by
  constructor <;> native_decide

/-- a `partial` function: no kernel definition, compiled evaluation -/
partial def countDown (n : Nat) : Nat := if n = 0 then 0 else countDown (n - 1)

theorem kl_partial : countDown 5 = 0 := by native_decide

/-- far over the budget: the kernel attempt stops after 2000 thousand heartbeats, then compiled
evaluation -/
theorem kl_budget : (List.range 1000000).foldl (· + ·) 0 = 499999500000 := by native_decide

theorem kl_budget_native : (List.range 1000000).foldl (· + ·) 0 = 499999500000 := by decide +native

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

/-- well-founded recursion: plain kernel evaluation cannot run it, compiled evaluation -/
theorem kl_wf : lexAck 2 3 = 9 := by native_decide

/-- a false goal fails as without the switch -/
example : (List.range 10).length = 11 := by native_decide

/-- written with configuration: left to Lean, compiled evaluation without a kernel attempt -/
theorem kl_config : (List.range 12).length = 12 := by native_decide +revert

/-- plain `decide` is untouched -/
theorem kl_decide : (List.range 10).length = 10 := by decide

/-- also when it fails: no kernel attempt, no compiled evaluation -/
example : countDown 5 = 0 := by decide

#print axioms kl_sum
#print axioms kl_native
#print axioms kl_two
#print axioms kl_partial
#print axioms kl_budget
#print axioms kl_budget_native
#print axioms kl_wf
#print axioms kl_config
#print axioms kl_decide
