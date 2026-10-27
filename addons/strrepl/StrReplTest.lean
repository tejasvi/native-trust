import NativeTrust
import StrRepl

set_option Elab.async false
set_option maxHeartbeats 0

#print axioms NativeTrust.StrRepl.sliceFoldl_eq
#print axioms NativeTrust.StrRepl.sliceIsNat_eq

-- static triage with the replacements registered
#kernel_blockers_const String.toNat?
#kernel_blockers_const String.toInt?

theorem t_toNat : ("613200".toNat? = some 613200) := by kdecide
theorem t_toNat_us : ("1_000".toNat? = some 1000 ∧ "12__3".toNat? = none ∧ "".toNat? = none) := by kdecide
theorem t_toInt : ("-37".toInt? = some (-37) ∧ "413".toInt? = some 413 ∧ "-".toInt? = none) := by kdecide
theorem t_parse : (("413/100".splitOn "/").map String.toNat? = [some 413, some 100]) := by kdecide

#print axioms t_toNat
#print axioms t_toInt
#print axioms t_parse
