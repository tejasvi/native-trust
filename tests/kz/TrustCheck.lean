import NativeTrust
import KzNative
set_option Elab.async false
theorem plain : (List.range 10).length = 10 := by decide
theorem withSorry : (List.range 10).length = 10 := sorry
trust_check plain
trust_check sorted_check
trust_check withSorry
