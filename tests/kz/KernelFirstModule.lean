module

import NativeTrust.KernelFirst

/-! `NativeTrust.KernelFirst` imported from a module-system file. -/

set_option Elab.async false

public theorem kfm_sum : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

public theorem kfm_sort : (List.range 30).reverse.mergeSort = List.range 30 := by native_decide

#print axioms kfm_sum
#print axioms kfm_sort
#kernel_first_summary
