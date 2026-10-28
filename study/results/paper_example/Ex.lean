import NativeTrust

theorem t : (List.range 300).reverse.mergeSort = List.range 300 := by native_decide
#print axioms t
kernelize t
#print axioms t.kernel
#check @t.kernel
