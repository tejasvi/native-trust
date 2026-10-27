import NativeTrust

/-! CI policy: `linter.nativeTrust.strict` makes "native_decide is unnecessary" an error. -/

set_option linter.nativeTrust true
set_option linter.nativeTrust.strict true

theorem st_sum : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

theorem st_ok : (List.range 100).foldl (· + ·) 0 = 4950 := by decide +kernel
