import MigBudget.Defs

/-! Facts for `ntrust migrate --fact-budget`: two cheap ones (rewritten within the default budget) and an
expensive one (plain `decide +kernel` proves it, but not within 2000 thousand heartbeats: it stays native). -/

theorem cheapSum : (List.range 50).foldl (· + ·) 0 = 1225 := by native_decide

theorem cheapMul : 3 * 7 = 21 := by decide +native

theorem slowDivSum : divSum 1500 = 11190 := by native_decide
