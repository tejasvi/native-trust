import MigBudget.Defs

/-! Examples leave no fact in the `.olean`: the budget is enforced in the build rounds. -/

example : (List.range 20).length = 20 := by native_decide

example : divSum 1500 = 11190 := by native_decide
