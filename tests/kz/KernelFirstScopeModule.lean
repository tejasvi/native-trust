module

import NativeTrust.KernelFirstLite

/-! `KernelFirstScope.lean` as a module-system file: here too
`import NativeTrust.KernelFirstLite` passes nothing beyond `Init` on to the importer, so the
structure-instance shorthand `{ grok, seat }` below elaborates as before. -/

inductive Seat where
  | root | sub
deriving DecidableEq

structure Cell where
  grok : Bool := false
  seat : Seat := .root
deriving DecidableEq

def allCells : List Cell := Id.run do
  let mut acc : List Cell := []
  for grok in [false, true] do
    for seat in [Seat.root, .sub] do
      acc := acc ++ [{ grok, seat }]
  return acc

/-- the kernel proves it: no native axiom -/
theorem ks_cells : allCells.length = 4 := by native_decide

theorem ks_native : (List.range 50).foldl (· + ·) 0 = 1225 := by decide +native

/-- a `partial` function: no kernel definition, compiled evaluation as before -/
partial def countDown (n : Nat) : Nat := if n = 0 then 0 else countDown (n - 1)

theorem ks_partial : countDown 5 = 0 := by native_decide

/-- over the budget (2000 thousand heartbeats): compiled evaluation as before -/
theorem ks_budget : (List.range 100000).foldl (· + ·) 0 = 4999950000 := by decide +native

#print axioms ks_cells
#print axioms ks_native
#print axioms ks_partial
#print axioms ks_budget
