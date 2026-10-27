import LratBits
import LratBitsSound
import Std.Sat.CNF
/-! Adapter for Lean 4.31-4.34 (`CNF.Clause α = List (Literal α)`). -/
namespace LratBits
open Std.Sat

/-- The clauses of a CNF as literal lists. -/
def toL (cnf : CNF Nat) : List (List (Nat × Bool)) := cnf.clauses.toList

/-- Soundness against core's notion: acceptance implies `CNF.Unsat`. -/
theorem unsat_of_checkBits (cnf : CNF Nat) (acts : List (List BAct))
    (h : checkBits (toL cnf) acts = true) : cnf.Unsat := by
  intro a
  have h1 := unsat_list_of_checkBits _ acts h a
  show cnf.clauses.all (fun c => CNF.Clause.eval a c) = false
  rw [← Array.all_toList]
  exact h1

end LratBits
