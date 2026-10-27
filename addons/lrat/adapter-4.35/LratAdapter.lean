import LratBits
import LratBitsSound
import Std.Sat.CNF
/-! Adapter for Lean ≥ 4.35 (`CNF.Clause` is a structure with packed atoms and polarities). -/
namespace LratBits
open Std.Sat

/-- The clauses of a CNF as literal lists. -/
def toL (cnf : CNF Nat) : List (List (Nat × Bool)) := cnf.clauses.toList.map (fun c => c.literals)

/-- Soundness against core's notion: acceptance implies `CNF.Unsat`. -/
theorem unsat_of_checkBits (cnf : CNF Nat) (acts : List (List BAct))
    (h : checkBits (toL cnf) acts = true) : cnf.Unsat := by
  intro a
  have h1 := unsat_list_of_checkBits _ acts h a
  unfold toL at h1
  rw [List.all_map] at h1
  show cnf.clauses.all (fun c => CNF.Clause.eval a c) = false
  rw [← Array.all_toList]
  exact h1

end LratBits
