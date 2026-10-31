import G_Veir_Interpreter_Memory_0
import Veir.Interpreter.Memory
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_0.unsat
#print axioms bvs5_1
#print axioms bvs5_2
#print axioms bvs5_3
#print axioms bvs5_4
#print axioms bvs5_5
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "_private.Veir.Interpreter.Memory.0.Veir.MemoryState.loadByte64._proof_1")).type}"
  IO.println s!"TYPE\tbvs5_2\t{(← getConstInfo (parse "bvs5_2")).type == (← getConstInfo (parse "Veir.MemoryState.loadByte64")).type}"
  IO.println s!"TYPE\tbvs5_3\t{(← getConstInfo (parse "bvs5_3")).type == (← getConstInfo (parse "Veir.MemoryState.llvmLoad")).type}"
  IO.println s!"TYPE\tbvs5_4\t{(← getConstInfo (parse "bvs5_4")).type == (← getConstInfo (parse "Veir.MemoryState.memcpy")).type}"
  IO.println s!"TYPE\tbvs5_5\t{(← getConstInfo (parse "bvs5_5")).type == (← getConstInfo (parse "Veir.MemoryState.memmove")).type}"
