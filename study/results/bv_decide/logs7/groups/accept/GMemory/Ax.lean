import GMemory
import Veir.Interpreter.Memory
#print axioms bvsg_Veir_Interpreter_Memory_0.unsat
#print axioms bvsg_Veir_Interpreter_Memory_1.unsat
#print axioms bvsg_1
#print axioms bvsg_2
#print axioms bvsg_3
#print axioms bvsg_4
#print axioms bvsg_5
#print axioms bvsg_6
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvsg_1 _private.Veir.Interpreter.Memory.0.Veir.MemoryState.llvmLoad._proof_1 {(← getConstInfo (parseN "bvsg_1")).type == (← getConstInfo (parseN "_private.Veir.Interpreter.Memory.0.Veir.MemoryState.llvmLoad._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_2 _private.Veir.Interpreter.Memory.0.Veir.MemoryState.loadByte64._proof_1 {(← getConstInfo (parseN "bvsg_2")).type == (← getConstInfo (parseN "_private.Veir.Interpreter.Memory.0.Veir.MemoryState.loadByte64._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_3 Veir.MemoryState.loadByte64 {(← getConstInfo (parseN "bvsg_3")).type == (← getConstInfo (parseN "Veir.MemoryState.loadByte64")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_4 Veir.MemoryState.llvmLoad {(← getConstInfo (parseN "bvsg_4")).type == (← getConstInfo (parseN "Veir.MemoryState.llvmLoad")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_5 Veir.MemoryState.memcpy {(← getConstInfo (parseN "bvsg_5")).type == (← getConstInfo (parseN "Veir.MemoryState.memcpy")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_6 Veir.MemoryState.memmove {(← getConstInfo (parseN "bvsg_6")).type == (← getConstInfo (parseN "Veir.MemoryState.memmove")).type}"
  pure ()
