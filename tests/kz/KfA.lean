/-! A native fact inside an instance (as `Fact (Nat.Prime p)` instances are in field libraries), and a
fact whose statement mentions the instance. -/

def isPrimeB (n : Nat) : Bool := n ≥ 2 && (List.range n).all fun d => d < 2 || n % d != 0

class PrimeFact (n : Nat) : Prop where
  ok : isPrimeB n = true

instance pf97 : PrimeFact 97 := ⟨by native_decide⟩

structure ZP (p : Nat) [PrimeFact p] where
  v : Nat

def zval (x : ZP 97) : Nat := x.v % 97

theorem t200 : zval ⟨200⟩ = 6 := by native_decide
