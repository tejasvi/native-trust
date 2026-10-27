module
import BVS
/-!
# Example: `bv_kdecide` in a file of the module system

`BVS` is a module, so `bv_kdecide` can be used in `module` files. The auxiliary declarations of the
tactic are private to this module; the theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

public theorem km_mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_kdecide
public theorem km_split (x y : BitVec 32) : (x &&& y) + (x ||| y) = x + y := by
  set_option bvs4.splitAbove 0 in
  set_option bvs4.segment 500 in
  bv_kdecide
theorem km_shift (x : BitVec 8) : x * 2 = x <<< 1 := by bv_kdecide
public theorem km_two (x y : BitVec 8) : x * 3 = x + x + x ∧ (x &&& y) + (x ||| y) = x + y :=
  ⟨by bv_kdecide, by bv_kdecide⟩
public theorem km_use (x : BitVec 8) : x * 2 = x <<< 1 := km_shift x

#print axioms km_mul_three
#print axioms km_split
#print axioms km_two
#print axioms km_use
