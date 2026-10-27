import BVS
import Examples.GroupB
/-!
# Example: facts from two modules, converted together

`gb_both` (module `Examples.GroupB`) uses the fact of its own module and, through `ga_mul_three`, the fact of
`Examples.GroupA`. Converting `Examples.GroupB` alone would rebuild `gb_both` with a proof that still refers to
the original `ga_mul_three` and therefore to its native axiom. `bvs5_group` converts both facts in one process
and rebuilds `ga_mul_three`, `gb_and_or` and `gb_both` (as `bvsg_1`, `bvsg_2`, `bvsg_3`, in dependency order),
each with the original statement and only the standard axioms.
-/

bvs5_group "Examples.GroupA:0" "Examples.GroupB:0"

#print axioms gb_both    -- the native axioms of both facts
#print axioms bvsg_3     -- [propext, Classical.choice, Quot.sound]
example : ∀ x y : BitVec 8, x * 3 = x + x + x ∧ (x &&& y) + (x ||| y) = x + y := bvsg_3
