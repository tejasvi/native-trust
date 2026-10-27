import BVS
/-!
# Example: small facts, one process

`bv_decide` proves each theorem with an auxiliary axiom whose proof is native evaluation.
`bvs4_kernelize t` proves the same statement as `t.bvs4`, checked by the kernel; the command fails
unless the new theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

theorem ex_xor (x y : BitVec 16) : (x ^^^ y) ^^^ y = x := by bv_decide
theorem ex_and_or (x y : BitVec 16) : (x &&& y) + (x ||| y) = x + y := by bv_decide
theorem ex_mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_decide
theorem ex_shift (x s : BitVec 16) (h : s < 16) :
    (x <<< s) >>> s = x &&& (BitVec.allOnes 16 >>> s) := by bv_decide

bvs4_kernelize ex_xor
bvs4_kernelize ex_and_or
bvs4_kernelize ex_mul_three
bvs4_kernelize ex_shift

-- the original depends on the native axiom of `bv_decide`, the copy does not
#print axioms ex_mul_three
#print axioms ex_mul_three.bvs4
example : ∀ x : BitVec 16, x * 3 = x + x + x := ex_mul_three.bvs4
