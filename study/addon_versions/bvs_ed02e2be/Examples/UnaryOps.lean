import BVS
/-!
# Example: `reverse`, `clz` and `cpop`

The bit-blaster handles every unary operation of `bv_decide`'s `BVUnOp`, including bit reversal,
count leading zeros (`BitVec.clz`) and population count (`BitVec.cpop`).
-/

theorem ex_rev (x : BitVec 8) : x.reverse.reverse = x := by bv_decide
theorem ex_rev_and (x y : BitVec 16) : (x &&& y).reverse = x.reverse &&& y.reverse := by bv_decide
theorem ex_clz_zero (x : BitVec 16) : (x.clz = 16#16) = (x = 0#16) := by bv_decide
theorem ex_clz_le (x : BitVec 8) : x.clz ≤ 8#8 := by bv_decide
theorem ex_clz_msb (x : BitVec 32) (h : x.getMsbD 0 = true) : x.clz = 0#32 := by bv_decide
theorem ex_cpop_le (x : BitVec 8) : x.cpop ≤ 8#8 := by bv_decide
theorem ex_cpop_not (x : BitVec 16) : (~~~x).cpop + x.cpop = 16#16 := by bv_decide
theorem ex_ctz_lt (x : BitVec 16) (h : x ≠ 0#16) : x.reverse.clz < 16#16 := by bv_decide

bvs4_kernelize ex_rev
bvs4_kernelize ex_rev_and
bvs4_kernelize ex_clz_zero
bvs4_kernelize ex_clz_le
bvs4_kernelize ex_clz_msb
bvs4_kernelize ex_cpop_le
bvs4_kernelize ex_cpop_not
bvs4_kernelize ex_ctz_lt

#print axioms ex_cpop_not.bvs4
