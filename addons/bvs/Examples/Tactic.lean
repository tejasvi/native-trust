import BVS
/-!
# Example: the tactic `bv_kdecide`

`bv_kdecide` is written where `bv_decide` would be. Each theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`; `#bvk_assert_std` fails otherwise.
-/

open Lean Elab Command in
/-- Fails unless each listed constant depends only on `propext`, `Classical.choice` and `Quot.sound`. -/
elab "#bvk_assert_std " ids:ident* : command => liftTermElabM do
  for id in ids do
    let n ← realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
      throwError "{n} depends on the axioms {axs.toList}"
    logInfo m!"{n}: axioms {axs.toList}"

theorem k_xor (x y : BitVec 16) : (x ^^^ y) ^^^ y = x := by bv_kdecide
theorem k_and_or (x y : BitVec 16) : (x &&& y) + (x ||| y) = x + y := by bv_kdecide
theorem k_mul_three (x : BitVec 16) : x * 3 = x + x + x := by bv_kdecide
theorem k_shift (x s : BitVec 16) (h : s < 16) :
    (x <<< s) >>> s = x &&& (BitVec.allOnes 16 >>> s) := by bv_kdecide
theorem k_cpop_not (x : BitVec 16) : (~~~x).cpop + x.cpop = 16#16 := by bv_kdecide

/-- `bv_decide`'s preprocessing closes this goal; there is no SAT call and no axiom to replace. -/
theorem k_norm (x : BitVec 8) : x &&& x = x := by bv_kdecide

/-- A configuration is passed on to `bv_decide`. -/
theorem k_config (x : BitVec 8) : x * 2 = x <<< 1 := by bv_kdecide (config := { timeout := 60 })

/-- `UInt8` and `Bool` are handled by `bv_decide`'s preprocessing. -/
theorem k_uint (a b : UInt8) (h : a < b) : a ≠ b := by bv_kdecide
theorem k_bool (p q : Bool) (x : BitVec 4) (h : p = (x == 0)) : (p && q) = true → x = 0 := by bv_kdecide

/-- Enumeration types and structures are handled by `bv_decide`'s preprocessing; for the enumeration
it creates `Color.enumToBitVec` and related declarations, which `bv_kdecide` keeps. -/
inductive Color where
  | red | green | blue
  deriving DecidableEq
theorem k_enum (c : Color) (h1 : c ≠ .red) (h2 : c ≠ .green) : c = .blue := by bv_kdecide
structure Pair where
  a : BitVec 8
  b : BitVec 8
theorem k_struct (p q : Pair) (h : p.a = q.b) (h2 : p.b = q.a) : p.a + p.b = q.a + q.b := by bv_kdecide

/-- Two calls in one proof, inside a term and after `have`. -/
theorem k_two (x y : BitVec 8) : x * 3 = x + x + x ∧ (x &&& y) + (x ||| y) = x + y :=
  ⟨by bv_kdecide, by bv_kdecide⟩
theorem k_have (x : BitVec 8) (h : x < 16) : x * 2 < 32 ∧ x + 1 ≠ 0 := by
  have h2 : x * 2 < 32 := by bv_kdecide
  exact ⟨h2, by bv_kdecide⟩
set_option Elab.async false in
theorem k_two_sync (x y : BitVec 8) : x * 3 = x + x + x ∧ (x &&& y) + (x ||| y) = x + y :=
  ⟨by bv_kdecide, by bv_kdecide⟩

/-- The split base check, which is used above `bvs4.splitAbove` clauses (default 200,000), forced here
with segments of 500 nodes. -/
theorem k_split (x y : BitVec 64) : (x &&& y) + (x ||| y) = x + y := by
  set_option bvs4.splitAbove 0 in
  set_option bvs4.segment 500 in
  bv_kdecide

set_option maxHeartbeats 1000 in
/-- The kernel checks of `bv_kdecide` do not count against the heartbeat budget of the rest of the proof
(here 1000 · 1000 heartbeats, less than these checks take). -/
theorem k_heartbeats (x : BitVec 16) (n : Nat) (h : n = 2) : x * 3 = x + x + x ∧ n + n = 4 := by
  refine ⟨by bv_kdecide, ?_⟩
  subst h
  simp

namespace KEx
private theorem k_priv (x y : BitVec 8) : (x &&& y) ||| (x &&& ~~~y) = x := by bv_kdecide
theorem k_pub (x y : BitVec 8) : (x &&& y) ||| (x &&& ~~~y) = x := k_priv x y
end KEx

example (x : BitVec 32) : x * 3 = x + x + x := by bv_kdecide

#bvk_assert_std k_xor k_and_or k_mul_three k_shift k_cpop_not k_norm k_config k_uint k_bool k_two k_have
  k_two_sync k_split k_heartbeats k_enum k_struct KEx.k_pub
