import NativeTrust

/-! Minimal reproduction of the "copies of definitions that occur in types" patterns of DyLean
(BobDyLean), core only. A well-founded function (`ack`, lexicographic measure) is reached through an
instance field; the instance then occurs
* as a phantom parameter of a structure (`Fmt Nat instSizer`, like `ExtensibleMessageFormat Bytes inst a`),
* in the field type of a class (`HasFmt.fmt : Fmt Nat instSizer`, like `ParseableSerializeable`),
* as a parameter of an inductive type declared with an instance variable (`Ev`, like `SignedDHEvent`),
* in a dependent class field (`Ext.fmt : Fmt Nat toBase.sz`, like `HasExecTrace extends HasExecBytes`). -/

namespace TR

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

class Sizer (α : Type) where
  size : α → Nat

instance instSizer : Sizer Nat where
  size n := ack 1 n

/-- the instance is a phantom parameter -/
structure Fmt (α : Type) [Sizer α] where
  enc : α → Nat

def mkFmt : Fmt Nat := ⟨fun n => Sizer.size n + 1⟩

/-- 1. the instance in a class field type -/
class HasFmt where
  fmt : Fmt Nat

instance instHasFmt : HasFmt := ⟨mkFmt⟩

def useFmt [h : HasFmt] (n : Nat) : Nat := h.fmt.enc n

theorem t1 : useFmt 3 = 6 := by native_decide

/-- 2. an inductive type with an instance parameter, and a dependent class field -/
class Base where
  sz : Sizer Nat

instance instBase : Base := ⟨instSizer⟩

section
variable [Base]
inductive Ev where
  | a (n : Nat)
  | b
  deriving DecidableEq

def evSize : Ev → Nat
  | .a n => @Sizer.size Nat Base.sz n
  | .b => 0
end

class Ext extends Base where
  fmt : @Fmt Nat toBase.sz

instance instExt : Ext := { toBase := instBase, fmt := ⟨fun n => @Sizer.size Nat instSizer n + 2⟩ }

def pick [Ext] (i : Nat) : Option Ev := if i = 0 then some (.a 4) else none

theorem t2 : (match pick 0 with | some e => evSize e | none => 0) + Ext.fmt.enc 2 = 12 := by native_decide

/-- 3. the instance in types, and a cast in a `Decidable` instance (built with `simp`) that evaluation
reaches only through the parametric route: the route's cast retry (`NativeTrust.CastFree`). -/
structure Pt where
  x : Nat
  y : Nat

instance instDecEqPt : DecidableEq Pt := fun a b => by
  cases a; cases b
  simp only [Pt.mk.injEq]
  exact inferInstance

structure Fmt2 (α : Type) [Sizer α] where
  test : α → Bool

def mkFmt2 : Fmt2 Nat := ⟨fun n => decide ((⟨Sizer.size n, 0⟩ : Pt) = ⟨n + 2, 0⟩)⟩

class HasFmt2 where
  fmt : Fmt2 Nat

instance instHasFmt2 : HasFmt2 := ⟨mkFmt2⟩

def useFmt2 [h : HasFmt2] (n : Nat) : Bool := h.fmt.test n

theorem t3 : useFmt2 5 = true := by native_decide

end TR

set_option Elab.async false
trust_check TR.t1 +trace -accFallback
trust_check TR.t2 +trace -accFallback
trust_check TR.t3 +trace -accFallback
