import StrRepl
import Cedar.Spec.Ext.Util

/-!
# Cedar-specific replacements (test artifact, not part of the core-only add-on)

`Cedar.Spec.Ext.toInt?'` / `toNat?'` call the pattern-generic `String.contains` with a `Char`
pattern. `String.contains` itself cannot be registered (its type quantifies over the searcher),
but these monomorphic callers can: `String.contains_char_eq` (core, v4.35.0) turns the test into
list membership, and `StrRepl.toNat?_eq_list` / `StrRepl.toInt?_eq` give list-based bodies (a
replacement's body is used as it is, so it must not call `String.toNat?` itself).
-/

namespace NativeTrust.StrRepl.Cedar

def toIntQ (str : String) : Option Int :=
  if decide ('_' ∈ str.toList) then .none else NativeTrust.StrRepl.toIntOfSlice? str.toSlice

@[kernel_replace] theorem toIntQ_eq : @Cedar.Spec.Ext.toInt?' = @toIntQ := by
  funext str
  simp only [Cedar.Spec.Ext.toInt?', toIntQ, String.contains_char_eq, NativeTrust.StrRepl.toInt?_eq]

def toNatQ (str : String) : Option Nat :=
  if decide ('_' ∈ str.toList) then .none else NativeTrust.StrRepl.toNatOfList? str.toList

@[kernel_replace] theorem toNatQ_eq : @Cedar.Spec.Ext.toNat?' = @toNatQ := by
  funext str
  simp only [Cedar.Spec.Ext.toNat?', toNatQ, String.contains_char_eq, NativeTrust.StrRepl.toNat?_eq_list]

end NativeTrust.StrRepl.Cedar
