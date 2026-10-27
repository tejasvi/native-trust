import NativeTrust
import StrRepl

set_option Elab.async false
#kernel_blockers_const String.Slice.isNat
#kernel_blockers_const String.Slice.toNat?
#kernel_blockers_const String.toNat?
#kernel_blockers_const String.toInt?
#check @String.Slice.foldl
#print String.Slice.toNat?
