import NativeTrust
import AxA
import F1_axa_2
set_option nativeTrust.eprint true
prove_native_axiom_nth AxA 0
prove_native_axiom_nth AxA 1
kernelize nested
#print axioms nested.kernel
