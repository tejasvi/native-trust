import NativeTrust
import KfA

set_option nativeTrust.eprint true

/-- A proof of the decided proposition made another way (here `decide`; in a field library, a
primality certificate): used instead of evaluating. -/
@[kernel_fact] theorem kf97 : isPrimeB 97 = true := by decide

#native_axioms KfA
prove_native_axiom_nth KfA 0 (config := { trace := true })
prove_native_axiom_nth KfA 1 (config := { trace := true })
