import NativeTrust
import KfPrime
import PrimeCerts

@[kernel_fact] theorem babybear_kf : Fact (Nat.Prime pBabybear) := PrimeCerts.fact_prime_babybear

#print axioms pBabybear_prime
kernelize pBabybear_prime (config := { trace := true })
kernelize pBabybear_pos
#print axioms pBabybear_prime.kernel
#print axioms pBabybear_pos.kernel
