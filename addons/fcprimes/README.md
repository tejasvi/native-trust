# formal-conjectures primes add-on

Pratt certificates, registered with `@[kernel_fact]`, for the primes 47059, 2217342227 and 1729101023519
that three formal-conjectures facts need. Without them the kernel decides `Nat.Prime p` by trial division up
to the square root of `p`, which does not finish within the study's limits for 1729101023519. The add-on
uses toolchain `v4.33.1`, the version the package pins.

| file | contents |
|---|---|
| `NTFcPrimes.lean` | the three certificates (6, 12 and 11 nodes); the kernel checks each with `decide +kernel` when the module builds |
| `PrattCert.lean` | the certificate checker, an unchanged copy of `addons/primes/PrattCert.lean` |
| `pratt_gen.py` | generates the certificates and checks them again |

To use the add-on, compile `PrattCert.lean` and then `NTFcPrimes.lean` to oleans in the package's
environment with a NativeTrust build for v4.33.1, then run the driver with `--extra-path <this directory> --extra-import
NTFcPrimes`.
