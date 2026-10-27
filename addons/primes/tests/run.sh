#!/bin/bash
# Rebuild the library and run the checks (one Lean process at a time, 1 thread, 32 GB cap).
# usage: NT_LIB=DIR MATHLIB_PROJECT=DIR tests/run.sh   (from anywhere; writes tests/*.out)
#   NT_LIB: lib/lean of a NativeTrust build; MATHLIB_PROJECT: a Lake project with Mathlib (for LEAN_PATH)
set -u
D=$(cd "$(dirname "$0")/.." && pwd)   # the primes directory
NT=${NT_LIB:?set NT_LIB to the lib/lean directory of a NativeTrust build}   # NativeTrust oleans (KfPrimeCheck only)
LP=$(cd "${MATHLIB_PROJECT:?set MATHLIB_PROJECT to a Lake project with Mathlib}" && lake env printenv LEAN_PATH) || exit 8
export LEAN_PATH="$LP:$D:$D/tests:$NT"
export LEAN_NUM_THREADS=1
ulimit -v 33554432
L() { nice -n 10 timeout 580 /usr/bin/time -f "WALL %e s  MAXRSS %M KB" lean -j1 "$@"; }
cd "$D" || exit 9
echo "== PrattCert";  L -o PrattCert.olean -i PrattCert.ilean PrattCert.lean 2>&1 | tail -5
echo "== PrimeCerts"; L -o PrimeCerts.olean -i PrimeCerts.ilean PrimeCerts.lean 2>&1 | tail -5
echo "== Axioms";     L tests/Axioms.lean > tests/Axioms.out 2>&1; tail -1 tests/Axioms.out
echo "   standard-three lines: $(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' tests/Axioms.out)"
echo "   other lines:"; grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' tests/Axioms.out
echo "== Controls (expect errors at C1..C8 only)"; L tests/Controls.lean > tests/Controls.out 2>&1
grep -E "^tests/Controls.lean:[0-9]+:[0-9]+: error" tests/Controls.out | cut -d: -f2 | tr '\n' ' '; echo; tail -1 tests/Controls.out
echo "== KTime";      L tests/KTime.lean > tests/KTime.out 2>&1; sed 's/^.*info: //' tests/KTime.out
echo "== KfPrime + KfPrimeCheck (NativeTrust @[kernel_fact])"
L -o tests/KfPrime.olean tests/KfPrime.lean 2>&1 | tail -3
# through a pipe: NativeTrust writes its trace to /dev/stderr, which a file redirection would overwrite
L tests/KfPrimeCheck.lean 2>&1 | cat > tests/KfPrimeCheck.out; cat tests/KfPrimeCheck.out
