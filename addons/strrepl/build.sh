#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild on the box): build.sh TOOLCHAIN FILE.lean [extra LEAN_PATH entries...]
# compiles FILE.lean to FILE.olean in $NT_BOX/strrepl/TOOLCHAIN, LEAN_PATH = nt14 lib + that dir + extras
set -u
TC=${1:?toolchain}; F=${2:?file}; shift 2
D=${NT_BOX}/strrepl/$TC
cd "$D" || exit 2
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
LP=${NT_BOX}/nt14/$TC/.lake/build/lib/lean:$D
for x in "$@"; do LP=$LP:$x; done
export LEAN_PATH=$LP
ulimit -v $((48*1024*1024)); ulimit -s unlimited
B=${F%.lean}
exec /usr/bin/time -f "maxrss_kb %M secs %e" timeout -k 30 ${TIMEOUT:-3000} ${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean -j1 --tstack=1048576 -o "$B.olean" "$F"
