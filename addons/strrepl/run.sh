#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild): run.sh SUBDIR FILE.lean   -- compile with NativeTrust + StrRepl + berry-esseen LEAN_PATH
set -u
SUB=${1:?}; F=${2:?}
TC=v4.34.0-rc2; D=${NT_BOX}/strrepl/$TC
PKG=${NT_BOX}/repos/berry-esseen
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
PLP=$(cd $PKG && lake env printenv LEAN_PATH)
export LEAN_PATH=${NT_BOX}/nt14/$TC/.lake/build/lib/lean:$D:$D/$SUB:$PLP
cd $D/$SUB || exit 2
ulimit -v $((48*1024*1024)); ulimit -s unlimited
B=${F%.lean}
/usr/bin/time -f "maxrss_kb %M secs %e" timeout -k 30 ${TIMEOUT:-3600} ${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean -j1 --tstack=1048576 -o "$B.olean" "$F" > "$B.log" 2>&1
echo "rc=$?" >> "$B.log"
