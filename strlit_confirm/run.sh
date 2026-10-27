#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild on the box: compile StrFast.olean, then each test file (v4.34.0-rc2, 1 thread, ulimit -v 24 GiB,
# timeout 600 s, 4 at once); NAME.log gets the output, "TIME <wall s> <max RSS KiB>" and rc
set -u
D=${NT_BOX}/strlit_confirm; cd $D || exit 2
L=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean
export LEAN_PATH=$D:${NT_BOX}/elan/toolchains/leanprover--lean4---v4.34.0-rc2/lib/lean LEAN_NUM_THREADS=1 L
[ -f StrFast.olean ] || $L -o StrFast.olean StrFast.lean > StrFast.build.log 2>&1 || { echo "StrFast build failed"; exit 3; }
one() { ( ulimit -v $((24*1024*1024)); ulimit -s unlimited
  /usr/bin/time -f "TIME %e %M" timeout -k 10 600 $L -j1 --tstack=1048576 "$1.lean" > "$1.log" 2>&1; echo "rc=$?" >> "$1.log" ) ; }
export -f one
printf '%s\n' Z_500 Z_1000 Z_2000 Z_4000 Z_8000 B_500 B_1000 B_2000 B_4000 B_8000 A_500 A_1000 A_2000 | xargs -P 4 -I{} bash -c 'one {}'
echo done > $D/ALL_DONE
