#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3_addon_build_v1.sh (v3, package add-ons): run as ntbuild inside a systemd scope (MemoryMax). Compiles the add-on
# modules MOD... (sources already copied into $NT_BOX/v3/addons/NAME) against NativeTrust v15
# ($NT_BOX/nt_fix14/TC) and the package's search path LP (a cached LEAN_PATH file, or the path itself), in order.
# usage: v3_addon_build_v1.sh NAME TC LP MOD...
N=${1:?}; TC=${2:?}; LP=${3:?}; shift 3
case "$N" in *[!a-z0-9_]*) echo "bad name"; exit 2;; esac
D=${NT_BOX}/v3/addons/$N
L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
NT=${NT_BOX}/nt_fix14/$TC/.lake/build/lib/lean
[ -f "$NT/NativeTrust.olean" ] || { echo "no NativeTrust build $NT"; exit 3; }
if [ -f "$LP" ]; then PLP=$(cat "$LP"); else PLP="$LP"; fi
export LEAN_PATH="$NT:$D:$PLP" ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1
cd "$D" || exit 3
echo "start $(date -u +%FT%TZ) $N tc=$TC"
for m in "$@"; do
  [ -e "$m.olean" ] && { echo "refusing: $D/$m.olean exists"; exit 3; }
  /usr/bin/time -f "maxrss_kb %M secs %e" $L -j1 --tstack=1048576 -o $m.olean $m.lean > build_$m.log 2>&1
  rc=$?
  echo "$N $m rc=$rc $(tail -1 build_$m.log) errors=$(command grep -c 'error' build_$m.log)"
  [ $rc -eq 0 ] || exit $rc
done
echo "end $(date -u +%FT%TZ)"
