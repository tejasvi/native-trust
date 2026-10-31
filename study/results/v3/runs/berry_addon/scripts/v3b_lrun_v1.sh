#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_lrun_v1.sh (v3 BerryEsseen, parse-once covers; adapted from the archived lrun3.sh): run as ntbuild. Compiles
# DIR/NAME.lean (to NAME.olean when OLEAN=1) with LEAN_PATH = NativeTrust v15 (nt_fix14/v4.34.0-rc2) :
# $NT_BOX/v3/berry/lib : DIR : BerryEsseen's search path, under an address-space cap of MEMGB GiB and a wall-clock
# limit of TO seconds. Writes NAME.log (lean's standard output, then rc= and the time line) and NAME.err (its standard
# error, where NativeTrust's trace lines go; kept apart, as the archived lrun3.sh did, so that the two streams never
# share a file). No slots: the scheduler admits jobs.
# usage: [OLEAN=1] MEMGB=G TO=S v3b_lrun_v1.sh DIR NAME
D=${1:?}; N=${2:?}
case "$D" in ${NT_BOX}/v3/berry/covers/*) ;; *) echo "DIR must be under ${NT_BOX}/v3/berry/covers"; exit 2;; esac
case "$N" in *[!A-Za-z0-9_]*) echo "bad name"; exit 2;; esac
cd "$D" || exit 2
TC=v4.34.0-rc2
export ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
LPF=${NT_BOX}/work_bigcert/lp_34e448b1.txt
export LEAN_PATH=${NT_BOX}/nt_fix14/$TC/.lake/build/lib/lean:${NT_BOX}/v3/berry/lib:$D:$(cat $LPF)
L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
( ulimit -v $((${MEMGB:?}*1024*1024)); ulimit -s unlimited
  /usr/bin/time -o "$N.time" -f "TIME %e s %M KB" timeout -k 30 ${TO:?} $L -j1 --tstack=1048576 ${OLEAN:+-o $N.olean} "$N.lean" > "$N.log" 2> "$N.err"
  echo "rc=$?" >> "$N.log"; cat "$N.time" >> "$N.log" )
