#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# s13_fact_v2.sh (S(13) probe; v2: thread stack TSTACK_KB as an argument, default of v1 = 1048576): run as ntbuild inside a systemd scope (MemoryMax). Elaborates one probe
# file DIR/ID.lean (a restated fact or a prove_native_axiom_nth file) with NativeTrust v15 for v4.35.0-rc3 and the
# project's build on LEAN_PATH, single-threaded, under a wall-clock limit, as the driver does. Log DIR/ID.log.
# usage: s13_fact_v2.sh DIR ID TIMEOUT_S TSTACK_KB
D=${1:?}; ID=${2:?}; T=${3:?}; TS=${4:?}
case "$TS" in *[!0-9]*) echo "bad tstack"; exit 2;; esac
case "$D" in ${NT_BOX}/work_iterstr/s13/probe_*) ;; *) echo "bad dir $D"; exit 2;; esac
case "$ID" in *[!A-Za-z0-9_]*) echo "bad id"; exit 2;; esac
cd $D || exit 3
[ -e $ID.log ] && { echo "refusing: $ID.log exists"; exit 3; }
L=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean
P=${NT_BOX}/work_iterstr/s13/lean_s45
NT=${NT_BOX}/nt_fix14/v4.35.0-rc3/.lake/build/lib/lean
PK=$(for p in $P/.lake/packages/*; do printf "%s:" $p/.lake/build/lib/lean; done)
export LEAN_PATH=$NT:$P/.lake/build/lib/lean:${PK}$D ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=1
echo "\$ lean $ID.lean start=$(date -u +%FT%TZ) timeout=$T tstack=$TS" > $ID.log
timeout -k 30 $T /usr/bin/time -f "maxrss_kb %M secs %e" $L -j1 --tstack=$TS $ID.lean >> $ID.log 2>&1
echo "rc=$? end=$(date -u +%FT%TZ)" >> $ID.log
