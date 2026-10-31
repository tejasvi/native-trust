#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3ms_be4_v1.sh   -- run as ntbuild in the systemd unit v3ms-be4-sweeps (72G, one process; paper v3, sweeps).
# BerryEsseen's BE4 fact (_private.BerryEsseen.Upper0423.Covers.Data.BE4.0.BerryEsseen.Upper0423.Covers.Data.BE4.accepted
# ._native.native_decide.ax_1_1), converted only in the heavy pass with well-founded copies (v3h-berry-esseen: 490 s,
# 66 GiB), checked again WITHOUT the well-founded replacement: the heavy pass's own check file
# (work/v3h-berry-esseen/mods/F2_BerryEsseen_Upper0423_Covers_Data_BE4_0.lean) with `wf := false` added to its config
# (split 8 and everything else unchanged), the heavy pass's command (lean -j1 --tstack=1048576 under /usr/bin/time), its
# limits (3600 s, 96 GiB address space), the same library build (nt_fix14/v4.34.0-rc2) and LEAN_PATH as the v3 driver
# computes it. Files in $NT_BOX/v3/sweeps/be4/.
set -u
D=${NT_BOX}/v3/sweeps/be4; PKG=${NT_BOX}/repos/berry-esseen; TC=v4.34.0-rc2
SRC=${NT_BOX}/work/v3h-berry-esseen/mods/F2_BerryEsseen_Upper0423_Covers_Data_BE4_0.lean
F=F2wf_BerryEsseen_Upper0423_Covers_Data_BE4_0
mkdir -p $D && cd $D || exit 2
[ -e $F.lean ] && { echo "refused: $D/$F.lean exists"; exit 3; }
command grep -q '^prove_native_axiom_nth BerryEsseen.Upper0423.Covers.Data.BE4 0 (config := { split := 8, trace := true })$' $SRC || { echo "unexpected check file"; exit 2; }
awk '{ if ($0 ~ /^prove_native_axiom_nth /) sub(/trace := true \}\)$/, "trace := true, wf := false })"); print }' $SRC > $F.lean
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
LP=$(cd $PKG && lake env printenv LEAN_PATH) || exit 2
export LEAN_PATH=${NT_BOX}/nt_fix14/$TC/.lake/build/lib/lean:$LP
L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
{ echo "start $(date -u +%FT%TZ) $F.lean"; cat $F.lean; } > $F.log
s=$(date +%s)
( ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v 100663296
  exec timeout -k 30 3600 /usr/bin/time -f "maxrss_kb %M" $L -j1 --tstack=1048576 $F.lean ) >> $F.log 2>&1
rc=$?
echo "rc=$rc secs=$(( $(date +%s) - s )) end $(date -u +%FT%TZ)" >> $F.log
