#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# con-ron launch (item 5), as root via sudo: con-ron (v4.35.0-rc3 toolchain, default --verified mode and worker
# count, as the 10-23 recheck did) on the v15 Theorem 1.1 export that nanoda checked. Reads the sum of MemoryMax over ALL
# capped units right before the start and refuses unless sum + CAP_G <= LINE_G and MemAvailable >= CAP_G + 64 GiB; writes
# a START line naming the real unit to $NT_BOX/work_resv8/BOXES.log; unit qec-conron11 (as ntbuild,
# MemoryMax=CAP_G, no swap) runs the core-hour guard (cap 1 core-h) around /usr/bin/time con-ron; the unit cgroup's
# memory.peak and CPU are appended to the log at the end; then re-reads the sum.
set -u
UNIT=qec-conron11; CAP_G=240; LINE_G=600; X=${NT_BOX}/work_resv8/box/t11; S=${NT_BOX}/work_resv8/qec/supp
B=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin; BL=${NT_BOX}/work_resv8/BOXES.log
capsum() { local s=0 p m; for p in /sys/fs/cgroup/system.slice/*.service /sys/fs/cgroup/system.slice/*.scope; do
  m=$(cat "$p/memory.max" 2>/dev/null) || continue; [ "$m" = max ] && continue; s=$((s + m / 1073741824)); done; echo $s; }
s1=$(capsum); avail=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
if [ $((s1 + CAP_G)) -gt $LINE_G ] || [ "$avail" -lt $((CAP_G + 64)) ]; then
  echo "$(date -u +%FT%TZ) REFUSED $UNIT capsum=${s1}G + ${CAP_G}G > ${LINE_G}G or MemAvailable ${avail}G" | tee -a "$BL"; exit 3; fi
[ -e "$S/Supp_thm11.conron.log" ] && { echo "REFUSE: con-ron log exists"; exit 2; }
echo "$(date -u +%FT%TZ) START unit=$UNIT.service owner=qec-run job=con-ron on the QEC Thm 1.1 v15 export MemoryMax=${CAP_G}G guard=1 core-h capsum_before=${s1}G MemAvailable=${avail}G" | tee -a "$BL"
systemd-run --quiet --collect --unit=$UNIT -p MemoryMax=${CAP_G}G -p MemorySwapMax=0 --uid=ntbuild --gid=ntbuild /bin/bash -c \
  "cd $S && /usr/bin/python3 -I -B $X/coreh_guard_v2.py $S/Supp_thm11.conron.guard.log 1 --run -- /usr/bin/time -f 'con-ron: %e s %M KB' $B/con-ron Supp_thm11.export > Supp_thm11.conron.log 2>&1; echo \"rc=\$?\" >> Supp_thm11.conron.log; cg=/sys/fs/cgroup\$(cut -d: -f3 /proc/self/cgroup); echo \"cg_memory_peak \$(cat \$cg/memory.peak) cg_cpu_usec \$(awk '/usage_usec/{print \$2}' \$cg/cpu.stat) \$(awk '\$1==\"oom_kill\"' \$cg/memory.events)\" >> Supp_thm11.conron.log"
rc=$?
sleep 10
echo "$(date -u +%FT%TZ) launched $UNIT.service rc=$rc capsum_after=$(capsum)G active=$(systemctl is-active $UNIT.service)" | tee -a "$BL"
