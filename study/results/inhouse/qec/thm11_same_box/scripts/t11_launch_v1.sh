#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# Theorem 1.1 same-box launch (as root via sudo): reads the sum of MemoryMax over ALL capped units on the box
# (every owner) right before the start; refuses unless sum + CAP_G <= LINE_G and MemAvailable >= CAP_G + 64 GiB; appends
# a START line naming the real unit to $NT_BOX/work_resv8/BOXES.log; starts unit qec-t11 (as ntbuild,
# MemoryMax=CAP_G, no swap) running the core-hour guard (cap 6 core-h: the job is killed at 6 core-h minus 60 s) around
# t11_box_v1.sh with JOBS/JOBS_BIG; then re-reads the sum and logs it.
set -u
UNIT=qec-t11; CAP_G=200; LINE_G=600; J=24; JB=12; X=${NT_BOX}/work_resv8/box/t11; T=${NT_BOX}/work_resv8/qec_t11
BL=${NT_BOX}/work_resv8/BOXES.log
capsum() { local s=0 p m; for p in /sys/fs/cgroup/system.slice/*.service /sys/fs/cgroup/system.slice/*.scope; do
  m=$(cat "$p/memory.max" 2>/dev/null) || continue; [ "$m" = max ] && continue; s=$((s + m / 1073741824)); done; echo $s; }
s1=$(capsum); avail=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
if [ $((s1 + CAP_G)) -gt $LINE_G ] || [ "$avail" -lt $((CAP_G + 64)) ]; then
  echo "$(date -u +%FT%TZ) REFUSED $UNIT capsum=${s1}G + ${CAP_G}G > ${LINE_G}G or MemAvailable ${avail}G" | tee -a "$BL"; exit 3; fi
[ -e "$T" ] && { echo "REFUSE: $T exists"; exit 2; }
mkdir -p "$T" && chown ntbuild:ntbuild "$T" || exit 2
echo "$(date -u +%FT%TZ) START unit=$UNIT.service owner=qec-run job=QEC Thm 1.1 native+kernel same-box build MemoryMax=${CAP_G}G jobs=$J/$JB guard=6 core-h (est 2 core-h, ~25 min) capsum_before=${s1}G MemAvailable=${avail}G" | tee -a "$BL"
systemd-run --quiet --collect --unit=$UNIT -p MemoryMax=${CAP_G}G -p MemorySwapMax=0 --uid=ntbuild --gid=ntbuild \
  --setenv=JOBS=$J --setenv=JOBS_BIG=$JB /usr/bin/python3 -I -B "$X/coreh_guard_v2.py" "$T/guard.log" 6 --run -- /bin/bash "$X/t11_box_v1.sh"
rc=$?
sleep 10
echo "$(date -u +%FT%TZ) launched $UNIT.service rc=$rc capsum_after=$(capsum)G active=$(systemctl is-active $UNIT.service)" | tee -a "$BL"
