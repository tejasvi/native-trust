#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# task 3: the project's native check scripts, in verify_all.sh's order without run_checks.sh (the 390 kernel-only
# modules of Theorem 1.1, which have no native facts; run_final.sh's two kernel modules then fail at import), JOBS=32,
# as ntbuild inside unit qec-checks (MemoryMax). GNU time per script; the unit cgroup's CPU (cpu.stat) after each.
set -u
Q=${NT_BOX}/work_resv8/qec; L=$Q/lean4; LOG=$Q/checks.log
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH JOBS=32
cd "$L" || exit 2
cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
echo "$(date -u +%FT%TZ) checks start cpu_usec=$(awk '/usage_usec/{print $2}' "$cg/cpu.stat")" >> "$LOG"
for s in "run_final.sh" "run_checks8.sh" "run_checksW.sh L" "run_checksW.sh He" "run_checksW.sh Hl" "run_checksW.sh H2" \
         "run_finalW.sh" "run_checksS.sh S8" "run_checksS.sh SL" "run_checksS.sh SHe" "run_checksS.sh SHl" \
         "run_checksS.sh SH2" "run_finalS.sh"; do
  /usr/bin/time -a -o "$LOG" -f "$s: %e s wall %U s user %S s sys rc=%x" bash scripts/$s >> "$Q/checks_${s// /_}.out" 2>&1
  echo "$(date -u +%FT%TZ) after $s cpu_usec=$(awk '/usage_usec/{print $2}' "$cg/cpu.stat")" >> "$LOG"
done
echo "$(date -u +%FT%TZ) checks end" >> "$LOG"
