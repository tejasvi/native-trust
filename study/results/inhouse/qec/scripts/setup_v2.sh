#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# task 3: QEC project setup v2 (as ntbuild, inside unit qec-setup2 with MemoryMax). The box cannot reach
# github.com, so `lake exe cache get` failed (setup_v1); the package set (Mathlib c55e6e786f49 prebuilt + deps, all at
# the manifest revisions) was copied from the main VM and sha-verified. Here: (1) `lake build --no-build Mathlib`
# must succeed (prebuilt Mathlib up to date, nothing to rebuild), else stop; (2) lake build QEC QECComp.
set -u
Q=${NT_BOX}/work_resv8/qec; L=$Q/lean4; LOG=$Q/setup.log
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=32
cd "$L" || exit 2
echo "$(date -u +%FT%TZ) setup v2 start" >> "$LOG"
/usr/bin/time -a -o "$LOG" -f "nobuild_check_Mathlib: %e s wall %U s user %S s sys %M KB rc=%x" lake build --no-build Mathlib >> "$Q/nobuild_check.out" 2>&1 || { echo "$(date -u +%FT%TZ) STOP: Mathlib not up to date" >> "$LOG"; exit 3; }
/usr/bin/time -a -o "$LOG" -f "build_QEC_QECComp: %e s wall %U s user %S s sys %M KB rc=%x" lake build QEC QECComp >> "$Q/build_lib.out" 2>&1
echo "$(date -u +%FT%TZ) setup v2 end" >> "$LOG"
