#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run_sizes_v1.sh (fail-116 analysis, read-only): re-runs the earlier sizes.lean (#eval of the minidregg array sizes and
# the jam length) against the study's minidregg build (commit 307b13ea, toolchain v4.30.0, cached search path
# lp_4c938c39), with plain lean (no lake). Output $NT_BOX/v3/opt/fail116/sizes_v3.log.
set -u
D=${NT_BOX}/v3/opt/fail116
[ -f "$D/sizes.lean" ] || { echo "missing $D/sizes.lean"; exit 3; }
[ -e "$D/sizes_v3.log" ] && { echo "refusing: $D/sizes_v3.log exists"; exit 3; }
export LEAN_PATH=$(cat ${NT_BOX}/work_bigcert/lp_4c938c39.txt) LEAN_NUM_THREADS=1
cd "$D" || exit 3
/usr/bin/time -f "maxrss_kb %M secs %e" timeout 600 ${NT_BOX}/elan/toolchains/leanprover--lean4---v4.30.0/bin/lean sizes.lean > sizes_v3.log 2>&1
echo "rc=$? end=$(date -u +%FT%TZ)" >> sizes_v3.log
