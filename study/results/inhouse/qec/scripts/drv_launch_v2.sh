#!/bin/bash
# task 3: drv_launch_v1.sh + `--include-file FILE`, passed on as `--include "<contents of FILE>"` (a long anchored
# regex cannot be quoted through ssh/sudo/systemd-run). Starts the capped driver inside this systemd unit (Delegate=yes,
# User=ntbuild): moves out of the unit's root cgroup, enables the memory controller for a jobs/ subtree, then execs
# python with CG_BASE=<unit cgroup>/jobs. usage: drv_launch_v2.sh SCRIPT.py ARGS... [--include-file FILE]
set -u
CG=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
case "$CG" in /sys/fs/cgroup/system.slice/qec-*) ;; *) echo "REFUSE: not in a qec unit cgroup: $CG"; exit 2;; esac
args=()
while [ $# -gt 0 ]; do
  if [ "$1" = --include-file ]; then args+=(--include "$(cat "$2")"); shift 2; else args+=("$1"); shift; fi
done
mkdir "$CG/driver" "$CG/jobs" || exit 2
echo $$ > "$CG/driver/cgroup.procs" || exit 2
echo +memory > "$CG/cgroup.subtree_control" || exit 2
echo +memory > "$CG/jobs/cgroup.subtree_control" || exit 2
export CG_BASE=$CG/jobs
exec env PYTHONDONTWRITEBYTECODE=1 python3 -I -B "${args[@]}"
