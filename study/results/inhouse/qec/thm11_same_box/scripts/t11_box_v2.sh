#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# QEC Theorem 1.1 on the box (request of 10-26): the native version (the 10 QEC/ChecksN/N_* modules, AllN, Thm11V2)
# and the kernel-only version (the 390 QEC/Checks modules, AllK, Thm11V3), compiled like the project's run_checks.sh and
# run_final.sh: one lean process per module, LEAN_NUM_THREADS=1, nice 10, the same -D options; the 13-size per-outcome
# chunks F_[ZX]_13_* first at JOBS_BIG at once, then the other kernel modules at JOBS at once. Sources: a copy of those
# files from the v2 tree (export of 643d947); outputs into a fresh root T/out, which comes first on LEAN_PATH; the library
# and Mathlib oleans are read from the existing build, which is not modified. Per module: wall, user, sys, max RSS
# (GNU time); per phase: this unit's cgroup CPU. Runs as ntbuild inside its own systemd unit (MemoryMax) under the
# core-hour guard. usage: JOBS=24 JOBS_BIG=12 t11_box_v2.sh
# v2 (from v1, whose every module failed at once): Lean resolves all QEC.* modules under the FIRST LEAN_PATH root that
# has a QEC directory, so the fresh root T/out also gets a copy of the library's QEC oleans (all but QEC/Checks and
# QEC/ChecksN, plus QEC.olean) before the build; the copy is checked file by file against the existing build.
set -u
T=${NT_BOX}/work_resv8/qec_t11b; SRC=$T/src; OUT=$T/out; LG=$T/logs; Q=${NT_BOX}/work_resv8/qec/lean4
B=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
JOBS=${JOBS:-24}; JOBS_BIG=${JOBS_BIG:-12}
export ELAN_HOME=${NT_BOX}/elan PATH=$B:${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
[ -e "$OUT" ] && { echo "REFUSE: $OUT exists"; exit 2; }
mkdir -p "$SRC/QEC/Checks" "$SRC/QEC/ChecksN" "$OUT/QEC/Checks" "$OUT/QEC/ChecksN" "$LG" || exit 2
cp "$Q"/QEC/Checks/*.lean "$Q"/QEC/Checks/LIST.txt "$SRC/QEC/Checks/" && cp "$Q"/QEC/ChecksN/*.lean "$SRC/QEC/ChecksN/" || exit 2
[ "$(find "$SRC" -type l | wc -l)" = 0 ] || { echo "REFUSE: symlinks in $SRC"; exit 2; }
L0=$Q/.lake/build/lib/lean
( cd "$L0" && find QEC -name '*.olean' ! -path 'QEC/Checks/*' ! -path 'QEC/ChecksN/*' -print0 | xargs -0 cp --parents -t "$OUT/" && cp QEC.olean "$OUT/" ) || exit 2
( cd "$OUT" && find QEC QEC.olean -name '*.olean' ! -path 'QEC/Checks/*' ! -path 'QEC/ChecksN/*' -print0 | xargs -0 sha256sum ) > "$LG/libcopy.sum" || exit 2
( cd "$L0" && sha256sum -c --quiet "$LG/libcopy.sum" ) || { echo "REFUSE: library copy differs"; exit 2; }
echo "library oleans copied: $(wc -l < "$LG/libcopy.sum")" >> "$LG/phases.log"
LP=$(cd "$Q" && lake env printenv LEAN_PATH) || exit 2
export LEAN_PATH=$OUT:$LP OUT LG B
cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
phase() { echo "$(date -u +%FT%TZ) $1 cpu_usec=$(awk '/usage_usec/{print $2}' "$cg/cpu.stat") jobs=$JOBS jobs_big=$JOBS_BIG" >> "$LG/phases.log"; }
one() {  # SRCPATH (relative, without .lean)
  m=$1; out=$OUT/$m.olean; n=$(echo "$m" | tr / _)
  /usr/bin/time -o "$LG/time_$n.txt" -f '%e %U %S %M' nice -n 10 "$B/lean" -o "$out.tmp" -DautoImplicit=false \
    -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dweak.linter.style.header=false "$m.lean" > "$LG/out_$n.txt" 2>&1
  rc=$?
  if [ $rc -eq 0 ]; then mv "$out.tmp" "$out"; st=OK; else rm -f "$out.tmp"; st=FAIL; fi
  echo "$m $st $(tail -n 1 "$LG/time_$n.txt")" >> "$LG/build.log"
}
export -f one
cd "$SRC" || exit 2
phase start
/usr/bin/grep -E '^F_[ZX]_13_' QEC/Checks/LIST.txt | sed 's|^|QEC/Checks/|' | xargs -P "$JOBS_BIG" -n 1 bash -c 'one "$0"'
phase kernel_big_done
( /usr/bin/grep '_13_' QEC/Checks/LIST.txt | /usr/bin/grep -vE '^F_[ZX]_13_'; /usr/bin/grep -v '_13_' QEC/Checks/LIST.txt ) |
  sed 's|^|QEC/Checks/|' | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
phase kernel_checks_done
one QEC/Checks/AllK; one QEC/Checks/Thm11V3
phase kernel_final_done
ls QEC/ChecksN/N_*.lean | sed 's/\.lean$//' | xargs -P "$JOBS" -n 1 bash -c 'one "$0"'
phase native_checks_done
one QEC/ChecksN/AllN; one QEC/ChecksN/Thm11V2
phase native_final_done
