#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3ms_bvs_build_v2.sh TC...   -- run as ntbuild in a systemd unit v3ms-bvsbuild<k>-sweeps (paper v3, sweeps).
# Check that the archived bvs add-on (study/addon_versions/bvs_ed02e2be, the version behind the paper's bv_decide
# numbers) builds unchanged for each toolchain TC and can be imported together with NativeTrust v15:
#  1. copy SRC=$NT_BOX/v3/sweeps/bvs/src_ed02e2be to B=$NT_BOX/v3/sweeps/bvs/build_TC (refused if B
#     exists; SRC must hold no symlinks) and check the add-on digest of the copy (ed02e2be...c566, the README rule:
#     sha256 over the sorted per-file sha256 lines; .lake and the lake-manifest.json that lake writes are excluded);
#     with RETRY=1 an existing B is used after the same digest check (a retry of a failed step, same copy);
#  2. `lake build` with TC's own lake binary (sources and lean-toolchain untouched; elan is not used), 2 threads;
#  3. `lake env lean Audit.lean` (the axiom audit of the 15 soundness theorems; lines "AUDIT name: axioms [...];
#     non-standard [...]; kind ...");
#  4. `lake build Examples.Small Examples.UnaryOps` (re-proves the small examples; CaDiCaL from TC);
#  5. one file `import NativeTrust` + `import BVS` with #print axioms of BVS.bvs_unsat4, BVS.bvs_unsat5 and
#     BVS.unsat_of_cnf, on LEAN_PATH = NativeTrust v15 build of TC (nt_fix14/TC, else v3/nt_v15/TC, each only with
#     its result file "TC OK"; skipped if neither exists) : B's build : TC's lib.
# Per-process limits: 48 GiB address space (none with NOVMEM=1, a diagnostic), 65536 open files, 3600 s.
# v2 (from v1): RETRY, NOVMEM, open files as in the driver, the audit counted from its AUDIT lines, steps tagged with
# the attempt (TAG, default v2). Results: $NT_BOX/v3/sweeps/bvs/build_check.tsv (tc, step, rc, seconds,
# note); logs in B/v3ms_<step>_<TAG>.log.
set -u
# leading arguments RETRY=1, NOVMEM=1, TAG=word set those variables (the launcher passes no environment)
while [ $# -gt 0 ]; do
  case "$1" in RETRY=1|NOVMEM=1) export "$1"; shift;; TAG=[a-z0-9]*) export "$1"; shift;; *) break;; esac
done
M=${NT_BOX}/v3/sweeps; S=$M/bvs/src_ed02e2be; T=$M/bvs/build_check.tsv
DIG=ed02e2be9146a2c1bda8b044faf15bd8d2b861c9ed8bc21e68a04b9fe359c566
TAG=${TAG:-v2}
export ELAN_HOME=${NT_BOX}/elan LEAN_NUM_THREADS=2
digest() { (cd "$1" && find . -path ./.lake -prune -o -type f ! -path ./lake-manifest.json ! -name 'v3ms_*' -printf '%P\n' | LC_ALL=C sort | xargs sha256sum | sha256sum | cut -d' ' -f1); }
rec() { printf '%s\t%s\t%s\t%s\t%s\n' "$@" >> $T; }
[ -d "$S" ] || { echo "no $S"; exit 2; }
[ "$(find "$S" -type l | wc -l)" = 0 ] || { echo "symlinks in $S"; exit 2; }
[ "$(digest "$S")" = $DIG ] || { echo "digest of $S differs"; exit 2; }
for tc in "$@"; do
  TB=$ELAN_HOME/toolchains/leanprover--lean4---$tc
  B=$M/bvs/build_$tc
  case "$B" in $M/bvs/build_v4.*) ;; *) rec "$tc" setup_$TAG 2 0 "bad dir $B"; continue;; esac
  [ -x "$TB/bin/lake" ] || { rec "$tc" setup_$TAG 2 0 "toolchain not installed"; continue; }
  if [ -e "$B" ]; then
    [ "${RETRY:-0}" = 1 ] || { rec "$tc" setup_$TAG 3 0 "refused: $B exists"; continue; }
    [ "$(find "$B" -type l | wc -l)" = 0 ] || { rec "$tc" setup_$TAG 2 0 "symlinks in $B"; continue; }
  else
    cp -r "$S" "$B" || { rec "$tc" setup_$TAG 2 0 "copy failed"; continue; }
  fi
  d=$(digest "$B"); [ "$d" = $DIG ] || { rec "$tc" setup_$TAG 2 0 "copy digest $d"; continue; }
  cd "$B" || continue
  step() {  # name, command...
    local n=${1}_$TAG; shift; local s=$(date +%s)
    ( ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); [ "${NOVMEM:-0}" = 1 ] || ulimit -v 50331648
      PATH=$TB/bin:$PATH timeout -k 30 3600 "$@" ) > "$B/v3ms_$n.log" 2>&1
    local rc=$?; rec "$tc" "$n" $rc $(( $(date +%s) - s )) "$(command grep -m1 -E 'error|failed to create' "$B/v3ms_$n.log" | cut -c1-200)"
    return $rc
  }
  step build "$TB/bin/lake" build || continue
  step audit "$TB/bin/lake" env lean Audit.lean
  na=$(command grep -c '^AUDIT ' "$B/v3ms_audit_$TAG.log"); ns=$(command grep -c '^AUDIT .*; non-standard \[\]; ' "$B/v3ms_audit_$TAG.log")
  rec "$tc" audit_axioms_$TAG $((na - ns)) 0 "AUDIT lines=$na with non-standard []=$ns (expected 15)"
  step examples "$TB/bin/lake" build Examples.Small Examples.UnaryOps
  NT=""
  for r in ${NT_BOX}/nt_fix14 ${NT_BOX}/v3/nt_v15; do
    command grep -q "^$tc OK" "$r/result_$tc.txt" 2>/dev/null && [ -f "$r/$tc/.lake/build/lib/lean/NativeTrust.olean" ] && { NT=$r/$tc; break; }
  done
  if [ -z "$NT" ]; then rec "$tc" joint_$TAG 9 0 "skipped: no NativeTrust v15 build for $tc"; continue; fi
  printf 'import NativeTrust\nimport BVS\n#print axioms BVS.bvs_unsat4\n#print axioms BVS.bvs_unsat5\n#print axioms BVS.unsat_of_cnf\n' > "$B/v3ms_Joint.lean"
  export LEAN_PATH=$NT/.lake/build/lib/lean:$B/.lake/build/lib/lean:$TB/lib/lean
  step joint "$TB/bin/lean" -j1 v3ms_Joint.lean
  unset LEAN_PATH
  rec "$tc" joint_axioms_$TAG 0 0 "nt=$NT standard_only=$(command grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' "$B/v3ms_joint_$TAG.log") of 3"
done
echo "$(date -u +%FT%TZ) done $TAG $*" >> $M/logs/bvsbuild.log
