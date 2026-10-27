#!/bin/bash
# run_tests.sh: run the NativeTrust tests against the library built in this directory.
#
# usage: lake build NativeTrust NativeTrust.KernelFirst NativeTrust.KernelFirstLite   (once)
#        ./run_tests.sh [OUT_DIR]          (default OUT_DIR: test_out/<toolchain>; it must not exist)
# environment: JOBS = number of Lean processes run at the same time (default 2).
#
# Each test file is copied to OUT_DIR and elaborated there with `lean`, the library on LEAN_PATH, under a 900 s
# time limit and a 48 GiB address-space limit; its output and exit code go to OUT_DIR/<test>.out.
# - a test file <T>.lean with a <T>.expected file next to it: the output is compared with the expected one after
#   masking timings and dropping timing and trace lines (for TypesRepro only the verdict lines are compared);
#   the result is SAME or DIFF, with the diff in OUT_DIR/<T>.exp.diff.
# - every other test file (tests/*.lean, tests/kz/*.lean) is run and reported with its exit code only. Files that
#   import Mathlib are skipped (the library has no Mathlib dependency).
# Test modules that other tests import (e.g. KzNative) are compiled first, to oleans in OUT_DIR.
# The expected outputs were produced with Lean v4.34.0; see tests/README.md for differences on other toolchains.
# Exit code: 0 if every compared test is SAME, 1 otherwise.
set -u
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT" || exit 2
TC=$(sed 's/.*://' lean-toolchain | tr -d '[:space:]')
OUT=${1:-$ROOT/test_out/$TC}
JOBS=${JOBS:-2}
[ -e "$OUT" ] && { echo "refusing: $OUT exists" >&2; exit 2; }
LP=$(lake env printenv LEAN_PATH) || { echo "lake env failed; run lake build first" >&2; exit 2; }
SYSROOT=$(lake env printenv LEAN_SYSROOT) || { echo "lake env failed" >&2; exit 2; }
LEAN=$SYSROOT/bin/lean
[ -x "$LEAN" ] || { echo "no lean at $LEAN" >&2; exit 2; }
[ -f "$ROOT/.lake/build/lib/lean/NativeTrust.olean" ] || { echo "NativeTrust is not built; run lake build first" >&2; exit 2; }
mkdir -p "$OUT" && cd "$OUT" || exit 2
export LEAN_PATH="$OUT:$LP" LEAN_NUM_THREADS=1

imports() { grep -E '^(public )?(meta )?import ' "$1" | awk '{print $NF}'; }
uses_mathlib() { imports "$1" | grep -q '^Mathlib'; }

# test files: name -> path (tests/kz first, then tests/)
declare -A SRC
for f in "$ROOT"/tests/kz/*.lean "$ROOT"/tests/*.lean; do
  n=$(basename "$f" .lean)
  [ -n "${SRC[$n]:-}" ] && { echo "duplicate test name $n" >&2; exit 2; }
  SRC[$n]=$f
done
# prerequisites: test modules imported by other test files
declare -A PRE
for n in "${!SRC[@]}"; do
  for m in $(imports "${SRC[$n]}"); do [ -n "${SRC[$m]:-}" ] && PRE[$m]=1; done
done
for n in "${!SRC[@]}"; do cp "${SRC[$n]}" "$OUT/$n.lean"; done

# compile prerequisites in dependency order (one at a time)
declare -A DONE
left=${#PRE[@]}
while [ "$left" -gt 0 ]; do
  progress=0
  for m in $(printf '%s\n' "${!PRE[@]}" | sort); do
    [ -n "${DONE[$m]:-}" ] && continue
    ready=1
    for d in $(imports "$m.lean"); do
      if [ -n "${PRE[$d]:-}" ] && [ -z "${DONE[$d]:-}" ]; then ready=0; fi
    done
    [ $ready = 1 ] || continue
    ( ulimit -v $((48*1024*1024)); timeout -k 30 900 "$LEAN" -o "$m.olean" -i "$m.ilean" "$m.lean" > "$m.build.out" 2>&1
      echo "rc=$?" >> "$m.build.out" )
    echo "prerequisite $m: $(tail -1 "$m.build.out")"
    DONE[$m]=1; left=$((left-1)); progress=1
  done
  [ $progress = 1 ] || { echo "prerequisite cycle" >&2; exit 2; }
done

run() { ( ulimit -v $((48*1024*1024)); timeout -k 30 900 "$LEAN" -j1 --tstack=1048576 "$1.lean" > "$1.out" 2>&1
  echo "rc=$?" >> "$1.out" ); }
TESTS=()
for n in $(printf '%s\n' "${!SRC[@]}" | sort); do
  [ -n "${PRE[$n]:-}" ] && continue
  if uses_mathlib "$n.lean"; then echo "$n: SKIPPED (imports Mathlib)"; continue; fi
  TESTS+=("$n")
done
running=0
for n in "${TESTS[@]}"; do
  run "$n" &
  running=$((running+1))
  if [ $running -ge "$JOBS" ]; then wait -n; running=$((running-1)); fi
done
wait

normx() { grep -v '^secs \|^Command exited\|^NT ' "$1" | sed -E 's/\(([0-9]+) ms\)/(N ms)/g; s/\(([0-9]+) ms in total\)/(N ms in total)/g; s/kernel_ms=[0-9]+/kernel_ms=_/; s/total_ms=[0-9]+/total_ms=_/'; }
sel() { if [ "$2" = TypesRepro ]; then normx "$1" | grep -E '^(KERNELIZED|OK|FAIL|rc=)'; else normx "$1"; fi; }
fail=0; same=0; cmp=0
for n in "${TESTS[@]}"; do
  e=${SRC[$n]%.lean}.expected
  rc=$(grep '^rc=' "$n.out" | tail -1)
  if [ -f "$e" ]; then
    cmp=$((cmp+1))
    if diff <(sel "$n.out" "$n") <(sel "$e" "$n") > "$n.exp.diff"; then x=SAME; same=$((same+1)); else x="DIFF ($(grep -c '^[<>]' "$n.exp.diff") lines)"; fail=1; fi
    echo "$n: $rc expected: $x"
  else
    echo "$n: $rc (no expected output)"
  fi
done
echo "compared with expected outputs: $same of $cmp SAME (toolchain $TC; outputs in $OUT)"
exit $fail
