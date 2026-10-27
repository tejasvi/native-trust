#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild on the box): run.sh TC DIR [NAME ...]  -- run lean on DIR/NAME.lean (default: all) with
# ulimit -v 24 GB, timeout 300 s, at most 4 at once; writes DIR/NAME.TC.log (lean output + time/mem + rc)
set -u
TC=${1:?}; DIR=${2:?}; shift 2
LEAN=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin/lean
[ -x "$LEAN" ] || { echo "no lean $LEAN"; exit 2; }
case "$DIR" in ${NT_BOX}/strlit/*) ;; *) echo "DIR must be under ${NT_BOX}/strlit"; exit 2;; esac
cd "$DIR" || exit 2
if [ $# -eq 0 ]; then set -- $(ls *.lean | sed 's/\.lean$//'); fi
export LEAN LIMIT_TO=${TO:-300} TC
one() {
  B=$1
  ( ulimit -v $((24*1024*1024)); ulimit -s unlimited
    export LEAN_NUM_THREADS=1
    /usr/bin/time -f "TIME %e s %M KB" timeout -k 10 $LIMIT_TO "$LEAN" -j1 --tstack=1048576 "$B.lean" > "$B.$TC.log" 2>&1
    echo "rc=$?" >> "$B.$TC.log" )
  printf '%s\t%s\t%s\n' "$B" "$(grep -o 'TIME.*' "$B.$TC.log" | tail -1)" "$(tail -1 "$B.$TC.log")"
}
export -f one
printf '%s\n' "$@" | xargs -P 4 -I{} bash -c 'one {}'
