#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: the 13 cast facts on library v9 (build nt_fix8) WITHOUT the AsiCasts/FcCasts add-ons:
# every last-verdict FAILED fact of asi-stack-book and formal-conjectures-nt18, results v9c-<pkg>.
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV9c.log
run() { # name pkg baseline
  echo "$(date -u +%FT%TZ) start $1" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$1" "$2" --skip-build --nt-root ${NT_BOX}/nt_fix8 --jobs 4 \
    --from-results "$3" --from-verdict FAILED > ${NT_BOX}/m2_$1.ax5.out 2>&1
  rc=$?
  echo "$(date -u +%FT%TZ) end $1 rc=$rc $(tail -1 ${NT_BOX}/m2_$1.ax5.out)" >> $log
}
run v9c-asi-stack-book ${NT_BOX}/repos/asi-stack-book/lean asi-stack-book
run v9c-formal-conjectures ${NT_BOX}/repos/formal-conjectures formal-conjectures-nt18
echo "$(date -u +%FT%TZ) ALL DONE" >> $log
