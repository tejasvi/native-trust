#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_smoke_v1.sh (v3 BerryEsseen on the clone): run as ntbuild inside a scope. Smoke test of both passes on one small item
# each, with the real run names (so the main run skips what finishes here): the covers scheduler on cover D8 alone, and the
# tokenizer pass on Covers.Data.BE3 alone.
B=${NT_BOX}/v3/berry
[ -e $B/covers_smoke.txt ] && { echo "refusing: smoke files exist"; exit 3; }
command grep '^D8 ' $B/covers_v1.txt > $B/covers_smoke.txt
echo 60 > $B/budget_smoke
bash $B/bin/v3b_sched_v1.sh $B/covers_smoke.txt $B/budget_smoke 8 & SP=$!
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
python3 -u ${NT_BOX}/v3/m2_axioms5.py v3b-tok-berry-esseen ${NT_BOX}/repos/berry-esseen --skip-build \
  --nt-root ${NT_BOX}/nt_fix14 --extra-import BeSplitL --extra-path $B/lib --split 64 --fact-mem 40 \
  --fact-timeout 14400 --jobs 1 --from-results berry-esseen --from-verdict FAILED --from-reason blocked \
  --include '\.Covers\.Data\.BE3\.' > $B/logs/tok_smoke.out 2>&1
echo "tok smoke rc=$?"
wait $SP; echo "sched smoke rc=$?"
