#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_main_v1.sh (v3 BerryEsseen on the clone): run as ntbuild inside the run's unit (MemoryMax 700G). Runs the tokenizer
# pass (v3b_tok_v1.sh, JOBS facts at a time) and the covers scheduler (v3b_sched_v1.sh, at most MAXP processes, memory
# budget BUDGET0 GiB while the tokenizer pass runs) together; when the tokenizer pass ends, the budget is raised to
# BUDGET1 GiB.
# usage: [REDO=1] v3b_main_v1.sh SEL JOBS MAXP BUDGET0 BUDGET1
SEL=${1:?}; J=${2:?}; MAXP=${3:?}; B0=${4:?}; B1=${5:?}
B=${NT_BOX}/v3/berry; BIN=$B/bin
echo "$B0" > $B/budget_gb
echo "$(date -u +%FT%TZ) main start sel=$SEL jobs=$J maxp=$MAXP budget=$B0/$B1" >> $B/logs/main.log
bash $BIN/v3b_tok_v1.sh "$SEL" "$J" & TP=$!
bash $BIN/v3b_sched_v1.sh $B/covers_v1.txt $B/budget_gb "$MAXP" & SP=$!
wait $TP; trc=$?
echo "$B1" > $B/budget_gb
echo "$(date -u +%FT%TZ) tokenizer pass ended rc=$trc; covers budget raised to $B1" >> $B/logs/main.log
wait $SP; src=$?
echo "$(date -u +%FT%TZ) main end tok_rc=$trc sched_rc=$src" >> $B/logs/main.log
