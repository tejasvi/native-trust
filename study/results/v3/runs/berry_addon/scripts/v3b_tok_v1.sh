#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# v3b_tok_v1.sh (v3 BerryEsseen, tokenizer pass): run as ntbuild inside the run's unit. The study driver copy with v2's
# settings (split 64, 40 GB address space and 14,400 s per fact) and the tokenizer add-on built against NativeTrust v15,
# on the string-blocked facts selected from results SEL (berry-esseen = the study's results, FAILED/blocked; any other
# name, e.g. v3u-berry-esseen, is taken whole), minus the 259 parse-once covers (tok_exclude_v1.txt). Resumes: facts
# with a verdict in results/v3b-tok-berry-esseen are skipped unless REDO=1 (then only non-PROVED ones are re-checked).
# usage: [REDO=1] v3b_tok_v1.sh SEL JOBS
SEL=${1:?}; J=${2:?}
B=${NT_BOX}/v3/berry
EX=$(cat $B/tok_exclude_v1.txt)
[ -n "$EX" ] || { echo "empty exclude"; exit 3; }
for m in StrReplace SplitOnSpace StrRepl BeList BeObs BeSplitL; do [ -f $B/lib/$m.olean ] || { echo "missing $m.olean"; exit 3; }; done
case $SEL in berry-esseen) FILT=(--from-verdict FAILED --from-reason blocked);; *) FILT=();; esac
export ELAN_HOME=${NT_BOX}/elan PATH=${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
echo "$(date -u +%FT%TZ) tok start sel=$SEL jobs=$J redo=${REDO:-0}" >> $B/logs/tok.out
python3 -u ${NT_BOX}/v3/m2_axioms5.py v3b-tok-berry-esseen ${NT_BOX}/repos/berry-esseen --skip-build \
  --nt-root ${NT_BOX}/nt_fix14 --extra-import BeSplitL --extra-path $B/lib --split 64 --fact-mem 40 \
  --fact-timeout 14400 --jobs $J ${REDO:+--redo} --from-results $SEL "${FILT[@]}" --exclude "$EX" >> $B/logs/tok.out 2>&1
rc=$?
echo "$(date -u +%FT%TZ) tok end rc=$rc" >> $B/logs/tok.out
exit $rc
