#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: ablation of the well-founded replacement. Re-runs the proved facts whose evaluation made copies
# (well-founded definitions reachable) with `wf := false`: no replacement and no fallback, so a fact converts only if
# its evaluation never reduces WellFounded.fix (Lean <= 4.36 compiles it with Lean.opaqueId, which the kernel does
# not unfold). cvc5-logos and Strata: all proved facts; formal-conjectures: only the facts with copies.
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV3.log
python3 -I ${NT_BOX}/wf_facts.py ${NT_BOX}/work/formal-conjectures-fuel > ${NT_BOX}/fc_wf_facts.txt 2>> $log
re="^($(sed -e 's/[.[\]*+?(){}|^$\\]/\\&/g' ${NT_BOX}/fc_wf_facts.txt | paste -sd'|'))$"
for spec in "cvc5-logos-nowf|${NT_BOX}/repos/cvc5-logos|cvc5-logos-fuel" "strata-nowf|${NT_BOX}/repos/Strata|strata-fuel" "formal-conjectures-nowf|${NT_BOX}/repos/formal-conjectures|formal-conjectures-fuel"; do
  IFS='|' read -r name pkg from <<< "$spec"
  inc=()
  [ "$name" = formal-conjectures-nowf ] && inc=(--include "$re")
  echo "$(date -u +%FT%TZ) start $name" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --from-results "$from" --from-verdict PROVED "${inc[@]}" --extra-config 'wf := false' --jobs 16 > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
done
