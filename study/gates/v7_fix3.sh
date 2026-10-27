#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: test NativeTrust with the retry design (proof transport and skipUnchanged only in a retry of the fuel route
# after the first attempt fails; builds in $NT_BOX/nt_fix3/<tc>, sources = local NativeTrust): Strata, the 15
# formal-conjectures facts that run well-founded recursion with accFallback := false, Zag, cvc5/logos, and
# formal-conjectures in full.
cd ${NT_BOX} || exit 1
log=${NT_BOX}/laneV7.log
re="^($(sed -e 's/[.[\]*+?(){}|^$\\]/\\&/g' ${NT_BOX}/fc_fallback.txt | paste -sd'|'))$"
run() { # name pkg extra...
  local name=$1 pkg=$2; shift 2
  echo "$(date -u +%FT%TZ) start $name $*" >> $log
  python3 -u ${NT_BOX}/m2_axioms5.py "$name" "$pkg" --skip-build --nt-root ${NT_BOX}/nt_fix3 --jobs 16 "$@" > ${NT_BOX}/m2_$name.ax5.out 2>&1
  echo "$(date -u +%FT%TZ) end $name rc=$? $(tail -1 ${NT_BOX}/m2_$name.ax5.out)" >> $log
}
run strata-nt18 ${NT_BOX}/repos/Strata
run fc15-nt18 ${NT_BOX}/repos/formal-conjectures --from-results formal-conjectures-fuel --from-verdict PROVED --include "$re" --extra-config 'accFallback := false'
run nt18-zag ${NT_BOX}/repos_s/FrederickPu_Zag

run cvc5-logos-nt18 ${NT_BOX}/repos/cvc5-logos
run formal-conjectures-nt18 ${NT_BOX}/repos/formal-conjectures
