#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# task 3: export + nanoda for an existing supplement module Supp_<TAG> (supp_build_v1.sh's step 3, fixed: the
# toolchain's bin directory first on PATH, since leanexport runs `lean` from PATH and the elan proxy has no default
# toolchain; an empty export is a failure and nanoda is not run on it). Runs as ntbuild in a systemd unit (MemoryMax).
# usage: supp_export_v1.sh TAG THEOREM
set -u
TAG=${1:?}; T=${2:?}
Q=${NT_BOX}/work_resv8/qec; S=$Q/supp; D=$Q/drv/qec/mods
B=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
export ELAN_HOME=${NT_BOX}/elan PATH=$B:${NT_BOX}/elan/bin:$PATH LEAN_NUM_THREADS=1
cd "$S" || exit 2
LP=$(cd "$Q/lean4" && lake env printenv LEAN_PATH) || exit 2
export LEAN_PATH=${NT_BOX}/nt_fix14/v4.35.0-rc3/.lake/build/lib/lean:$LP:$D:$S
F=Supp_$TAG; L=$S/$F.summary
[ -s "$F.olean" ] || { echo "no $F.olean" >> "$L"; exit 2; }
/usr/bin/time -f "leanexport: %e s wall %U s user %M KB" "$B/leanexport" "$F" -- "$T.kernel" > "$F.export" 2> "$F.export.err"
rc=$?; n=$(wc -l < "$F.export")
echo "$(date -u +%FT%TZ) leanexport(v1 export script) rc=$rc lines=$n bytes=$(wc -c < "$F.export") $(tail -n 1 "$F.export.err")" >> "$L"
if [ "$rc" != 0 ] || [ "$n" = 0 ]; then echo "EMPTY OR FAILED EXPORT: nanoda not run (counts as a failure)" >> "$L"; exit 1; fi
printf '{"export_file_path":"%s/%s.export","permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"print_success_message":true}\n' "$S" "$F" > "$F.nanoda.json"
( ulimit -s unlimited; /usr/bin/time -f "nanoda: %e s wall %U s user %M KB" timeout 7200 "$B/nanoda_bin" "$F.nanoda.json" ) > "$F.nanoda.log" 2>&1
echo "$(date -u +%FT%TZ) nanoda rc=$? $(tail -n 4 "$F.nanoda.log" | tr '\n' ' ')" >> "$L"
