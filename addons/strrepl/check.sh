#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# usage (as ntbuild): check.sh TC DIR MODULE THM...   -- export THMs (closure) from MODULE with lean4export, run nanoda + con-ron
# LEAN_PATH must contain the module's olean dir; set EXTRA_LP for package paths.
set -u
TC=${1:?}; DIR=${2:?}; MOD=${3:?}; shift 3
cd "$DIR" || exit 2
case $TC in v4.34.0-rc2) EXP=${NT_BOX}/strrepl/lean4export-v4.34.0-rc2/.lake/build/bin/lean4export;; *) EXP=${NT_BOX}/tools/lean4export-$TC/.lake/build/bin/lean4export;; esac
CHK=${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0/bin
export LEAN_PATH=${NT_BOX}/nt14/$TC/.lake/build/lib/lean:${NT_BOX}/strrepl/$TC:$DIR:${EXTRA_LP:-}
export PATH=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC/bin:$PATH
ulimit -v $((48*1024*1024)); ulimit -s unlimited
timeout 3600 "$EXP" "$MOD" -- "$@" > "$MOD.export" 2> "$MOD.export.err"; echo "export_rc=$? lines=$(wc -l < $MOD.export)"
cat > "$MOD.nanoda.json" <<J
{"export_file_path": "$DIR/$MOD.export", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "print_success_message": true, "num_threads": 1}
J
/usr/bin/time -f "nanoda: %e s %M KB" timeout 3600 $CHK/nanoda_bin "$MOD.nanoda.json" > "$MOD.nanoda.txt" 2>&1; echo "nanoda_rc=$?"; tail -3 "$MOD.nanoda.txt"
/usr/bin/time -f "con-ron: %e s %M KB" timeout 3600 $CHK/con-ron "$MOD.export" > "$MOD.conron.txt" 2>&1; echo "conron_rc=$?"; tail -3 "$MOD.conron.txt"
