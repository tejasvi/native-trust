#!/bin/bash
# On the box as ntbuild: negctl.sh TC NAME IMPORT DECL -- negative control: leanexport (the toolchain's bin/leanexport)
# of the ORIGINAL declaration DECL (proved by bv_decide with its native axiom) from module IMPORT, then nanoda with
# permitted axioms propext, Classical.choice, Quot.sound and unpermitted_axiom_hard_error. Expected: rejection.
# env XP = LEAN_PATH variable in paths.sh. Output: accept/NAME/ (cmd.txt, decls.export, nanoda.json, nanoda.log).
set -u
TC=$1; NAME=$2; IMP=$3; DECL=$4
W=/home/ntbuild/work_bvscale
source $W/scripts/paths.sh
XPV=${XP:-}; XPATH=${XPV:+${!XPV}}
L=/home/ntbuild/elan/toolchains/leanprover--lean4---$TC
D=$W/accept/$NAME; mkdir -p $D; cd $D || exit 2
export LEAN_PATH=$L/lib/lean${XPATH:+:$XPATH} LEAN_NUM_THREADS=1 PATH=$L/bin:$PATH
echo "$(date -u +%FT%TZ) leanexport $IMP -- $DECL  (toolchain $TC)" > cmd.txt
( ulimit -v 50331648; $L/bin/leanexport $IMP -- $DECL > decls.export 2> export.err ); RC1=$?
echo "export rc=$RC1 bytes=$(stat -c %s decls.export); target in export: $(grep -c "\"${DECL##*.}\"" decls.export) lines; native axiom names in export: $(grep -o '_native[^"]*' decls.export | sort -u | tr '\n' ' ')" | tee -a cmd.txt
cat > nanoda.json <<J
{ "export_file_path": "$D/decls.export", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
  "print_success_message": true, "num_threads": 1 }
J
echo "$(date -u +%FT%TZ) nanoda_bin nanoda.json (v4.35.0 nanoda_bin)" >> cmd.txt
( ulimit -v 50331648; /home/ntbuild/elan/toolchains/leanprover--lean4---v4.35.0/bin/nanoda_bin nanoda.json ) > nanoda.log 2>&1; RC2=$?
echo "nanoda rc=$RC2: $(head -3 nanoda.log | tr '\n' ' ')" | tee -a cmd.txt
