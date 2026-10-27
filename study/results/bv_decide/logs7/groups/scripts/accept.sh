#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# On the box as ntbuild: accept.sh TC NAME IMPORT ORIGMOD "FACTS" "NEW:ORIG ..." [NANODA_DECL ...]
#   IMPORT: the module with the converted declarations (olean in $BV_BUILD/TC); ORIGMOD: the original module.
#   1. A fresh lean process imports both: #print axioms of every fact theorem, every rebuilt declaration and its
#      original; TYPE_IDENTICAL: syntactic equality of the kernel types of rebuilt and original declaration.
#   2. With NANODA_DECLs: leanexport (the toolchain's bin/leanexport, else tools/lean4export-TC) of these declarations,
#      then nanoda (v4.35.0 nanoda_bin; permitted axioms propext, Classical.choice, Quot.sound). PASS needs rc 0 of
#      both, a non-empty export that contains every target name, and a positive declaration count.
# env: XP = name of a LEAN_PATH variable in paths.sh (package), BV_BUILD (default build8). Output in accept/NAME/.
# FACTS = @LOG / PAIRS = @LOG: take the fact theorems (BVS_UNSAT lines) / the NEW:ORIG pairs (BVS_USER lines) from a
# driver log. Original names may be private (numeric components are parsed); only rebuilt declarations and facts get
# #print axioms (private originals are not printable by name).
set -u
TC=$1; NAME=$2; IMP=$3; ORIG=$4; FACTS=$5; PAIRS=$6; shift 6
case $FACTS in @*) FACTS=$(awk -F'\t' '$1=="BVS_UNSAT" {print $9}' ${FACTS#@} | tr '\n' ' ');; esac
case $PAIRS in @*) PAIRS=$(awk -F'\t' '$1=="BVS_USER" {print $3":"$2}' ${PAIRS#@} | tr '\n' ' ');; esac
W=${NT_BOX}/work_bvscale
source $W/scripts/paths.sh
XPV=${XP:-}; XPATH=${XPV:+${!XPV}}
L=${NT_BOX}/elan/toolchains/leanprover--lean4---$TC
D=$W/accept/$NAME; mkdir -p $D; cd $D || exit 2
export LEAN_PATH=$W/${BV_BUILD:-build8}/$TC:$L/lib/lean${XPATH:+:$XPATH}
export LEAN_NUM_THREADS=1 PATH=$L/bin:$PATH
{
  echo "import $IMP"; echo "import $ORIG"
  for f in $FACTS; do echo "#print axioms $f"; done
  for p in $PAIRS; do echo "#print axioms ${p%%:*}"; done
  echo "open Lean in"
  echo "def parseN (s : String) : Name := (s.splitOn \".\").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous"
  echo "open Lean in"
  echo "#eval show MetaM Unit from do"
  for p in $PAIRS; do
    echo "  IO.println s!\"TYPE_IDENTICAL ${p%%:*} ${p#*:} {(← getConstInfo (parseN \"${p%%:*}\")).type == (← getConstInfo (parseN \"${p#*:}\")).type}\""
  done
  echo "  pure ()"
} > Ax.lean
( ulimit -v 50331648; /usr/bin/time -f "ax: wall=%e s maxrss=%M KB" timeout 3600 $L/bin/lean -j1 Ax.lean ) > ax.log 2>&1
echo "axioms rc=$? $(date -u +%T)"
grep -E "depends on|does not depend|TYPE_IDENTICAL|error|ax:" ax.log | cut -c1-300
if [ $# -gt 0 ]; then
  EXPORTER=$L/bin/leanexport
  [ -x $EXPORTER ] || EXPORTER=${NT_BOX}/tools/lean4export-$TC/.lake/build/bin/lean4export
  echo "exporter: $EXPORTER"
  ( ulimit -v 100663296; /usr/bin/time -f "export: wall=%e s maxrss=%M KB" timeout 7200 $EXPORTER $IMP -- "$@" > decls.export 2> export.err ); RC1=$?
  SZ=$(stat -c %s decls.export)
  echo "export rc=$RC1 bytes=$SZ $(tail -1 export.err) $(date -u +%T)"
  PRESENT=1
  for d in "$@"; do
    first=${d%%.*}; last=${d##*.}
    grep -q "\"$first\"" decls.export && grep -q "\"$last\"" decls.export || { PRESENT=0; echo "target $d not found in the export"; }
  done
  cat > nanoda.json <<J
{ "export_file_path": "$D/decls.export", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true,
  "print_success_message": true, "num_threads": 1 }
J
  ( ulimit -v 100663296; ulimit -s unlimited; /usr/bin/time -f "nanoda: wall=%e s maxrss=%M KB" timeout 14400 ${NT_BOX}/elan/toolchains/leanprover--lean4---v4.35.0/bin/nanoda_bin nanoda.json ) > nanoda.log 2>&1; RC2=$?
  N=$(grep -oE 'Checked [0-9]+ declarations' nanoda.log | grep -oE '[0-9]+' | head -1)
  if [ $RC1 = 0 ] && [ $RC2 = 0 ] && [ "$SZ" -gt 0 ] && [ $PRESENT = 1 ] && [ "${N:-0}" -gt 0 ]; then V=PASS; else V=FAIL; fi
  echo "nanoda $V rc=$RC2 decls=${N:-0} $(date -u +%T): $(grep -E 'Checked|rror|unpermitted|nanoda:' nanoda.log | head -4 | tr '\n' ' ' | cut -c1-600)"
fi
