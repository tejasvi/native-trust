NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# source me: package LEAN_PATHs on the box
CLEAN=${NT_BOX}/repos/clean
CLEAN_PATH=$CLEAN/.lake/packages/Cli/.lake/build/lib/lean:$CLEAN/.lake/packages/batteries/.lake/build/lib/lean:$CLEAN/.lake/packages/Qq/.lake/build/lib/lean:$CLEAN/.lake/packages/aesop/.lake/build/lib/lean:$CLEAN/.lake/packages/proofwidgets/.lake/build/lib/lean:$CLEAN/.lake/packages/importGraph/.lake/build/lib/lean:$CLEAN/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$CLEAN/.lake/packages/plausible/.lake/build/lib/lean:$CLEAN/.lake/packages/mathlib/.lake/build/lib/lean:$CLEAN/.lake/packages/CompPoly/.lake/build/lib/lean:$CLEAN/.lake/build/lib/lean
ASI_PATH=${NT_BOX}/repos/asi-stack-book/lean/.lake/build/lib/lean
# veir (s_opencompl_veir, toolchain v4.35.0-rc4), from work_bvsweep/scripts/pkgs.tsv
VEIR=${NT_BOX}/repos_s/opencompl_veir
VEIR_PATH=$VEIR/.lake/packages/Coinductive/.lake/build/lib/lean:$VEIR/lean-ctrees/.lake/build/lib/lean:$VEIR/ExArray/.lake/build/lib/lean:$VEIR/.lake/build/lib/lean
# Natuvea tacenta-core (model + proofs packages, toolchain v4.31.0), from work_bvsweep/scripts/pkgs.tsv
NATUVEA=${NT_BOX}/repos_s/Natuvea_tacenta-core
NATUVEA_PATH=$NATUVEA/tacenta-model/.lake/build/lib/lean:$NATUVEA/tacenta-proofs/.lake/build/lib/lean
