#!/bin/bash
NT_BOX=${NT_BOX:-/home/ntbuild}  # box root used in the study; set NT_BOX to run elsewhere
# run as ntbuild: shallow-clone the sampled repositories into $NT_BOX/repos_s and classify them by toolchain
# (one package directory per lean-toolchain file next to a lakefile; NativeTrust needs Lean >= 4.27)
mkdir -p ${NT_BOX}/repos_s && cd ${NT_BOX}/repos_s
while read -r repo; do
  [ -n "$repo" ] || continue
  d=$(echo "$repo" | tr '/' '__')
  [ -d "$d" ] || timeout 180 git clone -q --depth 1 "https://github.com/$repo.git" "$d" > /dev/null 2>&1 || { echo -e "$repo\t-\tCLONE_FAIL"; continue; }
  found=0
  while read -r tcf; do
    p=$(dirname "$tcf")
    [ -f "$p/lakefile.toml" ] || [ -f "$p/lakefile.lean" ] || continue
    n=$(grep -rlE --include=*.lean --exclude-dir=.lake "native_decide|decide *\+native" "$p" 2>/dev/null | wc -l)
    [ "$n" -gt 0 ] || continue
    echo -e "$repo\t$p\t$(cat "$tcf" | tr -d '\n')\t$n"; found=1
  done < <(find "$d" -maxdepth 4 -name lean-toolchain -not -path '*/.lake/*' 2>/dev/null)
  [ $found = 1 ] || echo -e "$repo\t-\tNO_PACKAGE"
done < "$1"
