#!/usr/bin/env python3
"""build_manifests.py: recompute the source manifest of every library build of the final run (final_run_builds.tsv) from the
library at the top of the artifact. A build is that library with its own toolchain file (leanprover/lean4:<toolchain>) and, on
Lean 4.27-4.29, with NativeTrust/CSimpCompatStub.lean.txt and NativeTrust/StrLibStub.lean.txt in place of
NativeTrust/CSimpCompat.lean and NativeTrust/StrLib.lean, as study/builds/nt_fix14_build_one.sh and v3_build_one_v1.sh build it.
The manifest is defined as in README.md here. Prints one line per build (toolchain, recorded manifest, same or DIFFERENT) and a
count.
usage (from the artifact's top directory):
  python3 -I -B study/library_versions/build_manifests.py study/library_versions/final_run_builds.tsv
"""
import hashlib
import sys
from pathlib import Path

lib = {p.as_posix(): p.read_bytes() for p in sorted(Path('NativeTrust').rglob('*.lean'))}
lib.update({n: Path(n).read_bytes() for n in ('NativeTrust.lean', 'lakefile.toml')})
stubs = {'NativeTrust/CSimpCompat.lean': Path('NativeTrust/CSimpCompatStub.lean.txt').read_bytes(),
         'NativeTrust/StrLib.lean': Path('NativeTrust/StrLibStub.lean.txt').read_bytes()}


def manifest(tc):
    fs = dict(lib)
    if tc.startswith(('v4.27', 'v4.28', 'v4.29')):
        fs.update(stubs)
    fs['lean-toolchain'] = f'leanprover/lean4:{tc}\n'.encode()
    return hashlib.sha256(''.join(f'{hashlib.sha256(b).hexdigest()}  {n}\n' for n, b in sorted(fs.items())).encode()).hexdigest()


rows = [l.split('\t') for l in Path(sys.argv[1]).read_text().splitlines()[1:] if l.strip()]
same = 0
for tc, folder, recorded, _ in rows:
    ok = manifest(tc) == recorded
    same += ok
    print(f"{tc}\t{recorded[:8]}\t{'same' if ok else 'DIFFERENT'}")
print(f'{same} of {len(rows)} manifests recomputed')
