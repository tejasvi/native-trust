#!/usr/bin/env python3
"""Profile pieces of the kernel evaluation on one data string (run as ntbuild). usage: gen_prof.py MODULE"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import sys
from pathlib import Path
m = sys.argv[1]
D = Path((NT_BOX + '/strrepl/v4.34.0-rc2/prof')); D.mkdir(exist_ok=True)
hdr = f'import NativeTrust\nimport StrRepl\nimport {m}\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nopen BerryEsseen.Upper0423.Native\n'
defs = '''def tokensNR (s : String) : List String := (s.splitOn " ").filter fun t => !t.isEmpty
'''
pieces = {
  'P1': f'theorem p1 : ({m}.data.toList.length > 0) = true := by kdecide (config := {{ native := false, trace := true }})',
  'P2': f'theorem p2 : ((tokensNR {m}.data).length > 0) = true := by kdecide (config := {{ native := false, trace := true }})',
  'P3': f'theorem p3 : ((parseCover 64 (tokensNR {m}.data)).isSome) = true := by kdecide (config := {{ native := false, trace := true }})',
  'P0': f'theorem p0 : ({m}.data.utf8ByteSize > 0) = true := by kdecide (config := {{ native := false, trace := true }})',
}
for k, v in pieces.items():
    (D / f'{k}.lean').write_text(hdr + defs + v + '\n')
print('ok')
