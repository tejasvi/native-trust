#!/usr/bin/env python3
"""Generate the BerryEsseen test modules from pick10.tsv (run as ntbuild on the box).

be10/RC.lean     : the prescribed test: NativeTrust + StrRepl + the 10 data modules,
                   `prove_native_axiom_nth M i (config := { split := 8 })` for each fact.
be10d/D<k>.lean  : diagnostic, one module per fact: the same acceptance check with `tokens`
                   replaced by `tokensNR` (no `String.replace "\n" " "` step), conjoined with a
                   kernel check that the data string contains no '\n'; proved by `kdecide`.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import re
from pathlib import Path
D = Path((NT_BOX + '/strrepl/v4.34.0-rc2'))
rows = [l.split('\t') for l in (Path((NT_BOX + '/strrepl/pick10.tsv'))).read_text().splitlines() if l.strip()]
hdr = 'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
(D / 'be10').mkdir(exist_ok=True)
(D / 'be10' / 'RC.lean').write_text('import NativeTrust\nimport StrRepl\n' + ''.join(f'import {m}\n' for m, *_ in rows) + hdr +
    ''.join(f'prove_native_axiom_nth {m} {i} (config := {{ split := 8 }})\n' for m, i, *_ in rows))
(D / 'be10d').mkdir(exist_ok=True)
pre = '''open BerryEsseen.Upper0423.Native

/-- `tokens` without its `String.replace "\\n" " "` step (diagnostic only). -/
def tokensNR (s : String) : List String := (s.splitOn " ").filter fun t => !t.isEmpty

def accBE (n : Nat) (blo bhi : Rat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAcceptedBE n blo bhi 0 1 cov
  | _ => false

def accDW (n : Nat) (dlo dhi : Rat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAccepted n dlo dhi 0 1 cov
  | _ => false

def acc0 (n : Nat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAccepted n 0 deltaMax 0 1 cov
  | _ => false

'''
for k, (m, i, ax, st) in enumerate(rows):
    mm = re.search(r'theorem accepted : (coverStringAccepted(BE|DW)?) (.*) data = true', st)
    fn = {'coverStringAcceptedBE': 'accBE', 'coverStringAcceptedDW': 'accDW', 'coverStringAccepted': 'acc0'}[mm.group(1)]
    args = mm.group(3)
    body = (f'theorem diag_{k} : ({fn} {args} {m}.data && !({m}.data.toList.contains \'\\n\')) = true := by\n'
            f'  kdecide (config := {{ native := false }})\n\n#print axioms diag_{k}\n')
    (D / 'be10d' / f'D{k}.lean').write_text(f'import NativeTrust\nimport StrRepl\nimport {m}\n' + hdr + pre + body)
print('ok', len(rows))
