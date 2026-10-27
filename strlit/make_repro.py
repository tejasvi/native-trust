#!/usr/bin/env python3
"""Write Repro.lean (aperiodic 1,000-char literal), ReproControl.lean (periodic literal, same length)
and ReproArray.lean (no strings: a left fold of Array.push over 1,000 aperiodic bytes).
usage: make_repro.py OUTDIR [N]"""
import sys
from pathlib import Path
out = Path(sys.argv[1]); n = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
cnt = ' '.join(str(i) for i in range(n))[:n]          # "0 1 2 3 ... " : aperiodic, only digits and spaces
per = ('613/200 ' * (n // 8 + 1))[:n]                  # period 8, digits '/' and spaces
assert len(cnt) == n and len(per) == n
hdr = '''-- Self-contained (prelude only). Toolchains measured: leanprover/lean4:v4.34.0-rc2 and v4.35.0.
-- Run: lean {f}     (see results.md for the size -> time/memory table)
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
'''
(out / 'Repro.lean').write_text(hdr.format(f='Repro.lean') + f'''
/-- {n} characters, `"0 1 2 3 ..."` truncated: aperiodic, digits and spaces only.
Kernel cost: ~21 s and ~4.6 GB peak at 1,000 chars; x4 time and memory per doubling. -/
def d : String := "{cnt}"

theorem t : d.utf8ByteSize > 0 := by decide +kernel
''')
(out / 'ReproControl.lean').write_text(hdr.format(f='ReproControl.lean') + f'''
/-- Control: {n} characters of `"613/200 "` repeated (period 8, same character classes). Kernel cost ~0.7 s. -/
def d : String := "{per}"

theorem t : d.utf8ByteSize > 0 := by decide +kernel
''')
bs = ', '.join(str(b) for b in cnt.encode())
(out / 'ReproArray.lean').write_text(hdr.format(f='ReproArray.lean') + f'''
/-- No strings: the UTF-8 bytes of Repro.lean's literal, as a `List UInt8`. -/
def bs : List UInt8 := [{bs}]

/-- The same left fold of `Array.push` (= `List.concat`, Init/Prelude.lean) that `List.toByteArray` performs. -/
theorem t : (bs.foldl Array.push #[]).size > 0 := by decide +kernel
''')
print('ok', n)
