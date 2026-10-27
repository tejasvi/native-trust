#!/usr/bin/env python3
"""Generate self-contained test files (no imports) for string-literal kernel cost.
usage: gen.py OUTDIR SPEC [SPEC ...]      SPEC = content:N:op:method
content: dw (prefix of DW21 data), rep8 ("613/200 " repeated), cnt ("0 1 2 3 ..." truncated), B-<block> (<block> repeated, '_' = space, '~' = '/'), a ('a'*N), sp (' '*N), nl ('\\n'*N),
         rnd (seeded random over DW21's 14-char alphabet), dig (random digits), bin (random 0/1),
         punct (random punctuation), na2 (random 2-byte chars), na3 (random 3-byte), na4 (random 4-byte),
         perP (random block of length P over the DW21 alphabet, repeated; e.g. per64)
op: ubs (utf8ByteSize > 0), len (length > 0), tol (toList.length > 0), eq (d == d2, d2 a separate
    identical literal), eqv (decide (d = d2)), dd (decide (d = d)), ubsN (utf8ByteSize = exact value)
mechanism ops (no string literal; d is replaced by an explicit list): sofl ((String.ofList l).utf8ByteSize > 0),
    fmlen ((l.flatMap String.utf8EncodeChar).length > 0), fmtba ((l.flatMap String.utf8EncodeChar).toByteArray.size > 0),
    u8tba (bs.toByteArray.size > 0 for bs : List UInt8 = the UTF-8 bytes), u8arr ((bs.toArray).size > 0, List.toArray),
    u8push (bs.foldl Array.push #[] |>.size > 0)
method: dk (decide +kernel), rfl (theorem ... := by rfl), trfl (term-mode rfl),
        nde (Nat.decEq-style: (Nat.decEq lhs rhs).decide = true, by decide +kernel)
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import sys, re, random
from pathlib import Path
DW21 = Path((NT_BOX + '/repos/berry-esseen/BerryEsseen/Upper0423/Covers/Data/DW21.lean'))
ALPHA = ' 0123456789/FS'

def dw_data():
    s = DW21.read_text(encoding='utf-8')
    i = s.index('def data'); j = s.index('"', i); k = s.index('"', j + 1)
    d = s[j + 1:k]
    assert '\\' not in d
    return d

def content(kind, n):
    r = random.Random(12345)
    if kind == 'dw':
        d = dw_data(); assert n <= len(d), (n, len(d)); return d[:n]
    if kind == 'rep8': return ('613/200 ' * (n // 8 + 1))[:n]
    if kind == 'cnt': return ' '.join(str(i) for i in range(n))[:n]
    if kind.startswith('B-'):
        blk = kind[2:].replace('_', ' ').replace('~', '/'); return (blk * (n // len(blk) + 1))[:n]
    if kind == 'a': return 'a' * n
    if kind == 'sp': return ' ' * n
    if kind == 'nl': return '\n' * n
    if kind == 'rnd': return ''.join(r.choice(ALPHA) for _ in range(n))
    if kind == 'dig': return ''.join(r.choice('0123456789') for _ in range(n))
    if kind == 'bin': return ''.join(r.choice('01') for _ in range(n))
    if kind == 'punct': return ''.join(r.choice('!#$%&()*+,-./:;<=>?@[]^_{|}~') for _ in range(n))
    if kind == 'na2': return ''.join(r.choice('αβγδεζηθλμπσφω') for _ in range(n))
    if kind == 'na3': return ''.join(r.choice('∀∃∧∨¬→←≤≥≠∈∉⊆∅') for _ in range(n))
    if kind == 'na4': return ''.join(r.choice('😀😁😂😃😄😅😆😇😈😉') for _ in range(n))
    m = re.fullmatch(r'per(\d+)', kind)
    if m:
        p = int(m.group(1)); blk = ''.join(r.choice(ALPHA) for _ in range(p))
        return (blk * (n // p + 1))[:n]
    raise SystemExit('unknown content ' + kind)

def lit(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'

def chlit(c):
    return {'\\': "'\\\\'", "'": "'\\''", '\n': "'\\n'"}.get(c, "'" + c + "'")

def stmt(op, d):
    nb = len(d.encode('utf-8'))
    return {
        'ubs': ('d.utf8ByteSize > 0', None),
        'ubsN': (f'd.utf8ByteSize = {nb}', None),
        'len': ('d.length > 0', None),
        'tol': ('d.toList.length > 0', None),
        'eq': ('(d == d2) = true', None),
        'eqv': ('d = d2', None),
        'dd': ('d = d', None),
        'sofl': ('(String.ofList l).utf8ByteSize > 0', None),
        'fmlen': ('(l.flatMap String.utf8EncodeChar).length > 0', None),
        'fmtba': ('(l.flatMap String.utf8EncodeChar).toByteArray.size > 0', None),
        'u8tba': ('bs.toByteArray.size > 0', None),
        'u8arr': ('bs.toArray.size > 0', None),
        'u8push': ('(bs.foldl Array.push #[]).size > 0', None),
    }[op][0]

def body(op, method, d):
    p = stmt(op, d)
    if method == 'dk': return f'theorem t : {p} := by decide +kernel\n'
    if method == 'rfl': return f'theorem t : {p} := by rfl\n'
    if method == 'trfl': return f'theorem t : {p} := rfl\n'
    if method == 'nde':
        m = re.fullmatch(r'(.*) = (.*)', p); assert m, p
        return f'theorem t : (Nat.decEq ({m.group(1)}) ({m.group(2)})).decide = true := by decide +kernel\n'
    raise SystemExit('unknown method ' + method)

out = Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)
for spec in sys.argv[2:]:
    kind, n, op, method = spec.split(':'); n = int(n)
    d = content(kind, n)
    hdr = '-- self-contained: no imports beyond the prelude\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
    defs = f'def d : String := {lit(d)}\n'
    if op in ('eq', 'eqv'): defs += f'def d2 : String := {lit(d)}\n'
    if op in ('sofl', 'fmlen', 'fmtba'):
        defs = 'def l : List Char := [' + ', '.join(chlit(c) for c in d) + ']\n'
    if op in ('u8tba', 'u8arr', 'u8push'):
        defs = 'def bs : List UInt8 := [' + ', '.join(str(b) for b in d.encode('utf-8')) + ']\n'
    name = f'{kind}_{n}_{op}_{method}'
    (out / f'{name}.lean').write_text(hdr + defs + body(op, method, d), encoding='utf-8')
    print(name, len(d), len(d.encode('utf-8')))
