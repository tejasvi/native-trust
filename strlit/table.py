#!/usr/bin/env python3
"""usage: table.py RESULTS_DIR  -- merge results/*.tsv (run.sh summaries) with results/dsub.tsv into markdown rows.
Columns: test, toolchain, chars, UTF-8 bytes, distinct byte substrings D, time s, peak RSS GB (KB/1e6), (RSS - base)/D KB, rc.
Also prints a least-squares fit peak - base = alpha*bytes + beta*D over the utf8ByteSize/decide+kernel runs."""
import re, sys
from pathlib import Path
R = Path(sys.argv[1])
BASE_KB = 472744   # trivial run: 2,000-char literal compared by `rfl` (m2 dw_2000_eqv_trfl, v4.34.0-rc2)
D = {}
for line in (R / 'dsub.tsv').read_text().splitlines():
    k, b, d = line.split('\t'); D[k] = (int(b.split('=')[1]), int(d.split('=')[1]))
rows = []
for f in sorted(R.glob('*.tsv')):
    if f.name == 'dsub.tsv': continue
    tc = None
    for line in f.read_text().splitlines():
        m = re.match(r'## summary\.(.*?)\.tsv', line)
        if m: tc = m.group(1); continue
        p = line.split('\t')
        if len(p) < 3: continue
        name, tm, rc = p[0], p[1], p[2]
        mm = re.match(r'TIME ([\d.]+) s (\d+) KB', tm)
        secs, kb = (float(mm.group(1)), int(mm.group(2))) if mm else (None, None)
        alias = {'Repro': 'cnt_1000_ubs_dk', 'ReproControl': 'rep8_1000_ubs_dk', 'ReproArray': 'cnt_1000_u8push_dk',
                 'Repro_nomrd': 'cnt_1000_ubs_dk_nomrd', 'Repro_mrd': 'cnt_1000_ubs_dk'}
        name = alias.get(name, name)
        suffix = ''
        if name.endswith('_nomrd'): name, suffix = name[:-6], '(no maxRecDepth)'
        parts = name.split('_')
        # name = kind_N_op_method (kind may contain '_' only for B- blocks)
        method, op, n = parts[-1] + suffix, parts[-2], parts[-3]; kind = '_'.join(parts[:-3])
        key = f'{kind}_{n}'
        b, d = D.get(key, (None, None))
        per = (kb - BASE_KB) / d if (kb and d) else None
        rows.append((f.stem, tc, kind, n, op, method, b, d, secs, kb, per, rc))
print('| batch | toolchain | content | chars | op | method | bytes | D | time s | peak GB | (peak-base)/D KB | rc |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|')
for (bt, tc, kind, n, op, method, b, d, secs, kb, per, rc) in rows:
    f = lambda v, fmt='{}': '' if v is None else fmt.format(v)
    print(f'| {bt} | {tc} | {kind} | {n} | {op} | {method} | {f(b)} | {f(d)} | {f(secs)} | '
          f'{f(kb / 1e6 if kb else None, "{:.2f}")} | {f(per, "{:.1f}")} | {rc} |')

fit = [(b, d, kb - BASE_KB) for (bt, tc, kind, n, op, method, b, d, secs, kb, per, rc) in rows
       if op == 'ubs' and method == 'dk' and kb and d and rc == 'rc=0']
sxx = sum(b*b for b, d, y in fit); sxy = sum(b*d for b, d, y in fit); syy = sum(d*d for b, d, y in fit)
sxz = sum(b*y for b, d, y in fit); syz = sum(d*y for b, d, y in fit)
det = sxx*syy - sxy*sxy
alpha = (sxz*syy - syz*sxy) / det; beta = (sxx*syz - sxy*sxz) / det
print()
print(f'fit over {len(fit)} runs (utf8ByteSize, decide +kernel, rc=0): peak_KB - {BASE_KB} = {alpha:.1f} KB * bytes + {beta:.2f} KB * D')
worst = max(fit, key=lambda t: abs(alpha*t[0] + beta*t[1] - t[2]) / (t[2] + BASE_KB))
print(f'max |predicted - measured| / measured = {abs(alpha*worst[0] + beta*worst[1] - worst[2]) / (worst[2] + BASE_KB):.3f}')
for b, d, y in sorted(fit, key=lambda t: t[1]):
    pred = alpha*b + beta*d
    print(f'  bytes={b:6d} D={d:8d} measured={(y+BASE_KB)/1e6:6.2f} GB predicted={(pred+BASE_KB)/1e6:6.2f} GB')
