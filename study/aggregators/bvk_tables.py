#!/usr/bin/env python3
"""The tables of the tactic bv_kdecide in addons/bvs/README.md ("The tactic `bv_kdecide`"), from the runs in study/results/bv_decide/tactic/.

usage: python3 -I -B study/aggregators/bvk_tables.py      (from the artifact's top directory)

Sources (under study/results/bv_decide/tactic/):
  real_facts_final.tsv   one row per bv_kdecide call that made a SAT call, i.e. per native bv_decide axiom of the
                         original modules (195 facts of veir, clean, Natuvea and asi-stack-book): times in ms, peak memory
                         in MiB of the bv_decide phase and of the kernel route, CNF size, certificate size
  real_facts_final.md    the module runs (one process per module copy) and the summary made from the same records
  evidence/bench_v1, evidence/bench_v2   single facts, one lean process each: results*.tsv (file, exit status, wall
                         seconds, peak memory in KiB) and the bv_kdecide statistics line of each log
Statistics as in the summary: median = statistics.median, 90th percentile = sorted values at index int(0.9 * (n - 1)),
memory of a call = the larger of its two peaks. The estimate of bvs5_estimate is 0.064 * clauses ^ 1.355 ms
(addons/bvs/BVS/Estimate.lean).
"""
import csv
import math
import re
import statistics as S
from pathlib import Path

T = Path('study/results/bv_decide/tactic')
rows = list(csv.DictReader(open(T / 'real_facts_final.tsv'), delimiter='\t'))
num = lambda r, c: int(r[c]) if r[c] not in ('', '-') else 0


def sec(ms, big=100):
    s = ms / 1000
    return f'{s:,.0f} s' if s >= big else f'{s:.1f} s'


def p90(v):
    v = sorted(v)
    return v[int(0.9 * (len(v) - 1))]


# ---- single facts (the 10-goal table)
GOALS = [('ex_mul_three', '`x * 3 = x + x + x`, 16 bits'), ('ex_cpop_not', '`(~~~x).cpop + x.cpop = 16#16`, 16 bits'),
         ('mul3_w128', '`x * 3 = x + x + x`, 128 bits'), ('mul3_w256', '`x * 3 = x + x + x`, 256 bits'),
         ('mulassoc_w5', '`x * (y * z) = (x * y) * z`, 5 bits'), ('andor_w1024', '`(x &&& y) + (x ||| y) = x + y`, 1024 bits'),
         ('mul3_w512', '`x * 3 = x + x + x`, 512 bits'), ('mul3_w1024', '`x * 3 = x + x + x`, 1024 bits'),
         ('andor_w4096', '`(x &&& y) + (x ||| y) = x + y`, 4096 bits (split base check, 4 segments)'),
         ('andor_w8192', '`(x &&& y) + (x ||| y) = x + y`, 8192 bits (split base check, 8 segments)')]
wall, peak, logs = {}, {}, {}
for d in ('bench_v1', 'bench_v2'):
    for res in sorted((T / 'evidence' / d).glob('results*.tsv')):
        for line in res.read_text().splitlines():
            c = line.split('\t')
            if len(c) >= 4 and c[1] == '0':
                wall[c[0]], peak[c[0]] = float(c[2]), int(c[3])
    for lg in sorted((T / 'evidence' / d).glob('bvk_*')):
        m = re.search(r'(\d+) clauses, (\d+) LRAT steps, (\d+) hints', lg.read_text(errors='ignore'))
        if m:
            logs[re.sub(r'\.(lean\.log|log|progress)$', '', lg.name)] = m.groups()
print('single facts:')
for key, label in GOALS:
    cl, st, hi = logs['bvk_' + key]
    k, d = wall['bvk_' + key + '.lean'], wall['bvd_' + key + '.lean']
    ks = f'{k:,.0f} s' if k >= 100 else f'{k:.1f} s'
    print(f'| {label} | {int(cl):,} | {int(st):,} | {int(hi):,} | {d:.1f} s | {ks} | {peak["bvk_" + key + ".lean"] / 1048576:.1f} GiB |')

# ---- the four packages
PKG = [('veir', 'veir (v4.35.0-rc4)', ('veir',)), ('clean', 'clean (v4.33.1)', ('clean',)),
       ('Natuvea', 'Natuvea (v4.31.0)', ('natuvea_model', 'natuvea_proofs')), ('asi', 'asi-stack-book (v4.31.0)', ('asi',))]
print('packages:')
for _, label, keys in PKG:
    rs = [r for r in rows if r['package'] in keys]
    v = sorted(num(r, 'bv_kdecide_ms') for r in rs)
    pk = sorted(max(num(r, 'peak_bv_decide_MiB'), num(r, 'peak_kernel_route_MiB')) for r in rs)
    print(f'| {label}: {len(rs)} | {sec(S.median(v))} | {sec(p90(v))} | {sec(v[-1])} | {sum(v) / 1000:,.0f} s | '
          f'{S.median(pk) / 1024:.1f} GiB, {pk[-1] / 1024:.1f} GiB |')

# ---- limits per fact
print('limits:')
for lim, label in ((1, '1 s'), (10, '10 s'), (60, '60 s'), (300, '300 s'), (None, 'none')):
    kept = [r for r in rows if lim is None or num(r, 'bv_kdecide_ms') <= lim * 1000]
    added = sum(num(r, 'bv_kdecide_ms') - num(r, 'bv_decide_ms') for r in kept)
    print(f'| {label} | {len(kept)} | {added / 1000:,.0f} s |')

# ---- the largest fact and the module without its 7 largest facts
big = max(rows, key=lambda r: num(r, 'bv_kdecide_ms'))
print(f"largest fact: {big['declaration'].split('.')[-1]}: {num(big, 'cnf_clauses'):,} clauses, {num(big, 'hints') / 1e6:.1f} million hints, "
      f"{big['split_segments']} segments, {num(big, 'bv_kdecide_ms') / 60000:.0f} minutes, "
      f"{max(num(big, 'peak_bv_decide_MiB'), num(big, 'peak_kernel_route_MiB')) / 1024:.1f} GiB")
md = (T / 'real_facts_final.md').read_text()
m = re.search(r'^\| veir \| ISelA \| (\d+) s, ([\d.]+) GiB \| (\d+) s, ([\d.]+) GiB \|$', md, re.M)
isel = [r for r in rows if r['module'] == 'InstructionSelection.Proofs']
print(f'InstructionSelection.Proofs: {len(isel)} facts, {len(isel) - 7} without the 7 largest; that copy: bv_decide {m.group(1)} s, '
      f'bv_kdecide {int(m.group(3)):,} s, peak {float(m.group(4)):.1f} GiB')

# ---- the estimate of bvs5_estimate
k = [num(r, 'bv_kdecide_ms') for r in rows]
cl = [num(r, 'cnf_clauses') for r in rows]
est = [0.064 * c ** 1.355 for c in cl]
over1 = [(e, t) for e, t in zip(est, k) if t > 1000]
rel = sorted(abs(e - t) / t for e, t in over1)
split = sorted(e / t for e, t, r in zip(est, k, rows) if r['split_segments'] not in ('', '-', '0'))


def ranks(v):
    o = sorted(range(len(v)), key=lambda i: v[i])
    r = [0.0] * len(v)
    i = 0
    while i < len(o):
        j = i
        while j + 1 < len(o) and v[o[j + 1]] == v[o[i]]:
            j += 1
        for t in range(i, j + 1):
            r[o[t]] = (i + j) / 2 + 1
        i = j + 1
    return r


def spearman(x, y):
    rx, ry = ranks(x), ranks(y)
    mx, my = S.mean(rx), S.mean(ry)
    return sum((a - mx) * (b - my) for a, b in zip(rx, ry)) / math.sqrt(sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry))


kr = [t - num(r, 'bv_decide_ms') for t, r in zip(k, rows)]
cert = [num(r, 'bv_decide_cert_bytes') for r in rows]
bvd = [num(r, 'bv_decide_ms') for r in rows]
print(f'estimate: {len(over1)} facts above 1 s: median relative error {S.median(rel) * 100:.0f} %, 90th percentile {p90(rel) * 100:.0f} %; '
      f'split-base-check facts overestimated {split[0]:.1f} to {split[-1]:.1f} times; sum overestimated {sum(est) / sum(k):.2f} times; '
      f'same decision as the measured time for a 60 s limit: {sum((e <= 60000) == (t <= 60000) for e, t in zip(est, k))} of {len(k)}')
print(f'rank correlation of the bv_kdecide time with the CNF size {spearman(k, cl):.2f}, the certificate size {spearman(k, cert):.2f}, '
      f'the bv_decide time {spearman(k, bvd):.2f}; of the kernel route alone (bv_kdecide - bv_decide): {spearman(kr, cl):.2f}, '
      f'{spearman(kr, cert):.2f}, {spearman(kr, bvd):.2f}')
