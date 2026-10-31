#!/usr/bin/env python3
"""ms_v3_bvs_ax.py: the v3 bv_decide results (sweeps) in the driver's 12-column .ax.tsv format, for the G column
(the bv_decide pipeline as a general add-on). Run on the box as ntbuild with python3 -I.

Inputs (all under $NT_BOX/v3/sweeps/bvs): facts.tsv (the 196 facts listed by bvs5_list, the study's list
without Radix), results/p1.tsv and results/p1h.tsv (one process per fact: bvs5_fact, 900 s, 48 GiB address space,
one thread), results/pass2.tsv (bvs5_prep / bvs6_prep with 4 shards, 3600 s and 48 GiB per process, shards 2 at a
time, for the facts that end TIMEOUT or MEMORY in one process), checks/p1*.axioms.tsv (fresh-process #print axioms),
study_final_per_fact.tsv (Radix's 17 facts, not run: the archived bvs needs Lean 4.31 or later).
Base runs: $NT_BOX/results/v3-<pkg>.ax.tsv (the inner flag is taken from there; a fact missing there is listed).
Output: $NT_BOX/results/v3bvs-<pkg>.ax.tsv, one row per fact (refused if the file exists), columns
package (= the stem), module, axiom, tactic (bv_decide), inner, verdict (PROVED / TIMEOUT / ERROR / FAILED), reason,
kernel_ms, maxrss_kb, secs, blockers (empty), notes (route and limits).
PROVED = the fact theorem bvs5fact_<i>.unsat (or the shard/split route's) was added with only the standard axioms, in
the run and again in a fresh process; the users of the module were rebuilt (counts in notes).
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, sys
from pathlib import Path

B = Path((NT_BOX + '/v3/sweeps/bvs'))
R = Path((NT_BOX + '/results'))
LIM1 = 'one process per fact (bvs5_fact), 900 s, 48 GiB address space, 1 thread'
LIM2 = '4 shards, 2 at a time, 3600 s and 48 GiB per process'


def tsv(p, skip_header=True):
    ls = p.read_text(errors='ignore').splitlines()
    return [l.split('\t') for l in (ls[1:] if skip_header else ls) if l]


def main():
    facts = tsv(B / 'facts.tsv', skip_header=False)
    single = {}
    for r in ('p1', 'p1h'):
        for c in tsv(B / 'results' / f'{r}.tsv'):
            single[(c[1], c[2], c[3])] = c + [r]
    chk = {}
    for r in ('p1', 'p1h'):
        for c in tsv(B / 'checks' / f'{r}.axioms.tsv', skip_header=False):
            if c[4] == 'fact':
                chk[(c[0], c[1], c[2])] = c[6]
    p2 = {}
    for c in tsv(B / 'results' / 'pass2.tsv'):
        w = c[2].split()
        if w[0] in ('shards', 'split'):
            p2[(c[1], w[1], w[2])] = c
    out = collections.defaultdict(list)
    for pkg, mod, idx, ax in facts:
        k = (pkg, mod, idx)
        s = single.get(k)
        if s is None:
            out[pkg].append([mod, ax, 'ERROR', 'not run', '', '', '', 'no result row'])
            continue
        v, reason, wall, rss, kms = s[5], s[6], s[7], s[8], s[10]
        users = f'users rebuilt {s[13]}, of them standard axioms and same type {s[14]}'
        if v == 'CONVERTED':
            fresh = chk.get(k, '?')
            if fresh == 'std':
                out[pkg].append([mod, ax, 'PROVED', '', kms, rss, wall,
                                 f'bvs ed02e2be with NativeTrust v15 loaded; {LIM1}; run {s[-1]}; fresh-process axioms std; {users}'
                                 + (f'; {reason}' if reason else '')])
            else:
                out[pkg].append([mod, ax, 'FAILED', 'fresh check', kms, rss, wall, f'fresh-process axioms {fresh}; run {s[-1]}'])
            continue
        q = p2.get(k)
        if q is not None and q[3] == 'CONVERTED':
            steps = q[4]
            secs = sum(int(x.split('=')[1]) for x in steps.replace(';', ' ').split() if x.startswith('wall='))
            pk = max(int(x.split('=')[1]) for x in steps.replace(';', ' ').split() if x.startswith(('peak_kb=', 'max_peak_kb=')))
            route = 'bvs5_prep' if q[2].startswith('shards') else 'bvs6_prep, split base check, segments of 30,000 gates'
            out[pkg].append([mod, ax, 'PROVED', '', '', str(pk), str(secs),
                             f'bvs ed02e2be with NativeTrust v15 loaded; after {v} {reason} in {LIM1} (run {s[-1]}): {route}, {LIM2}; '
                             f'fresh-process check: {q[7]}'])
            continue
        vv = {'TIMEOUT': 'TIMEOUT', 'MEMORY': 'ERROR'}.get(v, 'FAILED')
        rr = {'MEMORY': 'memory'}.get(v, reason)
        out[pkg].append([mod, ax, vv, rr, kms, rss, wall, f'{LIM1}; run {s[-1]}; follow-up: {q[3] if q else "none"}'])
    for c in tsv(B / 'study_final_per_fact.tsv'):
        if c[0] == 's_Provenance_Works_Radix':
            out[c[0]].append([c[1], c[3], 'FAILED', 'unsupported_toolchain', '', '', '',
                              'not run: the archived bvs ed02e2be needs Lean v4.31 or later; the package is on v4.29.0-rc4 '
                              '(build check: BVS/Blast.lean:332 Unknown constant Std.Tactic.BVDecide.BVUnOp.cpop)'])
    for pkg in sorted(out):
        stem = f'v3bvs-{pkg}'
        dst = R / f'{stem}.ax.tsv'
        if dst.exists():
            sys.exit(f'refused: {dst} exists')
        base = {}
        bf = R / f'v3-{pkg}.ax.tsv'
        if bf.exists():
            for c in tsv(bf, skip_header=False):
                if len(c) >= 7:
                    base[(c[1], c[2])] = c
        rows, miss = [], 0
        for mod, ax, v, reason, kms, rss, secs, notes in out[pkg]:
            b = base.get((mod, ax))
            if b is None:
                miss += 1
            rows.append('\t'.join([stem, mod, ax, 'bv_decide', b[4] if b else '', v, reason, kms, rss, secs, '', notes]))
        dst.write_text('\n'.join(rows) + '\n')
        bvd = {k for k, c in base.items() if c[3] == 'bv_decide'}
        mine = {(r[0], r[1]) for r in out[pkg]}
        cnt = collections.Counter(r[2] for r in out[pkg])
        print(f'G\tv3-{pkg}\t{stem}\trows={len(rows)} {dict(cnt)} base_bv_decide={len(bvd)} '
              f'in_both={len(bvd & mine)} only_base={len(bvd - mine)} only_bvs={len(mine - bvd)} missing_in_base={miss}')


if __name__ == '__main__':
    main()
