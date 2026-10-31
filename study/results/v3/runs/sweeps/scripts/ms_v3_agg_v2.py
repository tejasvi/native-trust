#!/usr/bin/env python3
"""ms_v3_agg_v2.py: tables of the sweep parts of paper v3, from the v3 results files only (run on the box as
ntbuild, python3 -I; reads $NT_BOX/results and $NT_BOX/v3/sweeps/bvs; writes $NT_BOX/v3/sweeps/agg/).
v2 (from ms_v3_agg.py): the default run of a package is v3-<pkg> with v3r-<pkg> (harness re-runs) laid over it, and
the plain run is v3plain-<pkg> with v3plainr-<pkg> (harness-killed checks re-run alone) laid over it.

1. Ablation (as the study's plain_agg.py): per package, the outer facts PROVED in the v3 default run (v3-<pkg>, last row
   per fact, inner != True), how many of them have a row in v3plain-<pkg> (wf := false, split := 1), how many of those
   are PROVED there, and the verdicts/reasons of the others. Inner facts (phase 1) are counted apart.
2. Blocked labels without the cap: per package, the facts of v3nocap-<pkg> (blockedHeartbeats := 0): outer facts by
   final verdict/reason, inner facts apart.
3. bv_decide: per package, the facts of runs p1 + p1h (one process per fact) by verdict, the follow-ups (pass2.tsv),
   the fresh-process checks (checks/p1*.axioms.tsv).
usage: ms_v3_agg.py
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, os
from pathlib import Path

R = Path((NT_BOX + '/results'))
B = Path((NT_BOX + '/v3/sweeps/bvs'))
OUT = Path((NT_BOX + '/v3/sweeps/agg/v2'))
PKGS = ['trainverify', 'strata', 'cvc5-logos', 'lido-srv3', 'cedar-lean', 'aks', 'sorting-network-expanders', 'aeneas-lean',
        'rs-mca-m31_dyadic_weight_laws', 'rs-mca-m31_flatness_keystone', 'formal-conjectures', 'longfellow-zk',
        'berry-esseen', 'humanfia-icho2026', 'sounio', 'asi-stack-book', 'clean']
NOCAP = ['berry-esseen', 'strata', 'cedar-lean']


def last_rows(name):
    f = R / f'{name}.ax.tsv'
    out = {}
    if f.exists():
        for l in f.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if len(c) >= 7:
                out[(c[1], c[2])] = c
    return out


def default_rows(p):
    """The v3 default run of p: v3-<p>, with the harness re-runs v3r-<p> (same configuration) laid over it."""
    d = last_rows(f'v3-{p}')
    d.update(last_rows(f'v3r-{p}'))
    return d


def plain_rows(p):
    """v3plain-<p>, with the re-runs of its harness-killed checks (alone, same configuration) v3plainr-<p> laid over it."""
    b = last_rows(f'v3plain-{p}')
    b.update(last_rows(f'v3plainr-{p}'))
    return b


def ablation():
    lines = ['package\tproved_default_outer\tre_run_plain\tproved_plain\tnot_proved_plain(verdict/reason=n)\tplain_inner_rows\tplain_inner_proved']
    tot = collections.Counter()
    for p in PKGS:
        d = default_rows(p)
        if not d:
            lines.append(f'{p}\t(no v3 default results)')
            continue
        a = {k: v for k, v in d.items() if v[5] == 'PROVED' and v[4] != 'True'}
        b = plain_rows(p)
        rer = {k: v for k, v in b.items() if k in a}
        ok = sum(1 for v in rer.values() if v[5] == 'PROVED')
        bad = collections.Counter((v[5], v[6]) for v in rer.values() if v[5] != 'PROVED')
        inner = [v for v in b.values() if v[4] == 'True']
        tot['default'] += len(a); tot['rerun'] += len(rer); tot['plain'] += ok
        lines.append(f'{p}\t{len(a)}\t{len(rer)}\t{ok}\t' + ' '.join(f'{x}/{y or "-"}={n}' for (x, y), n in bad.most_common()) +
                     f'\t{len(inner)}\t{sum(1 for v in inner if v[5] == "PROVED")}')
    lines.append(f'TOTAL\t{tot["default"]}\t{tot["rerun"]}\t{tot["plain"]}\tneed a transformation (of re-run): {tot["rerun"] - tot["plain"]}')
    return lines


def nocap():
    lines = ['package\tdefault_blocked_outer\tnocap_outer_rows\tnocap_outer(verdict/reason=n)\tnocap_inner(verdict=n)']
    for p in NOCAP:
        d = default_rows(p)
        blk = sum(1 for v in d.values() if v[5] == 'FAILED' and v[6] == 'blocked' and v[4] != 'True')
        b = last_rows(f'v3nocap-{p}')
        outer = [v for v in b.values() if v[4] != 'True']
        inner = [v for v in b.values() if v[4] == 'True']
        lines.append(f'{p}\t{blk}\t{len(outer)}\t' + ' '.join(f'{x}/{y or "-"}={n}' for (x, y), n in collections.Counter((v[5], v[6]) for v in outer).most_common()) +
                     '\t' + ' '.join(f'{x}={n}' for x, n in collections.Counter(v[5] for v in inner).most_common()))
    return lines


def bvs():
    rows = {}
    for r in ('p1', 'p1h'):
        f = B / 'results' / f'{r}.tsv'
        if f.exists():
            for l in f.read_text(errors='ignore').splitlines()[1:]:
                c = l.split('\t')
                if len(c) > 6:
                    rows[(c[1], c[2], c[3])] = c
    lines = ['package\tfacts_run\tverdicts (single process, 900 s / 48 GiB)']
    by = collections.defaultdict(collections.Counter)
    for (p, m, i), c in rows.items():
        by[p][c[5]] += 1
    for p in sorted(by):
        lines.append(f'{p}\t{sum(by[p].values())}\t' + ' '.join(f'{k}={n}' for k, n in by[p].most_common()))
    lines.append(f'TOTAL\t{len(rows)}\t' + ' '.join(f'{k}={n}' for k, n in collections.Counter(c[5] for c in rows.values()).most_common()))
    for r in ('p1', 'p1h'):
        f = B / 'checks' / f'{r}.axioms.tsv'
        if f.exists():
            ck = [l.split('\t') for l in f.read_text().splitlines() if l]
            fr = [c for c in ck if c[4] == 'fact']
            ur = [c for c in ck if c[4] != 'fact']
            lines.append(f'checks {r}: facts {len(fr)} std {sum(1 for c in fr if c[6] == "std")}; rebuilt {len(ur)} std '
                         f'{sum(1 for c in ur if c[6] == "std")} type_identical {sum(1 for c in ur if c[7] == "true")}')
    f = B / 'results' / 'pass2.tsv'
    if f.exists():
        lines += ['pass2: ' + '\t'.join(l.split('\t')[:5]) for l in f.read_text().splitlines()[1:]]
    return lines


def main():
    OUT.mkdir(exist_ok=True)
    for name, fn in (('ablation', ablation), ('nocap', nocap), ('bvs', bvs)):
        txt = '\n'.join(fn()) + '\n'
        (OUT / f'{name}.tsv').write_text(txt)
        print(f'== {name}\n{txt}')


if __name__ == '__main__':
    main()
