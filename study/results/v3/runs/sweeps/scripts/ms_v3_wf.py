#!/usr/bin/env python3
"""ms_v3_wf.py: converted facts of the v3 default run whose evaluation made well-founded copies, and how many of them
fail without the replacement (the plain runs), as the study's wf_facts.py + the v2 robustness sentence ("All 1,705
converted facts with well-founded copies were also run without the replacement, and 16 failed").
Run on the box as ntbuild with python3 -I. For each corpus package p: the per-fact logs of work/v3-<p> and then
work/v3r-<p> (harness re-runs, laid over), ax[12]*_*.log; a log counts when it reports "PROVED `<axiom>`"; it has
copies when the copies= fields of its NT lines sum to more than 0 (the study's rule). The plain verdict of each such
fact is its last row in results/v3plain-<p> with v3plainr-<p> laid over. Writes $NT_BOX/v3/sweeps/agg/v2/wf.tsv.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, re
from pathlib import Path

H = Path(NT_BOX)
PKGS = ['trainverify', 'strata', 'cvc5-logos', 'lido-srv3', 'cedar-lean', 'aks', 'sorting-network-expanders', 'aeneas-lean',
        'rs-mca-m31_dyadic_weight_laws', 'rs-mca-m31_flatness_keystone', 'formal-conjectures', 'longfellow-zk',
        'berry-esseen', 'humanfia-icho2026', 'sounio', 'asi-stack-book', 'clean']
PROVED_RE = re.compile(r'^PROVED `([^`]+)`', re.M)
COPIES_RE = re.compile(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', re.M)


def rows(name):
    f = H / 'results' / f'{name}.ax.tsv'
    out = {}
    if f.exists():
        for l in f.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if len(c) >= 7:
                out[c[2]] = c
    return out


def main():
    lines = ['package\tproved_logs\twith_copies\twith_copies_outer\tcopies_outer_plain_proved\tcopies_outer_plain_not_proved\tnot_proved(verdict/reason=n)\tcopies_inner']
    tot = collections.Counter()
    for p in PKGS:
        facts = {}
        for run in (f'v3-{p}', f'v3r-{p}'):
            w = H / 'work' / run
            if not w.is_dir():
                continue
            for lg in w.glob('ax[12]*_*.log'):
                t = lg.read_text(errors='ignore')
                m = PROVED_RE.search(t)
                if m:
                    facts[m.group(1)] = sum(int(x) for x in COPIES_RE.findall(t)) > 0
        d = rows(f'v3-{p}'); d.update(rows(f'v3r-{p}'))
        pl = rows(f'v3plain-{p}'); pl.update(rows(f'v3plainr-{p}'))
        cop = [a for a, c in facts.items() if c]
        outer = [a for a in cop if a in d and d[a][4] != 'True']
        inner = [a for a in cop if a in d and d[a][4] == 'True']
        ok = [a for a in outer if a in pl and pl[a][5] == 'PROVED']
        bad = collections.Counter((pl[a][5], pl[a][6]) if a in pl else ('not re-run', '') for a in outer if a not in ok)
        tot['logs'] += len(facts); tot['cop'] += len(cop); tot['outer'] += len(outer); tot['ok'] += len(ok)
        tot['bad'] += len(outer) - len(ok); tot['inner'] += len(inner)
        lines.append(f'{p}\t{len(facts)}\t{len(cop)}\t{len(outer)}\t{len(ok)}\t{len(outer) - len(ok)}\t'
                     + ' '.join(f'{v}/{r or "-"}={n}' for (v, r), n in bad.most_common()) + f'\t{len(inner)}')
    lines.append(f'TOTAL\t{tot["logs"]}\t{tot["cop"]}\t{tot["outer"]}\t{tot["ok"]}\t{tot["bad"]}\t\t{tot["inner"]}')
    out = H / 'v3' / 'sweeps' / 'agg' / 'v2'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'wf.tsv').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
