#!/usr/bin/env python3
"""The CPU cost of BerryEsseen's conversions, by the mechanism that after_table.py credits each fact to.
usage: python3 -I -B study/checks/be_cost.py   (from the artifact's root; runs study/aggregators/after_table.py --facts)

Seconds are the summed elapsed seconds of lean processes that each ran on one thread (-j1):
  tokenizer add-on     study/results/after/specific/berry-esseen-v8.ax.tsv: column 10 of each credited fact's PROVED row;
  earlier modules      study/results/after/specific/strings/berry_esseen_strings.tsv: wall_s of each credited module's first
                       PROVED row (BE3 and DW2 were run again with later versions of the add-on; those runs are not counted);
  covers parsed once   study/results/after/specific/covers/berry-esseen-covers.ax.tsv: column 10, all processes of the
                       cover (tree, parse, leaf modules, assembly, final check);
  sharded chunks       study/results/after/library/shards/<tag>/times.txt: sum_secs, all pieces and the combining module.
peak_GiB: the largest maximum resident set of a single process. Not counted: the 2 facts of the study's own run, and
failed attempts (such as the tokenizer run's 47 facts that ran out of memory and were then converted by the covers)."""
import os
import re
import subprocess
import sys
from pathlib import Path

AFT = Path('study/results/after')
BE = ('corpus', 'berry-esseen')
MECH = [('BerryEsseen tokenizer add-on', 'tokenizer add-on'),
        ('BerryEsseen tokenizer add-on (earlier modules)', 'earlier modules'),
        ('BerryEsseen covers parsed once', 'covers parsed once'),
        ('shard ', 'sharded chunks')]


def die(msg):
    sys.exit(f'be_cost.py: {msg}')


def credited():
    """(module, axiom, source) of every BerryEsseen fact that after_table.py credits outside the study's own run."""
    r, w = os.pipe()
    p = subprocess.Popen([sys.executable, '-I', '-B', 'study/aggregators/after_table.py', '--facts', f'/dev/fd/{w}'],
                         pass_fds=(w,), stdout=subprocess.DEVNULL)
    os.close(w)
    with os.fdopen(r) as f:
        lines = f.read().splitlines()
    if p.wait() != 0:
        die(f'after_table.py exited with {p.returncode}')
    if not lines or lines[0].split('\t')[:4] != ['set', 'package', 'module', 'axiom']:
        die('unexpected --facts output')
    out = []
    for line in lines[1:]:
        c = line.split('\t')
        if tuple(c[:2]) != BE:
            continue
        if '; ' in c[7]:
            die(f'more than one source for {c[3]}: {c[7]}')
        out.append((c[2], c[3], c[7]))
    return out


def ax_rows(path):
    """axiom -> (secs, maxrss_kb) of its PROVED row in a driver result (.ax.tsv)."""
    rows = {}
    for line in path.read_text().splitlines():
        c = line.split('\t')
        if len(c) >= 10 and c[5] == 'PROVED':
            if c[2] in rows:
                die(f'two PROVED rows for {c[2]} in {path}')
            rows[c[2]] = (float(c[9]), int(c[8]))
    return rows


def main():
    facts = credited()
    v8 = ax_rows(AFT / 'specific' / 'berry-esseen-v8.ax.tsv')
    bo = ax_rows(AFT / 'specific' / 'covers' / 'berry-esseen-covers.ax.tsv')
    st = {}
    lines = (AFT / 'specific' / 'strings' / 'berry_esseen_strings.tsv').read_text().splitlines()
    head = lines[0].split('\t')
    for line in lines[1:]:
        c = dict(zip(head, line.split('\t')))
        if c['verdict'] == 'PROVED':
            # peak_GB is kilobytes / 10^6
            st.setdefault('BerryEsseen.Upper0423.' + c['module'], (float(c['wall_s']), round(float(c['peak_GB']) * 1e6)))
    tot = {m: [0, 0.0, 0] for _, m in MECH}
    for module, axiom, src in facts:
        if src == MECH[0][0]:
            secs, kb = v8.get(axiom) or die(f'no PROVED row for {axiom} in berry-esseen-v8.ax.tsv')
        elif src == MECH[1][0]:
            secs, kb = st.get(module) or die(f'no PROVED row for {module} in berry_esseen_strings.tsv')
        elif src == MECH[2][0]:
            secs, kb = bo.get(axiom) or die(f'no PROVED row for {axiom} in berry-esseen-covers.ax.tsv')
        elif src.startswith(MECH[3][0]):
            t = (AFT / 'library' / 'shards' / src[len(MECH[3][0]):] / 'times.txt').read_text()
            m = re.search(r'^max_rss_kb (\d+) sum_secs ([0-9.]+)$', t, re.M) or die(f'no sum_secs line in times.txt of {src}')
            secs, kb = float(m.group(2)), int(m.group(1))
        else:
            die(f'unexpected source {src!r} for {axiom}')
        m = next(n for s, n in MECH if src == s or (s == MECH[3][0] and src.startswith(s)))
        tot[m][0] += 1
        tot[m][1] += secs
        tot[m][2] = max(tot[m][2], kb)
    print('mechanism\tfacts\tseconds\tCPU_h\tpeak_GiB')
    for _, m in MECH:
        n, s, kb = tot[m]
        print(f'{m}\t{n}\t{s:.0f}\t{s / 3600:.1f}\t{kb / 2 ** 20:.1f}')
    n, s, kb = (sum(t[0] for t in tot.values()), sum(t[1] for t in tot.values()), max(t[2] for t in tot.values()))
    print(f'total\t{n}\t{s:.0f}\t{s / 3600:.1f}\t{kb / 2 ** 20:.1f}')


if __name__ == '__main__':
    main()
