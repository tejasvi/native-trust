#!/usr/bin/env python3
"""v3_options.py: the opt-in options and the sharding of the final run (Section 4.7), from the result files in
study/results/v3/components/ and the final accounting study/results/v3/agg/facts_D.tsv (columns D, G, P, O, K). Prints:
  propSplit alone: the facts that P converts and G does not, per package;
  options: the facts that the options together (v3o-*) prove, of those that the final run (D) does not convert and that
    propSplit alone does not convert, per package;
  one option alone: per control run (v3oc- csimp, v3os- stage, v3op- propSplit, v3o16- 16 parts), the facts it proves of
    those the final run does not convert; and the facts that only the combination proves;
  3,000 s: the facts that v3oh-trainverify proves and the options run at 900 s does not, how many of them the shards also
    prove, and how many the final run converts (in its heavy pass);
  shards: per package the facts proved by sharding, their number of pieces and the axioms of the combined theorems, and the
    verdicts of the probes and of the nested-fact failures.
usage (from the artifact's top directory): python3 -I -B study/aggregators/v3_options.py
"""
import collections
import glob

C = 'study/results/v3/components/'
fd = {}
for line in open('study/results/v3/agg/facts_D.tsv', encoding='utf-8'):
    c = line.rstrip('\n').split('\t')
    if c[0] != 'base':
        fd[(c[0], c[1], c[2])] = dict(zip(('D', 'G', 'P', 'O', 'K'), (x == '1' for x in c[11:16])), pass_=c[10])


def rows(f):
    out = {}
    for line in open(f, encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if len(c) >= 6:
            out[(c[1], c[2])] = c
    return out


def base_of(f, prefix):
    return f.rsplit('/', 1)[1][len(prefix):-len('.ax.tsv')]


ps = collections.Counter((k[0]) for k, v in fd.items() if v['P'] and not v['G'])
for b, n in sorted(ps.items()):
    print(f'propSplit alone: {b} {n}')
print(f'propSplit alone: total {sum(ps.values())} in {len(ps)} packages')
opt = collections.Counter()
for f in sorted(glob.glob(C + 'options/v3o-*.ax.tsv')):
    b = base_of(f, 'v3o-')
    for k, c in rows(f).items():
        v = fd.get((b,) + k)
        if c[5] == 'PROVED' and v and not v['D'] and not (v['P'] and not v['G']):
            opt[b] += 1
for b, n in sorted(opt.items()):
    print(f'options: {b} {n}')
print(f'options: total {sum(opt.values())}')
alone = collections.defaultdict(set)
for kind in ('v3oc', 'v3os', 'v3op', 'v3o16'):
    for f in sorted(glob.glob(C + f'option_controls/{kind}-*.ax.tsv')):
        b = base_of(f, kind + '-')
        n = 0
        for k, c in rows(f).items():
            v = fd.get((b,) + k)
            if c[5] == 'PROVED' and v and not v['D']:
                n += 1
                alone[b].add(k)
        print(f'one option alone: {kind} {b} {n}')
for f in sorted(glob.glob(C + 'option_controls/v3o16-*.ax.tsv')):
    b = base_of(f, 'v3o16-')
    sel = rows(C.replace('components/', 'selections/') + f'v3ocsel-{b}.ax.tsv')
    only = [k for k in sel if (b,) + k in fd and not fd[(b,) + k]['D'] and k not in alone[b]]
    print(f'only the combination: {b} {len(only)}')
oh, o = rows(C + 'option_controls/v3oh-trainverify.ax.tsv'), rows(C + 'options/v3o-trainverify.ax.tsv')
sh = rows(C + 'shards/v3s-trainverify.ax.tsv')
more = [k for k, c in oh.items() if c[5] == 'PROVED' and c[4] != 'True' and (k not in o or o[k][5] != 'PROVED')]
dmore = [fd[('trainverify',) + k] for k in more if fd.get(('trainverify',) + k, {}).get('D')]
print(f'3,000 s: v3oh-trainverify proves {len(more)} facts that the options at 900 s do not; the shards also prove '
      f'{sum(1 for k in more if k in sh and sh[k][5] == "PROVED")} of them, and the final run converts {len(dmore)} of them '
      f'(in the heavy pass {sum(1 for v in dmore if v["pass_"].startswith("v3h"))})')
for f in sorted(glob.glob(C + 'shards/v3s-*.figs.tsv')) + sorted(glob.glob(C + 'shards/v3spilot-*.figs.tsv')):
    name = f.rsplit('/', 1)[1][:-len('.figs.tsv')]
    lines = [l.rstrip('\n').split('\t') for l in open(f, encoding='utf-8')][1:]
    verdicts = collections.Counter(c[3] for c in lines)
    proved = [c for c in lines if c[3] == 'PROVED']
    if proved:
        pieces = sorted(int(c[4]) for c in proved)
        axioms = collections.Counter(c[10] for c in proved)
        print(f'shards: {name} PROVED {len(proved)}, pieces {pieces[0]} to {pieces[-1]}, combined theorems\' axioms: '
              + '; '.join(f'{a} ({n})' for a, n in sorted(axioms.items())))
    print(f'shards: {name} verdicts ' + ', '.join(f'{k} {n}' for k, n in sorted(verdicts.items())))
