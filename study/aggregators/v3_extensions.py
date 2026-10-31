#!/usr/bin/env python3
"""v3_extensions.py: the facts that each opt-in extension converts, among the facts of the corpus and the random sample
that the final run does not convert (Table 3 (b) of the paper): for every extension, the facts that its result files prove
and that have no conversion in the final run's D passes (study/results/v3/agg/facts_D.tsv, column D), with their packages.
A fact can convert with more than one extension; Table 3 (a) counts each fact once.
usage (from the artifact's top directory): python3 -I -B study/aggregators/v3_extensions.py
"""
import collections
import glob

C = 'study/results/v3/components/'
SHORT = {'s_opencompl_veir': 'VeIR', 's_Natuvea_tacenta_core_tacenta_model': 'tacenta',
         's_Natuvea_tacenta_core_tacenta_proofs': 'tacenta', 's_moggedhedien_rimalloc_verify': 'rimalloc',
         'humanfia-icho2026': 'Humanfia', 's_clementefalcone_goya_ledger_formal': 'goya', 'berry-esseen': 'BerryEsseen',
         'trainverify': 'TrainVerify', 'strata': 'Strata', 's_BobDyLean_bobdylean_paper_artifact': 'BobDyLean',
         's_emberian_minidregg': 'minidregg', 's_pandaman64_lean_regex_correctness': 'lean-regex'}
EXT = [('general add-ons', 'bv_decide pipeline', 'bv_decide/v3bvs-*'), ('general add-ons', '@[csimp] add-on', 'addons/v3a-csimp_*'),
       ('options', 'propSplit', 'propsplit/v3p-*'), ('options', 'stage, csimp, propSplit, up to 16 parts', 'options/v3o-*'),
       ('options', 'shards', 'shards/v3s-*'), ('package add-ons', 'tokenizer replacement', 'addons/v3b-tok-*'),
       ('package add-ons', 'covers parsed once per certificate', 'addons/v3b-covers-*'),
       ('package add-ons', 'primality proofs by norm_num', 'addons/v3a-primes_clean-*'),
       ('package add-ons', 'hash-map lookups as array scans', 'addons/v3a-strata-*'),
       ('package add-ons', 'fast binomial coefficient', 'addons/v3a-longfellow-*'),
       ('package add-ons', 'DecidableEq instance', 'addons/v3a-bob-*'),
       ('package add-ons', 'list version of a graph linearization', 'addons/v3a-minidregg-*'),
       ('package add-ons', 'Pratt primality certificates', 'addons/v3a-fcprimes-*'),
       ('package add-ons', 'linear checks of a case-fold table', 'addons/v3a-regex-*')]
conv = {}
for line in open('study/results/v3/agg/facts_D.tsv', encoding='utf-8'):
    c = line.rstrip('\n').split('\t')
    if c[0] != 'base':
        conv[(c[0], c[1], c[2])] = c[11] == '1'
base_of_map = {}
for line in open('study/aggregators/v3_map.tsv', encoding='utf-8'):
    if line.strip() and not line.startswith('#'):
        col, base, stem = line.rstrip('\n').split('\t')[:3]
        base_of_map[stem] = base
for group, name, pat in EXT:
    facts = collections.Counter()
    for f in sorted(glob.glob(C + pat + '.ax.tsv')):
        stem = f.rsplit('/', 1)[1][:-len('.ax.tsv')]
        base = base_of_map.get(stem, stem.split('-', 1)[1])
        seen = set()
        for line in open(f, encoding='utf-8'):
            c = line.rstrip('\n').split('\t')
            key = (base, c[1], c[2]) if len(c) >= 6 else None
            if key and c[5] == 'PROVED' and key in conv and not conv[key] and key not in seen:
                seen.add(key)
                facts[SHORT.get(base, base)] += 1
    pk = ', '.join(f'{p} {n}' for p, n in sorted(facts.items(), key=lambda kv: (-kv[1], kv[0])))
    print(f'{group}\t{name}\t{sum(facts.values())}\t{pk}')
