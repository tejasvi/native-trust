#!/usr/bin/env python3
"""Sizes of the string literals in BerryEsseen's cover data modules (study/results/berryesseen_literals.tsv).

usage: python3 -I -B study/checks/be_literal_sizes.py BERRYESSEEN_CHECKOUT > literals.tsv

Every .lean file under BerryEsseen/ in a directory named Data; comments are removed first. Prints one TSV line per
module: path, number of string literals, the byte length of each literal (UTF-8, between the quotes, escapes as
written). The study used the repository at commit bfb22608ad18 (Appendix A).
"""
import re
import sys
from pathlib import Path

repo = Path(sys.argv[1])
lit = re.compile(r'"((?:[^"\\]|\\.)*)"', re.S)
print('module\tliterals\tbytes')
for f in sorted(repo.glob('BerryEsseen/**/Data/*.lean')):
    t = f.read_text(errors='replace')
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    t = re.sub(r'--[^\n]*', '', t)
    sizes = [len(m.group(1).encode()) for m in lit.finditer(t)]
    print(f"{f.relative_to(repo)}\t{len(sizes)}\t{','.join(map(str, sizes))}")
