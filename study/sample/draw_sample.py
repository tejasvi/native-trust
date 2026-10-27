#!/usr/bin/env python3
"""The draw of the random sample of repositories (seed 20261023), as run on 2026-10-23.

usage: python3 -I -B study/sample/draw_sample.py [FRAME [EXCLUDED]]
       (defaults: study/sample/frame585.tsv and study/sample/excluded35.tsv)

FRAME: the 585 repositories that GitHub code search returned for `native_decide language:Lean` in October 2026
(columns: files, repository, stars, pushed, created, size in KB as GitHub reports it, fork, archived, language, description).
EXCLUDED: the 35 repositories examined or inspected before the draw (first column). The candidates are the other
repositories that are neither forks nor archived and smaller than 400,000 KB; 70 of them are drawn with
random.sample after random.seed(20261023). The counts go to standard error, the 70 repositories in draw order to
standard output (the run wrote them to sample585.txt). In the run the 35 names were written into the command
itself; here they are read from EXCLUDED.
"""
import random
import sys

frame = sys.argv[1] if len(sys.argv) > 1 else 'study/sample/frame585.tsv'
excluded = sys.argv[2] if len(sys.argv) > 2 else 'study/sample/excluded35.tsv'
rows = [l.rstrip('\n').split('\t') for l in open(frame)]
studied = {l.split('\t')[0] for l in open(excluded).read().splitlines()[1:] if l.strip()}
cand = [r for r in rows if r[1] not in studied and r[6] == 'false' and r[7] == 'false' and int(r[5] or 0) < 400000]
big = [r for r in rows if r[1] not in studied and int(r[5] or 0) >= 400000]
forks = [r for r in rows if r[6] != 'false' or r[7] != 'false']
random.seed(20261023)
pick = random.sample(cand, 70)
print(f"frame {len(rows)}; excluded {len(studied)} (in the frame: {sum(1 for r in rows if r[1] in studied)}); "
      f"forks or archived {len(forks)}; at least 400,000 KB {len(big)}; candidates {len(cand)}; drawn {len(pick)}",
      file=sys.stderr)
print('\n'.join(r[1] for r in pick))
