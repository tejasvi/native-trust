#!/usr/bin/env python3
"""v3_check_blocks.py: compare the generated blocks of paper/main.tex with the outputs of v3_paper_numbers.py on
study/results/v3/agg. The blocks are the lines between a '% BEGIN ...' line and its '% END ...' line:
  v3 numbers           the macros (numbers_v3.tex)
  table1 rows          the rows of Table 1 (table1_v3.tex)
  table2 resource row  the resource row of Table 2: 'time, memory or recursion-depth limit reached & 230 & \vresfail & '
                       (the study's count, fixed, and the macro of the final run's count) followed by the final run's
                       packages from the resource line of table2_v3.tex
  tableext rows        the rows of Table 3 (a) (tableext_v3.tex)
Prints one line per block, 'identical' or 'DIFFERENT', with its number of lines, and exits with status 1 when a block differs
or is missing.
usage (from the artifact's top directory): python3 -I -B study/aggregators/v3_check_blocks.py
"""
import subprocess
import sys
from pathlib import Path

out = subprocess.run([sys.executable, '-I', '-B', 'study/aggregators/v3_paper_numbers.py', 'study/results/v3/agg', '-'],
                     capture_output=True, text=True, check=True).stdout
sections, name = {}, None
for line in out.splitlines():
    if line.startswith('== '):
        name = line[3:]
        sections[name] = []
    elif name is not None:
        sections[name].append(line)
paper = Path('paper/main.tex').read_text().splitlines()


def block(key):
    starts = [i for i, l in enumerate(paper) if l.startswith('% BEGIN ' + key)]
    ends = [i for i, l in enumerate(paper) if l.startswith('% END ' + key)]
    if len(starts) != 1 or len(ends) != 1 or ends[0] < starts[0]:
        return None
    return paper[starts[0] + 1:ends[0]]


res = [l for l in sections.get('table2_v3.tex', []) if l.startswith('time, memory or recursion-depth limit &')]
want = {'v3 numbers': sections.get('numbers_v3.tex'),
        'table1 rows': sections.get('table1_v3.tex'),
        'table2 resource row': ['time, memory or recursion-depth limit reached & 230 & \\vresfail & ' + res[0].split('&', 2)[2].strip()]
        if len(res) == 1 else None,
        'tableext rows': sections.get('tableext_v3.tex')}
bad = 0
for key, lines in want.items():
    got = block(key)
    if got is None or not lines:
        print(f'{key}: MISSING in the paper or in the output')
        bad += 1
    elif got == lines:
        print(f'{key}: identical ({len(lines)} lines)')
    else:
        print(f'{key}: DIFFERENT (paper {len(got)} lines, generator {len(lines)} lines)')
        bad += 1
sys.exit(1 if bad else 0)
