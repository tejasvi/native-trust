#!/usr/bin/env python3
"""usage: dsub.py SPEC...  (content:N, run on the box next to gen4.py) -- number of distinct non-empty substrings
of the literal's UTF-8 byte sequence (suffix automaton), the quantity the measured kernel memory tracks."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import sys, types
src = open((NT_BOX + '/strlit/gen4.py'), encoding='utf-8').read().split('\nout = Path')[0]
g = {'__name__': 'gen2lib'}
exec(compile(src, 'gen4.py', 'exec'), g)

def distinct_substrings(b):
    # suffix automaton; count = sum(len[v] - len[link[v]])
    maxlen = [0]; link = [-1]; nxt = [dict()]; last = 0
    for c in b:
        cur = len(maxlen); maxlen.append(maxlen[last] + 1); link.append(0); nxt.append(dict())
        p = last
        while p != -1 and c not in nxt[p]:
            nxt[p][c] = cur; p = link[p]
        if p != -1:
            q = nxt[p][c]
            if maxlen[p] + 1 == maxlen[q]:
                link[cur] = q
            else:
                cl = len(maxlen); maxlen.append(maxlen[p] + 1); link.append(link[q]); nxt.append(dict(nxt[q]))
                while p != -1 and nxt[p].get(c) == q:
                    nxt[p][c] = cl; p = link[p]
                link[q] = cl; link[cur] = cl
        last = cur
    return sum(maxlen[v] - maxlen[link[v]] for v in range(1, len(maxlen)))

for spec in sys.argv[1:]:
    kind, n = spec.split(':')[:2]
    b = g['content'](kind, int(n)).encode('utf-8')
    print(f'{kind}_{n}\tbytes={len(b)}\tdistinct_substrings={distinct_substrings(b)}')
