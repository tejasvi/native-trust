#!/usr/bin/env python3
"""Compare gate results v10-<pkg> (library v11, build nt_fix10) with their baselines: every baseline PROVED fact that was re-run must be PROVED again,
and no re-run fact may need the accGen fallback. Run as ntbuild on the box."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import os
R = (NT_BOX + '/results')
PAIRS = [('v11-cvc5-logos', 'cvc5-logos-nt18'), ('v11-lido-srv3', 'lido-srv3'), ('v11-cedar-lean', 'cedar-lean'),
         ('v11-sounio', 'sounio'), ('v11-asi-stack-book', 'asi-stack-book'), ('v11-humanfia-icho2026', 'humanfia-icho2026'),
         ('v11-zag', 'retry-zag'), ('v11-strata', 'strata-nt18'), ('v11-trainverify', 'trainverify'),
         ('v11-formal-conjectures', 'formal-conjectures-nt18'),
         ('v11c-asi-stack-book', 'v10c-asi-stack-book'), ('v11c-formal-conjectures', 'v10c-formal-conjectures'),
         ('v11-zag-all', 'v10-zag-all'),
         ('v11s-codegraff', 'v8s-codegraff-nt9c'), ('v11s-minidregg', 'v8s-minidregg-nt9c'), ('v11s-cedar', 'v8s-cedar-nt9c')]
def load(n):
    f = next((p for p in (os.path.join(d, n + '.ax.tsv') for d in [R] + [x for x in os.environ.get('NT_RESULTS', '').split(':') if x]) if os.path.exists(p)), os.path.join(R, n + '.ax.tsv')); last = {}
    if os.path.exists(f):
        for l in open(f, errors='ignore'):
            c = l.rstrip('\n').split('\t')
            if len(c) >= 7: last[(c[1], c[2])] = c
    return last
allok = True
for g, b in PAIRS:
    G, B = load(g), load(b)
    if not G:
        print(f"{g}: NOT RUN YET"); allok = False; continue
    rerun = [k for k in G if k in B and B[k][5] == 'PROVED']
    lost = [k for k in rerun if G[k][5] != 'PROVED']
    fb = [k for k in rerun if G[k][6] == 'acc_fallback']
    ok = not lost and not fb
    allok &= ok
    print(f"{g}: re-run {len(rerun)} of {sum(1 for v in B.values() if v[5]=='PROVED')} baseline PROVED; "
          f"lost {len(lost)}; acc_fallback {len(fb)}; {'PASS' if ok else 'FAIL'}")
    for k in lost[:5]: print("   LOST", k[0], k[1][-80:], G[k][5], G[k][6], G[k][10][:100] if len(G[k]) > 10 else '')
print("ALL PASS" if allok else "NOT ALL PASS")
