#!/usr/bin/env python3
"""v2: ninegates from v14s-ninegates-all (all baseline facts; laneE selected only baseline-PROVED facts, i.e. none).
Compare gate results v14-<pkg> (library v14, build nt_fix13) with their baselines: every baseline PROVED fact that was re-run must be PROVED again,
and no re-run fact may need the accGen fallback. Run as ntbuild on the box."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import os
R = (NT_BOX + '/results')
PAIRS = [('v14-cvc5-logos', 'cvc5-logos-nt18'), ('v14-lido-srv3', 'lido-srv3'), ('v14-cedar-lean', 'cedar-lean'),
         ('v14-sounio', 'sounio'), ('v14-asi-stack-book', 'asi-stack-book'), ('v14-humanfia-icho2026', 'humanfia-icho2026'),
         ('v14-zag', 'retry-zag'), ('v14-strata', 'strata-nt18'), ('v14-trainverify', 'trainverify'),
         ('v14-formal-conjectures', 'formal-conjectures-nt18'),
         ('v14c-asi-stack-book', 'v10c-asi-stack-book'), ('v14c-formal-conjectures', 'v10c-formal-conjectures'),
         ('v14-zag-all', 'v10-zag-all'),
         ('v14s-codegraff', 'v8s-codegraff-nt9c'), ('v14s-minidregg', 'v8s-minidregg-nt9c'), ('v14s-cedar', 'v8s-cedar-nt9c'),
         ('v14s-ninegates-all', 's_sun123zxy_ninegates_lean4')]
# ninegates: besides "lost 0", the word-size case split should convert the 14 facts blocked in the sample run (printed below).
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
G, B = load('v14s-ninegates-all'), load('s_sun123zxy_ninegates_lean4')
if G:
    newly = [k for k in G if k in B and B[k][5] != 'PROVED' and G[k][5] == 'PROVED']
    print(f"v14s-ninegates-all: newly PROVED {len(newly)} (expected 14); still not PROVED {sum(1 for k in G if G[k][5] != 'PROVED')}")
print("ALL PASS" if allok else "NOT ALL PASS")
