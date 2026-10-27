#!/usr/bin/env python3
"""Independent check of a whole kernel supplement written by `lake exe ntrust`, one supplement module at a time
(v2: projects whose modules cannot all be imported together). Run as ntbuild on the box.

usage: supp_check2.py OUT_DIR EXPORT_BIN [--jobs N] [--checkers DIR] [--mem GB]
For each supplement module K: export K's kernel theorems with their dependency closure (lean4export for the
project's toolchain), run nanoda (single-threaded; permitted axioms the standard three, any other a hard error) and
con-ron. Writes OUT_DIR/check2/<i>/... and OUT_DIR/check2/summary.tsv; an empty export never counts as a pass.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import concurrent.futures as cf, json, os, re, subprocess, sys, time
from pathlib import Path

out = Path(sys.argv[1]); exp = sys.argv[2]
arg = lambda k, d: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
checkers = arg('--checkers', (NT_BOX + '/elan/toolchains/leanprover--lean4---v4.35.0/bin'))
mem = int(arg('--mem', '64')); jobs = int(arg('--jobs', '8'))
cj = json.loads((out / 'comparator.json').read_text())
by = {}
for p in cj['pairs']:
    by.setdefault(p['kernel_module'], []).append(p['kernel_theorem'])
proj = Path(cj['project'])
tc = (proj / 'lean-toolchain').read_text().strip().split(':')[-1]
tcbin = Path((NT_BOX + '/elan/toolchains')) / f"leanprover--lean4---{tc}" / 'bin'
env = dict(os.environ); env['ELAN_HOME'] = (NT_BOX + '/elan')
env['PATH'] = f"{tcbin}:{NT_BOX}/elan/bin:" + env.get('PATH', '')
env['LEAN_PATH'] = ':'.join(cj['lean_path']); env['LEAN_NUM_THREADS'] = '1'
W = out / 'check2'; W.mkdir(exist_ok=True)


def sh(cmd, cwd, log, timeout=3600):
    with open(log, 'w') as f:
        return subprocess.run(['bash', '-c', f'ulimit -v {mem * 1024 * 1024}; ulimit -s unlimited; exec timeout -k 30 {timeout} "$@"', 'x'] +
                              [str(c) for c in cmd], cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT).returncode


def one(item):
    i, (mod, thms) = item
    w = W / str(i); w.mkdir(exist_ok=True)
    with open(w / 'k.export', 'w') as f, open(w / 'export.err', 'w') as e:
        p = subprocess.run(['bash', '-c', f'ulimit -v {mem * 1024 * 1024}; exec timeout 3600 "$@"', 'x', exp, mod, '--'] + thms,
                           cwd=w, env=env, stdout=f, stderr=e)
    cfg = {"export_file_path": str(w / 'k.export'), "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
           "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True,
           "print_success_message": True, "num_threads": 1}
    (w / 'nanoda.json').write_text(json.dumps(cfg))
    rcn = sh([Path(checkers) / 'nanoda_bin', w / 'nanoda.json'], w, w / 'nanoda.txt')
    rcc = sh([Path(checkers) / 'con-ron', w / 'k.export'], w, w / 'conron.txt')
    nt = (w / 'nanoda.txt').read_text(errors='ignore'); ct = (w / 'conron.txt').read_text(errors='ignore')
    mn = re.search(r'Checked (\d+) declarations with no typechecker errors', nt)
    mc = re.search(r'accepted (\d+) declarations', ct)
    dc = re.search(r'con-ron: declined: ([^\n]*)', ct)
    vn = 'PASS' if rcn == 0 and mn and int(mn.group(1)) > 0 else 'FAIL'
    vc = 'PASS' if rcc == 0 and mc and int(mc.group(1)) > 0 else ('DECLINED' if dc else 'FAIL')
    return f"{mod}\t{len(thms)}\t{p.returncode}\t{vn}\t{mn.group(1) if mn else 0}\t{vc}\t{mc.group(1) if mc else 0}\t{(dc.group(1)[:80] if dc else '')}"


t0 = time.time()
with cf.ThreadPoolExecutor(jobs) as ex:
    rows = list(ex.map(one, enumerate(sorted(by.items()))))
(W / 'summary.tsv').write_text('module\tkernel_theorems\texport_rc\tnanoda\tnanoda_decls\tcon_ron\tcon_ron_decls\tdeclined\n' + '\n'.join(rows) + '\n')
import collections
cn = collections.Counter(r.split('\t')[3] for r in rows); cc = collections.Counter(r.split('\t')[5] for r in rows)
nth = sum(int(r.split('\t')[1]) for r in rows)
print(f"modules={len(rows)} kernel_theorems={nth} nanoda={dict(cn)} con-ron={dict(cc)} s={time.time() - t0:.0f}")
