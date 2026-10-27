#!/usr/bin/env python3
"""task 3 (v2, for m2_axioms5_cg2.py): test of run() under drv_launch_v1.sh: (1) a 3 GiB allocation under a 1 GiB cap must be
OOM-killed (rc 137, cg_oom_kill=1); (2) a 1 s sleep under the same cap must exit 0 with cg_oom_kill=0; (3) a 5 s sleep
with a 2 s time limit must give rc 124. Prints PASS/FAIL per case and the log lines."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import importlib.util, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location('drv', (NT_BOX + '/work_resv8/box/qec/m2_axioms5_cg2.py'))
drv = importlib.util.module_from_spec(spec); spec.loader.exec_module(drv)
d = Path((NT_BOX + '/work_resv8/qec/cgtest2')); d.mkdir(parents=True, exist_ok=True)
cases = [('oom', ['python3', '-c', 'x = bytearray(3 << 30); x[::4096] = b"1" * len(x[::4096])'], 60, 1, 137, '1'),
         ('ok', ['sleep', '1'], 60, 1, 0, '0'),
         ('timeout', ['sleep', '5'], 2, 1, 124, '0')]
ok = True
for name, cmd, t, mem, want_rc, want_oom in cases:
    lg = d / f'{name}.log'
    if lg.exists(): lg.unlink()
    rc, secs = drv.run(cmd, d, None, t, mem, lg)
    txt = lg.read_text()
    oom = txt.rsplit('cg_oom_kill=', 1)[-1].strip()
    good = rc == want_rc and oom == want_oom
    ok &= good
    print(f"{'PASS' if good else 'FAIL'} {name}: rc={rc} (want {want_rc}) oom={oom} (want {want_oom}) | {txt.strip().splitlines()[-1]}")
left = list(Path(drv.CG_BASE).iterdir())
print('cgroups left:', [p.name for p in left if p.is_dir()])
print('ALL PASS' if ok else 'SOME FAIL')
