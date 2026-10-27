#!/usr/bin/env python3
"""Tables of the same-box Theorem 1.1 build (read-only): per module (GNU time: wall, user, sys, max RSS) and per part,
with the unit cgroup's CPU between the phase marks of phases.log. usage: t11_table_v1.py RUN_DIR OUT_DIR"""
import re, sys
from pathlib import Path

R, O = Path(sys.argv[1]), Path(sys.argv[2]); O.mkdir(parents=True, exist_ok=True)
ph = {}
jobs = ''
for l in (R / 'logs/phases.log').read_text().splitlines():
    m = re.match(r'(\S+) (\S+) cpu_usec=(\d+) jobs=(\d+) jobs_big=(\d+)', l)
    if m:
        ph[m.group(2)] = (m.group(1), int(m.group(3))); jobs = f"{m.group(4)} at once (the F_[ZX]_13 chunks {m.group(5)} at once)"
rows = []
for l in (R / 'logs/build.log').read_text().splitlines():
    c = l.split()
    m = c[0]
    part = ('native_final' if m in ('QEC/ChecksN/AllN', 'QEC/ChecksN/Thm11V2') else 'native_check' if m.startswith('QEC/ChecksN/')
            else 'kernel_final' if m in ('QEC/Checks/AllK', 'QEC/Checks/Thm11V3')
            else 'kernel_check_big' if re.match(r'QEC/Checks/F_[ZX]_13_', m) else 'kernel_check')
    rows.append((part, m, c[1], float(c[2]), float(c[3]), float(c[4]), int(c[5])))
(O / 't11_modules.tsv').write_text('part\tmodule\tstatus\twall_s\tuser_s\tsys_s\tmaxrss_kb\n' +
                                   ''.join(f"{p}\t{m}\t{s}\t{w:.2f}\t{u:.2f}\t{y:.2f}\t{k}\n" for p, m, s, w, u, y, k in rows))
seg = {'kernel_check': ('start', 'kernel_checks_done'), 'kernel_final': ('kernel_checks_done', 'kernel_final_done'),
       'native_check': ('kernel_final_done', 'native_checks_done'), 'native_final': ('native_checks_done', 'native_final_done')}
def cg(a, b):
    return (ph[b][1] - ph[a][1]) / 1e6
L = ['part\tmodules\tok\tcgroup_cpu_s\tsum_user_sys_s\tmax_module_wall_s\tmax_rss_gib\tphase_start\tphase_end']
groups = {'kernel_check': ('kernel_check_big', 'kernel_check'), 'kernel_final': ('kernel_final',),
          'native_check': ('native_check',), 'native_final': ('native_final',)}
tot = {}
for g, parts in groups.items():
    rs = [r for r in rows if r[0] in parts]
    a, b = seg[g]
    tot[g] = cg(a, b)
    L.append(f"{g}\t{len(rs)}\t{sum(r[2] == 'OK' for r in rs)}\t{cg(a, b):.1f}\t{sum(r[4] + r[5] for r in rs):.1f}\t"
             f"{max(r[3] for r in rs):.1f}\t{max(r[6] for r in rs) / 1048576:.2f}\t{ph[a][0]}\t{ph[b][0]}")
kv = tot['kernel_check'] + tot['kernel_final']; nv = tot['native_check'] + tot['native_final']
L += ['', f"kernel-only version (390 check modules + AllK + Thm11V3): cgroup CPU {kv:.1f} s = {kv / 3600:.3f} core-h, "
      f"wall {ph['start'][0]} to {ph['kernel_final_done'][0]}",
      f"native version (10 N_* modules + AllN + Thm11V2): cgroup CPU {nv:.1f} s = {nv / 3600:.4f} core-h, "
      f"wall {ph['kernel_final_done'][0]} to {ph['native_final_done'][0]}",
      f"parallelism: one lean process per module, LEAN_NUM_THREADS=1, nice 10; {jobs}"]
(O / 't11_summary.tsv').write_text('\n'.join(L) + '\n')
print('\n'.join(L))
