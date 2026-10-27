#!/usr/bin/env python3
"""Generate the BerryOpt modules for one cover fact.
usage: gen_cover.py TAG MODULE LEAVES BATCH OUTDIR
  TAG     short name, e.g. C3 (Lean prefix BerryOpt.<TAG>, files BO_<TAG>_*.lean)
  MODULE  package module, e.g. BerryEsseen.Upper0423.Small.Data.Cover3 (fact MODULE.accepted, data MODULE.data)
  LEAVES  number of leaves; BATCH leaves per leaf module
Writes OUTDIR/BO_<TAG>_Tree.lean, _Parse.lean, _L<j>.lean, _All.lean, F2_<TAG>.lean and OUTDIR/batches.txt."""
import sys, os
tag, mod, leaves, batch, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
os.makedirs(out, exist_ok=True)
P = f"BerryOpt.{tag}"
F = f"{mod}.accepted"
hdr = "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
def w(name, txt):
    open(os.path.join(out, name), 'w').write(txt)
w(f"BO_{tag}_Tree.lean", f"import BoCore\nimport {mod}\n{hdr}bo_tree {P} {mod}.data\n")
w(f"BO_{tag}_Parse.lean", f"import BO_{tag}_Tree\n{hdr}bo_parse {P} {F}\n#print axioms {P}.parse\n")
nb = (leaves + batch - 1) // batch
names = []
for j in range(nb):
    a, b = j * batch, min(leaves, (j + 1) * batch)
    w(f"BO_{tag}_L{j}.lean", f"import BO_{tag}_Tree\n{hdr}bo_leaves {P} {F} {a} {b}\n")
    names.append(f"BO_{tag}_L{j}")
imps = ''.join(f"import {n}\n" for n in [f"BO_{tag}_Parse"] + names)
w(f"BO_{tag}_All.lean", f"import NativeTrust\n{imps}{hdr}bo_assemble {P} {F}\nattribute [kernel_fact] {P}.final\n#print axioms {P}.final\n")
w(f"F2_{tag}.lean", f"import NativeTrust\nimport {mod}\nimport BO_{tag}_All\nset_option Elab.async false\n{hdr}"
  f"set_option nativeTrust.eprint true\nprove_native_axiom_nth {mod} 0 (config := {{ split := 1, trace := true }})\n")
open(os.path.join(out, 'batches.txt'), 'w').write('\n'.join(names) + '\n')
print(tag, mod, 'leaves', leaves, 'batches', nb)
