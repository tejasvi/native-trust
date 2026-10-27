#!/usr/bin/env python3
"""Generate the string-literal scaling test: Repro.lean's literal ("0 1 2 3 ..." cut to N chars) with
 A_N: the original path, theorem t : d.utf8ByteSize > 0 := by decide +kernel
 B_N: the same theorem after d is bridged to NativeTrust.ofListFast [chars] (String.ofList with the byte array built in
      one step instead of List.toByteArray's Array.push fold; ofList_eq_ofListFast is proved in StrFast.lean)
 Z:   the import baseline of the B files (import Lean, StrFast, the literal, no kernel check)
All files: import Lean (needed by the bridge's run_meta), maxHeartbeats 0, maxRecDepth 1000000."""
import sys
def lit(n):
    s, i = [], 0
    while len(" ".join(s)) < n:
        s.append(str(i)); i += 1
    return " ".join(s)[:n]
HDR = "import Lean\n{imp}set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nset_option Elab.async false\nopen Lean Meta Elab Command\n"
BRIDGE = '''run_meta do
  let some (.defnInfo di) := (← getEnv).find? ``d | throwError "no d"
  let .lit (.strVal s) := di.value | throwError "not a literal"
  let l := toExpr s.toList
  addDecl (.defnDecl {{ name := `d2, levelParams := [], type := mkConst ``String, value := mkApp (mkConst ``NativeTrust.ofListFast) l, hints := .abbrev, safety := .safe }})
  let ty ← mkEq (mkConst ``d) (mkConst `d2)
  addDecl (.thmDecl {{ name := `d_eq, levelParams := [], type := ty, value := mkApp (mkConst ``NativeTrust.ofList_eq_ofListFast) l }})
'''
for n in [500, 1000, 2000, 4000, 8000]:
    L = lit(n); assert len(L) == n
    dd = f'def d : String := "{L}"\n'
    if n <= 2000:
        open(f"A_{n}.lean", "w").write(HDR.format(imp="") + dd + "theorem t : d.utf8ByteSize > 0 := by decide +kernel\n#print axioms t\n")
    open(f"B_{n}.lean", "w").write(HDR.format(imp="import StrFast\n") + dd + BRIDGE.format() +
        "theorem t : d.utf8ByteSize > 0 := by rw [d_eq]; decide +kernel\n#print axioms t\n")
    open(f"Z_{n}.lean", "w").write(HDR.format(imp="import StrFast\n") + dd + BRIDGE.format() + "#print axioms d_eq\n")
print("ok")
