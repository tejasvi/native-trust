import Kernel.Cpc.Proofs.Rules.Re_star_union_char

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some kidx := env.getModuleIdx? `Kernel.Cpc.Proofs.Rules.Re_star_union_char
    | IO.println "NOMODULE"
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut same := 0
  let mut defeq := 0
  let mut diff := 0
  let mut missing := 0
  let mut badAx := 0
  let mut origNative := 0
  for (k, ki) in env.constants.map₁.toList do
    if env.getModuleIdxFor? k != some kidx then continue
    if !(k matches .str _ "kernel") then continue
    let t := k.getPrefix
    if (← collectAxioms t).any (fun a => !std.contains a) then
      origNative := origNative + 1
    match env.find? t with
    | none =>
      missing := missing + 1
      IO.println s!"MISSING {t}"
    | some ti =>
      if ti.type == ki.type then
        same := same + 1
      else if (← liftTermElabM (Meta.isDefEq ti.type ki.type)) then
        defeq := defeq + 1
        IO.println s!"DEFEQ {t}"
      else
        diff := diff + 1
        IO.println s!"DIFF {t}"
    let axs ← collectAxioms k
    let bad := axs.filter (fun a => !std.contains a)
    if !bad.isEmpty then
      badAx := badAx + 1
      IO.println s!"AXIOMS {k} {bad.toList}"
  IO.println s!"STMT same={same} defeq={defeq} diff={diff} missing={missing} nonstd_axioms={badAx} control_originals_nonstd={origNative}"
