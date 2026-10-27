import NTBobDeq
open Lean Meta
#print axioms NTBob.decideEquality_eq_decC
#eval show MetaM Unit from do
  for n in [``NTBob.decB, ``NTBob.decA, ``NTBob.decL, ``NTBob.decC] do
    let some (.defnInfo d) := (← getEnv).find? n | IO.println s!"{n}: not a defn"
    let cs := d.value.getUsedConstants
    IO.println s!"{n}: WF.fix={cs.contains ``WellFounded.fix} brecOn={cs.any (fun c => (c.toString.splitOn "brecOn").length > 1)} consts={cs.size}"
  let st := NativeTrust.kernelReplaceExt.getState (← getEnv)
  IO.println s!"kernel_replace entries: {st.toList.map (·.1)}"
