import NativeTrust
import KzNative
open NativeTrust

#print axioms combined
kernelize combined
#print axioms combined.kernel
kernelize sorted_check as sorted_check_k
#print axioms sorted_check_k
-- the statement is the original one, expression for expression
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  for (a, b) in [(``combined, ``combined.kernel), (``sorted_check, `sorted_check_k)] do
    let ta := (env.find? a).get!.type
    let tb := (env.find? b).get!.type
    Lean.logInfo m!"{a} and {b} have identical statements: {ta == tb}"
