import Lean

/-! Toolchain-dependent lookup of `@[csimp]` replacements (the compiler's table changed shape across
Lean versions). This version is for Lean v4.30 and later; drivers replace this file with
`CSimpCompatStub.lean.txt` on older toolchains, where the mismatch report then omits `@[csimp]`. -/

open Lean

namespace NativeTrust

/-- If the compiler replaces `c` by a `@[csimp]` theorem `thm : @c = @repl`, return `(repl, thm)`. -/
def csimpEntry? (env : Environment) (c : Name) : Option (Name × Name) :=
  ((Compiler.CSimp.ext.getState env).map.find? c).map fun ent => (ent.toDeclName, ent.thmName)

end NativeTrust
