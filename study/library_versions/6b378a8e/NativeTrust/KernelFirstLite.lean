module

/-!
# Kernel first without `Lean`: `native_decide` that tries `decide +kernel`, as two macros

`import NativeTrust.KernelFirstLite` changes what every `native_decide` and `decide +native`
(written without further configuration) in the importing modules does, without editing any call:

1. the kernel evaluates `decide p` as `decide +kernel` does (same instance, same auxiliary lemma),
   within 2000 thousand heartbeats (deterministic);
2. if the kernel proves it, that is the proof: no native axiom, nothing trusted beyond the kernel;
3. otherwise Lean's own native path runs on the original call, so it behaves as before.

This module imports nothing but `Init`: the switch is two macros. Importers get no declaration,
instance or notation of `Lean` or `Std`, so the rest of their code elaborates exactly as before. (A
module that imports `Lean` passes `Std` on to every importer, module-system files included, whatever
the import modifiers: `Std.Data.DHashMap.Raw`'s `Singleton`/`Insert` instances, for instance, make
the structure-instance shorthand `{ a, b }` elaborate as set notation when its expected type is not
yet known.)

`NativeTrust.KernelFirst` is the same switch as elaborators, with what needs `Lean`: the options
`nativeTrust.kernelFirst`, `nativeTrust.kernelHeartbeats` and `nativeTrust.kernelFirst.report`, an
info message with the reason at each call that falls back, a static triage before evaluation, and
`#kernel_first_summary`. When it is loaded, the macros here leave every call to it.
-/

public meta section

namespace NativeTrust.KernelFirstLite

/-- The keyword atom of a fallback call. It has no source information, while a keyword written by a
user or produced by a quotation always has some; so the macros below recognize their own fallback
call and leave it to Lean's elaborator. -/
def fallbackKeyword (kw : String) : Lean.Syntax := .atom .none kw

/-- The atoms and identifiers of `stx`, in order. -/
partial def tokens : Lean.Syntax → Array String
  | .atom _ v => #[v]
  | .ident _ _ n _ => #[n.toString]
  | .node _ _ args => args.foldl (fun acc a => acc ++ tokens a) #[]
  | .missing => #[]

/-- Should the macros below leave the call `stx` alone: it is their own fallback call, it is written
with configuration (other than `+native` for `decide`), or `NativeTrust.KernelFirst` is loaded? The
call must consist of exactly the tokens `expected`. -/
def leaveAlone (stx : Lean.Syntax) (expected : Array String) : Lean.MacroM Bool := do
  if stx[0] matches .atom .none _ then return true
  if tokens stx != expected then return true
  Lean.Macro.hasDecl `NativeTrust.KernelFirst.evalNativeDecideKernelFirst

/-- `native_decide`: `decide +kernel` within the budget, else the original call. -/
@[macro Lean.Parser.Tactic.nativeDecide] def nativeDecideKernelFirst : Lean.Macro := fun stx => do
  if ← leaveAlone stx #["native_decide"] then Lean.Macro.throwUnsupported
  let tk := stx[0]
  let fb := fallbackKeyword "native_decide"
  `(tactic| first
    | set_option Elab.async false in set_option maxHeartbeats 2000 in decide%$tk +kernel
    | native_decide%$fb)

/-- `decide +native`: `decide +kernel` within the budget, else the original call. -/
@[macro Lean.Parser.Tactic.decide] def decideNativeKernelFirst : Lean.Macro := fun stx => do
  if ← leaveAlone stx #["decide", "+", "native"] then Lean.Macro.throwUnsupported
  let tk := stx[0]
  let fb := fallbackKeyword "decide"
  `(tactic| first
    | set_option Elab.async false in set_option maxHeartbeats 2000 in decide%$tk +kernel
    | decide%$fb +native)

end NativeTrust.KernelFirstLite

end
