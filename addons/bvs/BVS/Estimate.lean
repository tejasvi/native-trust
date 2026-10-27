module

public import BVS.Driver.Select
public meta import BVS.Driver.Select

public meta section
/-!
# Cost estimate for `bv_kdecide`

`bvs5_estimate M` lists the `bv_decide` axioms of the imported module `M` (indices as in `bvs5_list`) with
the size of the kernel bit-blaster's CNF for each fact and an estimate of the time `bv_kdecide` (or
`bvs4_kernelize`) needs for it. Only compiled code runs (the bit-blaster on the problem `E` read from the
axiom); there is no SAT call and no kernel check, so the command takes about a second per module.

The estimate is `0.064 · clauses ^ 1.355` milliseconds, fitted on 127 facts of veir, clean, Natuvea and
asi-stack-book that took more than one second (median relative error 30 %, 90th percentile 71 %; Lean
v4.31.0 to v4.35.0-rc4, one thread). It is meant for budgeting a rewrite of `bv_decide` into `bv_kdecide`,
not as a bound. Each line also goes to standard error as
`BVS_ESTIMATE <module> <index> <axiom> <nodes> <clauses> <seconds>` (tab-separated).
-/
open Lean Meta Elab Command Std.Tactic.BVDecide

namespace BVS.Estimate

/-- Estimated `bv_kdecide` time in seconds for a kernel-bit-blaster CNF with `clauses` clauses. -/
def estimateSeconds (clauses : Nat) : Float :=
  0.064 * Float.pow (Float.ofNat clauses) 1.355 / 1000.0

elab "bvs5_estimate " id:ident : command => liftTermElabM do
  let m := id.getId
  let axs ← BVS.Driver5.bvdAxioms m
  let mut total : Float := 0
  for i in [0:axs.size] do
    let ax := axs[i]!
    let E ← BVS.Driver5.axiomE ax
    let bv ← unsafe evalExpr BVLogicalExpr (mkConst ``BVLogicalExpr) E
    if !supportedBool bv then
      logInfo m!"{i}: {ax}: unsupported by the kernel bit-blaster"
      BVS.Driver5.emit s!"BVS_ESTIMATE\t{m}\t{i}\t{ax}\t-\t-\tunsupported"
      continue
    let (st, out) := blastBool St.empty bv
    let clauses := (cnfOf st.es out).length
    let t := estimateSeconds clauses
    total := total + t
    logInfo m!"{i}: {ax}: {st.n} nodes, {clauses} CNF clauses; estimated bv_kdecide time {t.toString} s"
    BVS.Driver5.emit s!"BVS_ESTIMATE\t{m}\t{i}\t{ax}\t{st.n}\t{clauses}\t{t}"
  logInfo m!"{m}: {axs.size} bv_decide axioms; estimated bv_kdecide time in total {total.toString} s"

end BVS.Estimate
