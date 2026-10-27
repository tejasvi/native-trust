import NativeTrust
import StrRepl
import BerryEsseen.Upper0423.Covers.Data.DW21
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open BerryEsseen.Upper0423.Native

/-- `tokens` without its `String.replace "\n" " "` step (diagnostic only). -/
def tokensNR (s : String) : List String := (s.splitOn " ").filter fun t => !t.isEmpty

def accBE (n : Nat) (blo bhi : Rat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAcceptedBE n blo bhi 0 1 cov
  | _ => false

def accDW (n : Nat) (dlo dhi : Rat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAccepted n dlo dhi 0 1 cov
  | _ => false

def acc0 (n : Nat) (data : String) : Bool :=
  match parseCover 64 (tokensNR data) with
  | some (cov, []) => coverAccepted n 0 deltaMax 0 1 cov
  | _ => false

theorem diag_6 : (accDW 21 (258569/454000 : Rat) (1 : Rat) BerryEsseen.Upper0423.Covers.Data.DW21.data && !(BerryEsseen.Upper0423.Covers.Data.DW21.data.toList.contains '\n')) = true := by
  kdecide (config := { native := false })

#print axioms diag_6
