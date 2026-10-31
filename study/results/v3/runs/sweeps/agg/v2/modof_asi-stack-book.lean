import AsiStackProofs.PrivacyInformationFlow
import AsiStackProofs.Replacement
import AsiStackProofs.SupplyChainIntegrity
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["AsiStackProofs.PrivacyInformationFlow.InformationRun", "AsiStackProofs.PrivacyInformationFlow.InformationRun._f", "AsiStackProofs.PrivacyInformationFlow.InformationStep", "AsiStackProofs.Replacement.ReplacementRun", "AsiStackProofs.Replacement.ReplacementRun._f", "AsiStackProofs.Replacement.ReplacementStep", "AsiStackProofs.SupplyChainIntegrity.SupplyChainRun", "AsiStackProofs.SupplyChainIntegrity.SupplyChainRun._f", "AsiStackProofs.SupplyChainIntegrity.SupplyChainStep"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
