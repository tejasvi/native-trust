import Compiler.BendProofCshakeBoundedChecks
import Compiler.BendProofKeccakChecks
import Compiler.BendCommitmentFrameChecks
import Assurance.ObjectiveZkLiteralInstance
import Theory.NockCost
open Minidregg.Compiler
-- sizes of the arrays the kernel would build by `Array.push` (each push copies the list), and of the jam `cue` reads
#eval s!"cshake_bounded gates={(BendProofCshakeBounded.network BendProofCshakeBoundedChecks.domain 136).gates.size} inputs={(BendProofCshakeBounded.network BendProofCshakeBoundedChecks.domain 136).inputCount}"
#eval s!"keccak gates={BendProofKeccak.network.gates.size} inputs={BendProofKeccak.network.inputCount}"
#eval s!"frame gates={(BendCommitmentFrame.frameNetwork BendCommitmentFrameChecks.publicContext 4).gates.size}"
#eval s!"zk_literal_graph gates={Minidregg.Assurance.ObjectiveZkLiteralInstance.graph.gates.size}"
#eval s!"forge_jam bytes={Minidregg.Theory.NockCost.forgeJam.length}"
