import F_001
import F_006
import F_011
import F_012
import F_013
import F_014
import F_015
import F_036
import F_037
import F_038
import F_039
import F_040
import F_005
import F_010
import F_031
import F_032
import F_033
import F_034
import F_035
import F_056
import F_057
import F_058
import F_059
import F_060
import F_004
import F_009
import F_026
import F_027
import F_028
import F_029
import F_030
import F_051
import F_052
import F_053
import F_054
import F_055
import F_003
import F_008
import F_021
import F_022
import F_023
import F_024
import F_025
import F_046
import F_047
import F_048
import F_049
import F_050
import F_002
import F_007
import F_016
import F_017
import F_018
import F_019
import F_020
import F_041
import F_042
import F_043
import F_044
import F_045
import F_061
import QEC.ChecksN.Thm11V2
set_option maxHeartbeats 0
#native_facts QEC.Circ.thm11_circuit_native
kernelize QEC.Circ.thm11_circuit_native
#print axioms QEC.Circ.thm11_circuit_native
#print axioms QEC.Circ.thm11_circuit_native.kernel
open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let a := (env.find? `QEC.Circ.thm11_circuit_native).get!.type
  let b := (env.find? `QEC.Circ.thm11_circuit_native.kernel).get!.type
  logInfo m!"statements identical (Expr ==): {a == b}"
