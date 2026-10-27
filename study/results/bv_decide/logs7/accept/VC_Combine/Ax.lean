import VC_Combine
import Veir.Passes.RISCVCombines.Combine
#print axioms bvs5fact_0.unsat
#print axioms bvs5fact_1.unsat
#print axioms bvs5fact_2.unsat
#print axioms bvs5fact_3.unsat
#print axioms bvs5fact_4.unsat
#print axioms bvs5fact_5.unsat
#print axioms bvs5fact_6.unsat
#print axioms bvs5fact_7.unsat
#print axioms bvs5fact_8.unsat
#print axioms bvs5fact_9.unsat
#print axioms bvs5fact_10.unsat
#print axioms bvs5fact_11.unsat
#print axioms bvs5fact_12.unsat
#print axioms bvs5fact_13.unsat
#print axioms bvs5fact_14.unsat
#print axioms bvs5fact_15.unsat
#print axioms bvs5fact_16.unsat
#print axioms bvs5fact_17.unsat
#print axioms bvs5fact_18.unsat
#print axioms bvs5fact_19.unsat
#print axioms bvs5fact_20.unsat
#print axioms bvs5fact_21.unsat
#print axioms bvs5fact_22.unsat
#print axioms bvs5fact_23.unsat
#print axioms bvs5fact_24.unsat
#print axioms bvs5fact_25.unsat
#print axioms bvs5fact_26.unsat
#print axioms bvs5fact_27.unsat
#print axioms bvs5fact_28.unsat
#print axioms bvs5fact_29.unsat
#print axioms bvs5_1
#print axioms bvs5_2
#print axioms bvs5_3
#print axioms bvs5_4
#print axioms bvs5_5
#print axioms bvs5_6
#print axioms bvs5_7
#print axioms bvs5_8
#print axioms bvs5_9
#print axioms bvs5_10
#print axioms bvs5_11
#print axioms bvs5_12
#print axioms bvs5_13
#print axioms bvs5_14
#print axioms bvs5_15
#print axioms bvs5_16
#print axioms bvs5_17
#print axioms bvs5_18
#print axioms bvs5_19
#print axioms bvs5_20
#print axioms bvs5_21
#print axioms bvs5_22
#print axioms bvs5_23
#print axioms bvs5_24
#print axioms bvs5_25
#print axioms bvs5_26
#print axioms bvs5_27
#print axioms bvs5_28
#print axioms bvs5_29
#print axioms bvs5_30
#print axioms bvs5_31
#print axioms bvs5_32
#print axioms bvs5_33
#print axioms bvs5_34
#print axioms bvs5_35
#print axioms bvs5_36
#print axioms bvs5_37
#print axioms bvs5_38
#print axioms bvs5_39
#print axioms bvs5_40
#print axioms bvs5_41
#print axioms bvs5_42
#print axioms bvs5_43
#print axioms bvs5_44
#print axioms bvs5_45
#print axioms bvs5_46
#print axioms bvs5_47
#print axioms bvs5_48
#print axioms bvs5_49
#print axioms bvs5_50
#print axioms bvs5_51
#print axioms bvs5_52
#print axioms bvs5_53
#print axioms bvs5_54
#print axioms bvs5_55
#print axioms bvs5_56
#print axioms bvs5_57
#print axioms bvs5_58
#print axioms bvs5_59
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs5_1 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh._proof_1 {(← getConstInfo (parseN "bvs5_1")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_2 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lh._proof_1 {(← getConstInfo (parseN "bvs5_2")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lh._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_3 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_andi._proof_1 {(← getConstInfo (parseN "bvs5_3")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_andi._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_4 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_andi {(← getConstInfo (parseN "bvs5_4")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_andi")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_5 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltiu._proof_1 {(← getConstInfo (parseN "bvs5_5")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltiu._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_6 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_zexth._proof_1 {(← getConstInfo (parseN "bvs5_6")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_zexth._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_7 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clzw._proof_1 {(← getConstInfo (parseN "bvs5_7")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clzw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_8 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clzw {(← getConstInfo (parseN "bvs5_8")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clzw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_9 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpop._proof_1 {(← getConstInfo (parseN "bvs5_9")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpop._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_10 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slti._proof_1 {(← getConstInfo (parseN "bvs5_10")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slti._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_11 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slti {(← getConstInfo (parseN "bvs5_11")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slti")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_12 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srli._proof_1 {(← getConstInfo (parseN "bvs5_12")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srli._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_13 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srli {(← getConstInfo (parseN "bvs5_13")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srli")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_14 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ori._proof_1 {(← getConstInfo (parseN "bvs5_14")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ori._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_15 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ori {(← getConstInfo (parseN "bvs5_15")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ori")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_16 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_zexth {(← getConstInfo (parseN "bvs5_16")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_zexth")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_17 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh {(← getConstInfo (parseN "bvs5_17")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_18 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srai._proof_1 {(← getConstInfo (parseN "bvs5_18")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srai._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_19 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srai {(← getConstInfo (parseN "bvs5_19")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_srai")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_20 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bext._proof_1 {(← getConstInfo (parseN "bvs5_20")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bext._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_21 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bext {(← getConstInfo (parseN "bvs5_21")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bext")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_22 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bexti._proof_1 {(← getConstInfo (parseN "bvs5_22")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bexti._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_23 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bexti {(← getConstInfo (parseN "bvs5_23")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_bexti")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_24 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sextb._proof_1 {(← getConstInfo (parseN "bvs5_24")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sextb._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_25 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sextb {(← getConstInfo (parseN "bvs5_25")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sextb")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_26 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sexth._proof_1 {(← getConstInfo (parseN "bvs5_26")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sexth._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_27 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sexth {(← getConstInfo (parseN "bvs5_27")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sexth")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_28 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltiu {(← getConstInfo (parseN "bvs5_28")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltiu")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_29 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clz._proof_1 {(← getConstInfo (parseN "bvs5_29")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clz._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_30 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clz {(← getConstInfo (parseN "bvs5_30")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_clz")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_31 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctz._proof_1 {(← getConstInfo (parseN "bvs5_31")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctz._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_32 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctz {(← getConstInfo (parseN "bvs5_32")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctz")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_33 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpop {(← getConstInfo (parseN "bvs5_33")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpop")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_34 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slt._proof_1 {(← getConstInfo (parseN "bvs5_34")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slt._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_35 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slt {(← getConstInfo (parseN "bvs5_35")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_slt")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_36 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltu._proof_1 {(← getConstInfo (parseN "bvs5_36")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltu._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_37 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltu {(← getConstInfo (parseN "bvs5_37")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_sltu")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_38 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctzw._proof_1 {(← getConstInfo (parseN "bvs5_38")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctzw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_39 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctzw {(← getConstInfo (parseN "bvs5_39")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_ctzw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_40 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpopw._proof_1 {(← getConstInfo (parseN "bvs5_40")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpopw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_41 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpopw {(← getConstInfo (parseN "bvs5_41")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_cpopw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_42 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lh {(← getConstInfo (parseN "bvs5_42")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lh")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_43 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lb._proof_1 {(← getConstInfo (parseN "bvs5_43")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lb._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_44 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lb {(← getConstInfo (parseN "bvs5_44")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lb")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_45 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lhu._proof_1 {(← getConstInfo (parseN "bvs5_45")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lhu._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_46 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lhu {(← getConstInfo (parseN "bvs5_46")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lhu")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_47 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lbu._proof_1 {(← getConstInfo (parseN "bvs5_47")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lbu._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_48 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lbu {(← getConstInfo (parseN "bvs5_48")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_lbu")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_49 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_sraw._proof_1 {(← getConstInfo (parseN "bvs5_49")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_sraw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_50 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_sraw {(← getConstInfo (parseN "bvs5_50")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_sraw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_51 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rolw._proof_1 {(← getConstInfo (parseN "bvs5_51")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rolw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_52 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_rolw {(← getConstInfo (parseN "bvs5_52")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_rolw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_53 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rorw._proof_1 {(← getConstInfo (parseN "bvs5_53")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rorw._proof_1")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_54 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_rorw {(← getConstInfo (parseN "bvs5_54")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_sextw_rorw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_55 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_sraw {(← getConstInfo (parseN "bvs5_55")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_sraw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_56 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rolw {(← getConstInfo (parseN "bvs5_56")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rolw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_57 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rorw {(← getConstInfo (parseN "bvs5_57")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.drop_zextw_rorw")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_58 _private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.Combine.impl {(← getConstInfo (parseN "bvs5_58")).type == (← getConstInfo (parseN "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.Combine.impl")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_59 Veir.RISCV.Combine {(← getConstInfo (parseN "bvs5_59")).type == (← getConstInfo (parseN "Veir.RISCV.Combine")).type}"
  pure ()
