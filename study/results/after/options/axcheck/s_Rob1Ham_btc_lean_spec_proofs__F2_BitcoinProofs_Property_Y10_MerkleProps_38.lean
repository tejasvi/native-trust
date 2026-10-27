import NativeTrust
import BitcoinProofs.Property.Y10.MerkleProps
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth BitcoinProofs.Property.Y10.MerkleProps 38 (config := { stage := true, trace := true })

#print axioms _ktr.s_Rob1Ham_btc_lean_spec_proofs__F2_BitcoinProofs_Property_Y10_MerkleProps_38.BitcoinProofs.Property.Y10.MerkleProps.casea24._kernel.native_decide.ax_1_1
