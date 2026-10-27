import NativeTrust
import StrRepl
import BerryEsseen.Upper0423.Native.CoverGen

set_option Elab.async false
-- with the StrRepl replacements registered
#kernel_blockers_const BerryEsseen.Upper0423.Native.parseRat
#kernel_blockers_const BerryEsseen.Upper0423.Native.parseCover
#kernel_blockers_const BerryEsseen.Upper0423.Native.tokens
#kernel_blockers_const BerryEsseen.Upper0423.Native.coverAcceptedBE
#kernel_blockers_const BerryEsseen.Upper0423.Native.coverAccepted
