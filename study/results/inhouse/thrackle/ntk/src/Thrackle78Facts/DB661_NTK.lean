import Thrackle78Core.ReaderX
import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter3
import T78Data.DB661
import NativeTrust


/-! `CompFacts.db661`: the listing `lDB661` (as run) is not combinatorially thrackleable (native check of a
certificate with 6 filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db661 : ¬ CombThr (mkE 10 lDB661) :=
  not_combThr_mkE_of_checkI 10 lDB661 (by decide)
    [parseFilter (T78Data.db661f0c0.toUTF8),
      parseFilter (T78Data.db661f1c0.toUTF8),
      parseFilter (T78Data.db661f2c0.toUTF8),
      parseFilter (T78Data.db661f3c0.toUTF8),
      parseFilter (T78Data.db661f4c0.toUTF8
          ++ T78Data.db661f4c1.toUTF8
          ++ T78Data.db661f4c2.toUTF8
          ++ T78Data.db661f4c3.toUTF8
          ++ T78Data.db661f4c4.toUTF8),
      parseFilter (T78Data.db661f5c0.toUTF8)]
    (textReaderX (T78Data.db661mc0.toUTF8
          ++ T78Data.db661mc1.toUTF8
          ++ T78Data.db661mc2.toUTF8
          ++ T78Data.db661mc3.toUTF8
          ++ T78Data.db661mc4.toUTF8
          ++ T78Data.db661mc5.toUTF8
          ++ T78Data.db661mc6.toUTF8
          ++ T78Data.db661mc7.toUTF8)) (by kdecide (config := { native := false, split := 8 }))

end Thrackle78.Facts
