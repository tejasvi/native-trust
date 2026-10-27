# BerryEsseen add-on

Proved replacements that let NativeTrust evaluate BerryEsseen's cover certificates in the kernel.
The package stores each cover as a string literal and parses it inside the decided term; these
modules restate the parse on lists and register the replacements. The add-on uses toolchain
`v4.34.0-rc2`, the version the package pins; `BeList`, `BeObs` and `BeSplitL` import the package's
`BerryEsseen.Upper0423.Native.CoverGen`.

| file | contents |
|---|---|
| `SplitOnSpace.lean` | legacy `String.splitOn` on a one-character separator equals `List.splitOn` on `toList` (core only) |
| `StrReplace.lean` | `String.replace` with a one-character pattern as a map on `toList` (core only) |
| `StrRepl.lean` | list-based replacements for the iterator-based `String.toNat?`, `String.toInt?` and related functions |
| `BeList.lean` | the whole cover parse on `List Char`: no `String` operation and no string literal |
| `BeObs.lean` | cover acceptance as `List.all` over the list of obligations, so that NativeTrust's `split` can cut the check into pieces |
| `BeSplitL.lean` | the forms NativeTrust rewrites to, for a data literal: `coverStringAccepted* … data` becomes `obsAccepted*L … [c₁, …]` |
