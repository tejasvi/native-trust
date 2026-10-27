# minidregg's accessibility-fallback facts on library v14

In the random sample, three of minidregg's facts converted only through the accessibility fallback
(`study/results/sample/s_emberian_minidregg.ax.tsv`, reason `acc_fallback`). They were proved again with
library v14, built for minidregg's toolchain (Lean v4.30.0) from the library sources at the top of the artifact.
Each fact was run from the file written for it by the study's driver (`F2_…`, `split := 8`, `trace := true`), in its
own process with a 24 GiB memory limit. All three are PROVED with `acc_fallback=0`.

| file | fact | seconds | peak memory |
|---|---|---|---|
| `F2_Compiler_LegacyStoreCarryChecks_2` | `trailing_byte_refused` | 140.1 | 13.2 GiB |
| `F2_Compiler_LegacyStoreCarryChecks_5` | `truncated_source_refused` | 136.3 | 13.2 GiB |
| `F2_Compiler_StoreCodec_0` | `Worked.store32_compiled_roundtrip` | 4.7 | 3.8 GiB |

Earlier runs of the same facts without the fallback are in `../wt-final3-miniacc.ax.tsv` (the work build `0d9bca14`)
and `../wt-v9f-miniacc.ax.tsv` (library v10, `61dc5f97`).
