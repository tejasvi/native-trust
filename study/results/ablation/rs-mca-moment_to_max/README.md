# rs-mca's conversion that made copies, checked again

Of rs-mca's conversions by the earlier per-theorem driver, one made copies: the auxiliary theorem
`MomentToMax.PTEClusterPacking.champion_packingStats._proof_1_1` (theorem 1 of `#native_theorems` in its module;
`study/results/m2/pertheorem_logs/rs-mca-moment_to_max/`, `copies=6`). It was checked again three times on Lean v4.28.0
(the package's toolchain), with the same command as in its run (`trust_check_nth`, `split := 8`, trace on). Each check
ran in its own process with a 64 GiB memory limit:

| file | build | setting | result |
|---|---|---|---|
| `chk4_wfoff` | the build used in the study's run (accessibility route) | `wf := false` | not converted: the kernel does not reduce the check to `true` |
| `chk4_wfon` | the same | as in the study | converted, 6 copies, 894 s |
| `chk4_fuel` | `e839bc05` (the fuel route with its retry) | `accFallback := false` | converted, 6 copies, `acc_fallback=0`, 825 s |

Without the replacement of `WellFounded.fix` the fact does not convert, so its evaluation reaches a definition
compiled through well-founded recursion; with the fuel route it converts without the accessibility fallback. The six
copies (listed in the trace of `chk4_fuel`) are core's `List.merge._unary`, `List.merge`, `List.mergeSort._unary` and
`List.mergeSort`, and the package's `packingStats` and `champion_packingStats._nativeDecide_1_1`.
