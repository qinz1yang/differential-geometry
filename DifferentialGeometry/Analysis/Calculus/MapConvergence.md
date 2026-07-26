# MapConvergence

## 2026-07-15 canonical placement

The generic definitions `mapDerivNorm`, `MapCPConvOn`, and
`MapCInfConvOnCompacts`, together with their elementary restriction,
subsequence, and uniform-convergence projections, now live in the analysis
calculus layer. Their namespace and public names are unchanged, so existing
HCG consumers retain source compatibility.

The HCG-path module remains a compatibility/Arzelà--Ascoli consumer. Focused
verification and the narrow compatibility refresh passed.
