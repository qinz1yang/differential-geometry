# RawConnLapLinear

## 2026-07-10: smooth-section linear producer

`rawConnLapLin` packages `rawTensorConnLapSmooth` as an `ℝ`-linear
endomorphism of `SmoothCcTensor g r s`.  Its additivity and homogeneity reuse
the bundled connection-Laplacian producers already consumed by
`connLaplacianL2Action`; no `L²` realization, continuity bound, or additional
geometric assumption is introduced.

`rawConnLapLin_apply` is the scalar-free application normal form for consumers.
The only proof adjustment needed was normalizing `LinearMap.map_smul'` from the
`RingHom.id` scalar action to the ordinary real scalar action before section
extensionality.

Focused verification passes.  This producer is complete (100%).  The final
moving-Laplacian `A2` continuous-linear-map theorem remains unstated and
unproved (0%); this lemma only supplies its canonical algebraic operator layer.
