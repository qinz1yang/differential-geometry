# BoundedGeometry

Source used: MSM135 Definition 3.8 and the bounded-curvature assumptions in Theorems 3.9 and 3.10.

Introduced definitions: `curvCovDerivStep`, `curvCovDeriv`, `curvDerivNormSq`, `curvDerivNorm`, `HasCurvDerivBound`, `BoundedGeometry`, `SeqBoundedGeometry`, `HasSpacetimeCurvBound`, `HasSpacetimeCurvDerivBound`, `SpacetimeCurvBound`, `FlowDerivBounds`, and `FlowDerivativeInput`.

Design note: bounded geometry is derivative-order indexed. `HasCurvDerivBound` is no longer an opaque predicate: it unfolds to a global pointwise bound on `curvDerivNorm`, defined from the canonical metric Riemann tensor, iterated `totalNabla0S`, and the metric-induced `normSq0S`. The flow derivative bound is a spacetime family of spatial curvature-derivative bounds on the time-slice metrics.

2026-05-27 correction, updated 2026-07-09: removed the vague curvature-bound axioms. The canonical conditional solution-compactness route needs `FlowDerivativeInput` and concrete `FlowUpgradeData`; the former exact-conclusion `SmoothFlowLimitInput` package has been deleted. The curvature-bound fields have concrete norm content.

Verification: passed.

2026-07-08 volume-comparison bridge: added `rm04Bound_of_curv0`,
`rm04Bound_of_geom`, and `rm04Bound_of_seq`.  These show that the zeroth-order
`HasCurvDerivBound`/`BoundedGeometry` inputs supply
`VolumeComparison.Rm04GlobalBound`, the named global Rm04 predicate consumed by
the local ball-volume comparison endpoint.  This is only the curvature-bound
producer bridge; it does not yet apply the full volume theorem to pointed
metric objects or instantiate `VolumeComparisonInput`.

Verification: passed for `BoundedGeometry.lean`.

2026-07-08 D6 input threading: added `SeqBoundedGeometry.subseq`, the
reindexing wrapper that carries uniform curvature-derivative bounds through a
subsequence.  This supports later D6 assembly after Step A/D diagonal
subsequences; it does not prove the volume-comparison producer from bounded
geometry.

Verification: passed for `BoundedGeometry.lean`.
