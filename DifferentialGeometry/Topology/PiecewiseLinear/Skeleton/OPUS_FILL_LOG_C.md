# Opus fill log, lease c (`claude-agent-c-20260919`), 2026-09-22

## isCombinatorialSolidTorus_of_hasCylindricalDiagram — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/CombinatorialSolidTorusOfCylindricalDiagram.lean`
  (311 lines, SHA-256 `95F4FCA940308BA2A519A370824459359BA65893CF94E58FE23EEDC982D80378`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorusOfCylindricalDiagram`
- New public names (grepped tree-wide, unused before):
  `IsCylindricalDiagram.image_strip_inter_adjacent`, `IsCylindricalDiagram.image_strip_inter_ends`,
  `IsCylindricalDiagram.apply_notMem_image_strip`, `IsCylindricalDiagram.isClosed_image_strip`,
  `IsCylindricalDiagram.exists_simplicialComplex_slab`,
  `IsCylindricalDiagram.isCombinatorialSolidTorus`, and the leaf itself (statement byte-identical
  to `Skeleton/Section31CanonicalConfiguration.lean:395`). One private helper,
  `image_slab_ends_subset_boundaryComplex`, is a copy of the private
  `image_prism_ends_subset_boundaryComplex` of `CylinderCut.lean` (not reachable from outside).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CombinatorialSolidTorusOfCylindricalDiagram.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~13:38 local, -07:00).
- Axiom audit: `AuditOpusC1.lean` (Skeleton audit template, output root of lease c) —
  `Verified ...\AuditOpusC1.lean with no diagnostics; shared outputs unchanged.`: every
  declaration of the module has closure within `propext`, `Classical.choice`, `Quot.sound`, and the
  thirteen Batteries environment linters pass.
- Route: the general `IsCylindricalDiagram.isCombinatorialSolidTorus` (any PL two-ball `P`, any
  three-dimensional `F`) slices the diagram into the slabs over `[0,1/3]`, `[1/3,2/3]`,
  `[2/3,1]` (cycle graph of order 3 is complete; consecutive intersections are slice disks, the
  third is the glued end disk); a triangulation `M` of `S` is a combinatorial 3-manifold with
  boundary by `isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods` (middle slab over
  `[1/4,3/4]`, or `C₀ ∪ C₂` glued by `isPLBall_union_of_boundary_disk`); `M` lies in one large
  3-simplex (`exists_affineIndependent_openSimplex_superset`), hence
  `isOrientable_of_space_subset_convexHull` applies and
  `IsCylindricalDiagram.isTopologicalSolidTorus_of_isOrientable` excludes the reversed gluing.
- Gemini G007 blocker claim was FALSE: `isOrientable_of_space_subset_convexHull` needs only
  `K.space ⊆ convexHull T` with `T.card = n + 1`, and every compact set in `ℝ³` lies in the
  convex hull of four points; no new with-boundary orientability theorem was needed.
- Compiles: 4 module checks (≈15 s each) + 1 audit (≈50 s).

## exists_annulus_parametrization_of_product_circle_cut — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsAnnulusParametrizationOfProductCircleCut.lean`
  (298 lines, SHA-256 `1DD98B2C10B0B671F89BDE87C8449EB1C5E7B3A88EF2CC10D9E0FF9B990952E3`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut`
- New public names (grepped tree-wide, unused before): `IsPLSphere.exists_arc_between_adjacent_marks`
  (the reusable marked-circle helper: for at least two distinct marks on a PL circle and a point
  `s` off the marks, a PL arc `β : [0,1] → Q` between two distinct marks with `s ∈ β (0,1)`, no
  mark in `β (0,1)`, and `Q \ β (0,1)` closed) and the leaf itself (statement byte-identical to
  `Skeleton/Section28Annuli.lean:87`, same `local notation "E3"`). Private helper
  `exists_adjacent_marks_of_arc`.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsAnnulusParametrizationOfProductCircleCut.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~13:47 local, -07:00).
- Axiom audit: `AuditOpusC2.lean` — `Verified ...\AuditOpusC2.lean with no diagnostics; shared
  outputs unchanged.` (closure within `propext`, `Classical.choice`, `Quot.sound`; thirteen
  environment linters pass).
- Route: cut `Q` at two marks with `exists_arc_decomposition_of_isPLSphere_one`; on the arc `γ`
  through `s`, the marks form a finite subset of `[0,1]` containing `0, 1`, and the nearest marks
  `a < t₀ < b` around `s = γ t₀` give `β = γ ∘ σ` (`σ` affine onto `[a,b]`). With
  `ρ = f ∘ Prod.map id β`, `ρ (J × (0,1))` is connected and contains `x`; the compact sets
  `ρ (J × [0,1])` and `f (J × (Q \ β (0,1)))` cover `X` and meet only in marked fibres, so by
  `isPreconnected_iff_subset_of_disjoint_closed` it is the whole component; its closure is
  `ρ (J × [0,1])` by `IsPLHomeomorphOn.image_closure`, and the ends are the fibres over `β 0`, `β 1`.
- Gemini G025 blocker claim: TRUE as a statement about the tree (no `n`-point cyclic
  decomposition existed; `MarkedCircleSector.lean` only consumes arc covers), but it was not an
  obstruction: the two-point cut plus order on `[0,1]` gives the adjacent-marks arc, now the helper
  above.
- Compiles: 2 module checks (≈14 s each) + 1 audit (≈50 s).

## exists_triod_chart_at_common_boundary — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsTriodChartAtCommonBoundary.lean`
  (501 lines, SHA-256 `45C2F2DFB5BBEF6160ECFAF5CDFB16E8F491CF9287CAC7DABC92812236B03382`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsTriodChartAtCommonBoundary`
- New public names (grepped tree-wide, unused before): `smul_mem_linearHalfSpace`,
  `eq_of_eventually_sub_mem_iff`, `linearHalfSpace_inter_subset_of_eventually`,
  `IsCombinatorialManifoldWithBoundary.exists_mem_boundaryComplex_space_notMem`,
  `IsCombinatorialManifoldWithBoundary.exists_halfSpace_germ_of_mem_boundaryComplex`,
  `exists_isPLHomeomorphOn_triod_straightening`, and the leaf itself (statement byte-identical to
  `Skeleton/Section26ThreeSurfaces.lean:65`, same `open Classical in` and `local notation "E3"`).
  The two surface lemmas take the `DecidableEq` instance as a binder and substitute it by the
  classical one (`Subsingleton.elim`), so they apply to `E3`, whose `boundaryComplex` uses the
  `WithLp` instance.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsTriodChartAtCommonBoundary.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~14:06 local, -07:00).
- Axiom audit: `AuditOpusC3.lean` — `Verified ...\AuditOpusC3.lean with no diagnostics; shared
  outputs unchanged.` (closure within `propext`, `Classical.choice`, `Quot.sound`; thirteen
  environment linters pass).
- Route: `∂M₀` is a closed combinatorial 1-manifold (`isCombinatorialManifold_boundaryComplex`), so
  `B` contains an edge and a point `p` that is a vertex of no `M i`; there the carrier of `p` in
  each `M i` is a boundary edge with one coface, giving the germs `M i = p + linearHalfSpace D uᵢ`,
  `B = p + D` (`eventually_mem_space_iff_mem_codimension_one_cone`,
  `eventually_mem_space_iff_sub_mem_vectorSpan`); the three `D` agree and the half-planes meet only
  in `D` (disjoint interiors, scaling argument). Straightening: `exists_isPLHomeomorphOn_straighten_rays`
  (explicitly `h y = y + min (ℓ y) 0 • w₀`, positively homogeneous) makes `u₁` opposite to `u₀`,
  then the linear equivalence given by the basis `(u₀, h u₂, d)` sends the three half-planes onto
  the three coordinate pages; the chart is this global PL homeomorphism restricted to an open
  neighbourhood of `p` on which the germs hold.
- Gemini G012 blocker claim was FALSE: the tree already had the needed PL straightening
  (`exists_isPLHomeomorphOn_straighten_rays` and `exists_linearMap_eq_one_neg_of_disjoint` in
  `GeneralPosition.lean`, used by `TwoFoldCrossing.lean`); no sector-by-sector fan map was needed.
- Compiles: 2 module checks (≈15 s each) + 1 audit (≈35 s).


(Lead note 2026-09-22: module renamed to `CombinatorialSolidTorusOfCylindricalDiagram` because the import line of the original name exceeded 100 characters.)
