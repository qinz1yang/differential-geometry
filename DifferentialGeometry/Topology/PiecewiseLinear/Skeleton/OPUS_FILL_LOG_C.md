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

# Batch 2

## exists_isPLBall_superset_of_exterior_compression — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsIsPLBallSupersetOfExteriorCompression.lean`
  (536 lines, SHA-256 `a7b0c88695042087e75a108fcbcc121227e827d3810acf29291604f0a3f8c315`).
- Import line to register (96 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression`
- New public names (grepped tree-wide, unused before):
  `IsPreconnected.subset_interior_of_disjoint_frontier` (in the PL namespace),
  `IsCombinatorialManifoldWithBoundary.subset_closure_interior_space` (a finite combinatorial
  `n`-manifold with boundary in `n`-space is regular closed),
  `IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifold_space_eq_frontier`,
  `IsCombinatorialManifold.isPLSphere_closure_sdiff_union_of_bettiOne_le_two` (compressing a
  closed connected surface with `β₁ ≤ 2` along an essential annulus-and-caps datum gives a PL
  two-sphere; the separating case is excluded by positivity and evenness of `β₁`),
  `IsPLTorus.isPathConnected`, `IsPLTorus.bettiOne_le_two`,
  `IsPLSphere.exists_isPLBall_eq_of_isOpen_sdiff` (a compact `X ⊇ S` with `X \ S` open and
  nonempty is the Schoenflies ball of `S`), `IsPLSphere.isPLBall_of_isOpen_sdiff`,
  `IsPLBall.exists_isPLBall_subset_interior_of_isOpen` (a PL three-ball inside an open `U ⊆ ℝ³`
  lies in the interior of a PL ball inside `U`), and the leaf itself (statement byte-identical to
  `Skeleton/Section30Torus.lean:97`, checked by string comparison after CRLF normalization).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsIsPLBallSupersetOfExteriorCompression.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 14:40 local, -07:00).
- Axiom audit: `AuditOpusC4.lean` (covers this module and the next) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC4.lean with no diagnostics;
  shared outputs unchanged.` (14:44): closure within `propext`, `Classical.choice`, `Quot.sound`;
  the thirteen environment linters pass.
- Route: `K = ∂R` (boundary complex) is a closed connected surface with `β₁(K) ≤ 2` (the torus
  homeomorphism gives `π₁ ≅ ℤ²`, then `fieldSingularHomology_one_finrank_le_of_fundamentalGroup_injective`).
  `exists_compression_neighborhood_of_spanning_disk` inside `U` gives the prism ball `N`, wall
  `W = K ∩ N`, caps `D₀, D₁`; `exists_annulus_complement` + `exists_capped_annulus_complement`
  (or `exists_capped_pair_of_separating_essential_annulus`, refuted by `β₁` parity) make
  `Σ = cl(K \ W) ∪ D₀ ∪ D₁` a PL sphere. `int N` is connected, misses `K`, and contains
  `D \ ∂D ⊆ Rᶜ`, so `N ∩ int R = ∅`. At a point of `W \ Σ`, the two local sides from
  `exists_connected_neighborhood_pair_sdiff` meet `int N` and `int R` respectively (both sets are
  regular closed), hence lie in them; so `(R ∪ N) \ Σ` is open and Schoenflies uniqueness gives
  `R ∪ N` = the ball of `Σ`. Enlargement: `Σ` is simply embedded; the ambient PL homeomorphism `h`
  takes `R ∪ N` onto a simplex `Δ`, and `h⁻¹` of the dilation of `Δ` about its centroid by
  `1 + ε/(|M|+1)` (thickening of `Δ` inside `h(U)`) is the output ball.
- Gemini G017 blocker claim was FALSE: 3D Schoenflies is unconditional
  (`IsPLSphere.exists_isPLBall_frontier_eq`, `IsPLSphere.isSimplyEmbedded`), and the compression
  neighbourhood already existed (`SpanningDiskCompression.lean`); no regular-neighbourhood theory
  was needed beyond the side identification above.
- Compiles: 4 module checks (≈15–20 s each).

## exists_ball_pair_of_interior_essential_disk — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsBallPairOfInteriorEssentialDisk.lean`
  (310 lines, SHA-256 `73ead0eb0e3cc037df6536115d2091525cc9fcad6b024048bbec48e4cec8d644`);
  imports the previous module.
- Import line to register (90 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsBallPairOfInteriorEssentialDisk`
- New public names: the leaf only (statement byte-identical to `Skeleton/Section30Torus.lean:112`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsBallPairOfInteriorEssentialDisk.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~14:42 local).
- Axiom audit: `AuditOpusC4.lean`, as above.
- Route: same `K`, `Σ` and compression ball `N` (with `U = univ`); now `D \ ∂D ⊆ int R` forces
  `int N ⊆ int R`, so `N ⊆ R`. The balls are `A = N` and `B = cl(R \ N) ∪ D₀ ∪ D₁`. At a point
  of `W \ Σ` the local side meeting `int N` lies in it and the other lies in `Rᶜ`, so the point
  is not in `cl(R \ N)`; hence `B \ Σ = int R \ N` (open, nonempty because `K \ W ≠ ∅` by
  connectedness of `Σ`) and `B` is the ball of `Σ`. `A ∩ B = D₀ ∪ D₁` uses
  `W ∩ cl(K \ W) = ρ(J × {±1}) ⊆ D₀ ∪ D₁` from `exists_annulus_complement`.
- Gemini G018 blocker claim was FALSE: no solid-torus recognition or cylindrical diagram is
  needed; the cut remainder is identified as a ball directly by Schoenflies.
- Compiles: 1 module check (≈20 s).

## exists_annular_split_ball — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsAnnularSplitBall.lean`
  (448 lines, SHA-256 `f0b5c70e9fed3d060c54740c11776c71e12e1243fbe4488d9dae11c62522a054`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall`
- New public names (grepped tree-wide, unused before):
  `isPLSphere_union_of_inter_eq_image_stdSimplexBoundary` (two PL disks meeting exactly in
  their common rim form a PL two-sphere), `IsPLHomeomorphOn.image_image_stdSimplexBoundary`
  (a PL homeomorphism of PL disks carries rim onto rim), `IsPLBall.exists_prism_of_disjoint_frontier_disks`
  (a PL three-ball with two disjoint disks `D₀, D₁` in its frontier is a prism `P × [0,1]`
  from `D₀` to `D₁`, with the frontier formula), and the leaf itself (statement byte-identical to
  `Skeleton/Section30Separation.lean:60`, same nested namespaces and `local notation "E3"`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsAnnularSplitBall.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 15:01 local).
- Axiom audit: `AuditOpusC5.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC5.lean with no diagnostics;
  shared outputs unchanged.` (15:02): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- LEAD DECISION: the hypotheses `hM`, `hCM`, `hC`, `hΔC`, `hΩM` of the frozen statement are not
  needed by the leaf (only by the `moise303` assembly). The compiler's unused-variable linter
  rejected them, so the proof begins with `let _ := hM` … `let _ := hΩM` (the AGENTS.md
  `unusedArguments` pattern). The leaf could be restated without `M`, `hM`, `hCM`, `hC`, `hΔC`,
  `hΩM` (a strictly stronger statement); then these five lines go.
- Route: ambient `K` = a triangulated 3-simplex containing `D₁ ∪ D₂` in its interior,
  `U = Ω ∩ int K`; `exists_surface_split_local_traces_with_side_trace` gives `N ⊆ U`, the cut
  ball `B ⊆ N` with `∂B = E₂ ∪ Δ'` (`E₂ = D₂ ∩ N`), `C ∩ B = E₂ ∪ A'`, the disk `D₁ ∩ N` with rim
  `J₁ ⊆ ∂B \ E₂`. `IsPLSphere.exists_isPLBall_with_boundary_disjoint_of_isPreconnected` on the
  sphere `∂B` gives the small disk `Δ₁ ⊆ ∂B` bounded by `J₁` and disjoint from `E₂`; then
  `(D₁ ∩ N) ∩ Δ₁ = J₁`, so `(D₁ ∩ N) ∪ Δ₁` is a PL sphere; its Schoenflies ball `W` has a prism
  structure `G' : Δ × [0,1] → W` from `Δ` to `Δ₁`, and `A₁ := G'(∂Δ × [0,1])` is the annulus
  (ends `∂Δ`, `G'(∂Δ × {1}) = J₁` by rim invariance). A second prism structure
  `G : E₂ × [0,1] → B` from `E₂` to `Δ₁` gives `ψ = G`, `J = ∂E₂`, and the safe boundary
  `G(∂E₂ × (0,1))`; `Q = B`, `O = int B`.
- Gemini G055 blocker claim ("missing joint PL regular-neighbourhood construction") was FALSE:
  the joint construction exists (`SurfaceSplitLocalTrace.lean`); the missing pieces were the
  small disk (sphere disk-pair API) and the two prism structures (`PrismDiskPair.lean`,
  `PrismFrontier.lean`).
- Compiles: 4 module checks (≈20–25 s each) + 1 audit.

## exists_generalPosition_solidTorus_relative — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsGeneralPositionSolidTorusRelative.lean`
  (400 lines, SHA-256 `88eea94be977b25b8020a05d9e87aa88c20e69e36217b0192f5f51f179578011`).
- Import line to register (92 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative`
- New public names (grepped tree-wide, unused before): `IsPolyhedron.frontier`,
  `IsCombinatorialSolidTorus.isPolyhedron`, `IsCombinatorialSolidTorus.image_homeomorph` (image
  under an ambient PL homeomorphism), `exists_isPLSphere_cover_inter_of_transverse_faces` (two
  closed combinatorial surfaces with transverse faces cross at every common point and meet in a
  finite disjoint union of PL circles), `notMem_interior_of_homeomorph_closedBall_prod_sphere`,
  `mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere`,
  `IsTopologicalSolidTorus.nonempty_homeomorph_frontier`,
  `IsCombinatorialSolidTorus.isPLTorus_frontier`, and the leaf itself (statement byte-identical
  to `Skeleton/Section31CanonicalConfiguration.lean:403`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsGeneralPositionSolidTorusRelative.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~15:18 local).
- Axiom audit: `AuditOpusC6.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC6.lean with no diagnostics;
  shared outputs unchanged.` (15:19): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: the frontier of a combinatorial solid torus is a PL torus (polyhedron: `S ∩ cl(Δ \ S)`
  with `IsPolyhedron.closure_sdiff`; homeomorphic to `S¹ × S¹`: `|b| < 1` points are interior by
  `mem_interior_of_homeomorph_closedBall_prod_sphere`, `|b| = 1` points are not, by
  `invariance_of_domain_isOpen_image_of_finrank_eq` applied to `x ↦ ((2 + b₀)θ, b₁)` and the
  points `((2 + t b₀)θ, t b₁)`, `t ↓ 1`); `isCombinatorialManifold_two_of_homeomorph_sphere_prod`
  makes every triangulation of such a frontier a combinatorial surface.
  `exists_simplicialComplex_space_iUnion` triangulates all `∂F i` at once as subcomplexes of one
  `R`; `exists_small_homeomorph_transverse_affineImage` (with `ε` below the thickening margins of
  `S₀ ⊆ U` and `A ⊆ int S₀`) gives `h` with `h(∂S₀)` transverse to every face of `R`; then
  `exists_triangulation_inter_of_transverse_faces`, `neighbors_eq_pair_of_transverse_face` (empty
  boundary complexes) and the graph components of `OneManifoldComponents` give the circles, and
  `hasPLCrossingAt_of_transverse_faces` the crossings. `S = h(S₀)`.
- Gemini G020 blocker claim ("general position existing only for 1-complexes and singular
  2-cells") was FALSE: `GeneralPosition.lean` already has ambient transversality of two finite
  complexes (`exists_small_homeomorph_transverse_affineImage`) and the transverse-surface
  intersection theory; the missing input was that combinatorial solid tori have PL-torus frontiers.
- Compiles: 2 module checks (≈25 s each) + 1 audit.

# Batch 3

## exists_innerSolidTorus_toroidalShell_of_annulusImage — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/InnerSolidTorusToroidalShell.lean`
  (352 lines, SHA-256 `cb4faceb7fb6671b48c4a5bc3f78c811a820a55461b9e5887a7149d371a6e352`).
- Import line to register (81 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.InnerSolidTorusToroidalShell`
- New public names (grepped tree-wide, unused before):
  `IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior` (for any
  topological solid torus `Y ⊆ ℝ³` and compact `K ⊆ interior Y`: a topological solid torus `S₁`
  with `K ⊆ interior S₁`, `S₁ ⊆ interior Y` and
  `IsToroidalShell (closure (Y \ S₁)) (frontier S₁) (frontier Y)`), and the leaf itself (statement
  byte-identical to `Skeleton/Section31CanonicalConfiguration.lean`, checked by string comparison
  after CRLF normalization). Private helpers: `isCompact_revolutionOf_of_isCompact` (a renamed
  copy of the skeleton's public `isCompact_revolutionOf`, which cannot be imported; renamed so the
  skeleton can import this module without a clash — the lead may hoist one public copy later) and
  `smul_mem_closedBall_zero_one`.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\InnerSolidTorusToroidalShell.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~15:39 local).
- Axiom audit: `AuditOpusC7.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC7.lean with no diagnostics;
  shared outputs unchanged.` (15:40): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route (not the reviewer's revolution route; no planar cell geometry is needed): `Y = h '' S j`
  is a topological solid torus through the embedding `h|S j`; by
  `mem_interior_of_homeomorph_closedBall_prod_sphere` / `notMem_interior_of_homeomorph_closedBall_prod_sphere`
  (invariance of domain) the interior points of a solid torus `φ : Y ≃ D² × S¹` are exactly those
  with `|b| < 1`, and the frontier those with `|b| = 1`
  (`mem_frontier_iff_norm_eq_one_of_homeomorph_closedBall_prod_sphere`). So
  `K = h '' A j` (compact: revolved segment) lies over `|b| ≤ m < r < 1`;
  `S₁ = φ⁻¹(D(0,r) × S¹)` (the range of a continuous injection of a compact space, hence a
  homeomorphic copy), and `((u, θ), s) ↦ φ⁻¹((r + s(1 - r)) u, θ)` is the toroidal shell: its
  range is `{r ≤ |b|}`, which is `closure (Y \ S₁)` (the level `s = 0` is a limit of `s ↓ 0`), and
  its ends are `frontier S₁` and `frontier Y` by the frontier characterisation applied to `S₁` and
  to `Y`.
- Compiles: 3 module checks (≈20 s each; one heartbeat timeout in a continuity unification, fixed
  by making `Ψ = val ∘ φ.symm` opaque) + 1 audit.

## carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier — STUCK

- File: `DifferentialGeometry/Topology/PiecewiseLinear/CarriesGeneratorOrIsPLCellOfDisjointCarrier.lean.wip`
  (not a module; no import line, no registered names). Proposed sub-leaf names (grepped, unused):
  `IsCombinatorialSolidTorus.exists_isPLCell_frontier_of_not_isPreconnected_sdiff` (separating
  case = Moise 28.9 on the boundary torus) and
  `IsCombinatorialSolidTorus.carriesFundamentalGroupOnto_of_isPreconnected_sdiff` (nonseparating
  case). The leaf is a two-line `by_cases` on `IsPreconnected (frontier S \ G)` from them.
- Check: external probe `claude-moise-agent-c/ProbeTorusCurveReduction.lean` (both reductions of
  this leaf and the next, frozen statements verbatim): exactly three `declaration uses 'sorry'`
  warnings (the three sub-leaves), nothing else. No audit (not closed).
- Statement: TRUE (no counterexample: an essential `G` disjoint from the essential `K` is parallel
  to it; an inessential one bounds a disk). The case split is not the obstacle.
- Stuck goal 1 (separating case, 28.9): a PL circle `G` with `¬ IsPreconnected (frontier S \ G)`
  bounds a PL disk in `frontier S`. Everything but one case is available: triangulation `L`
  (`IsPLTorus.exists_combinatorial_triangulation`, `isOrientable_euclidean_three`),
  `χ(L) ∈ {0, 2}` (`IsPLTorus.bettiOne_le_two`, `eulerChar_eq_two_sub_bettiOne_of_isOrientable`,
  `even_eulerChar_of_finrank_eq_three`), sides `A, B` (`exists_manifold_pair_of_separating_circle`,
  `χ(A) + χ(B) = χ(L)`), cone caps in `E × ℝ` (`exists_cone_disk_of_isPLSphere_one`,
  `exists_closed_of_disk`) giving `χ ≤ 1` per side, and "`χ = 1` side is a PL disk"
  (`isPLSphere_two_of_faceEulerChar_eq_two`, `IsPLSphere.isPLBall_closure_sdiff`). The case
  `χ(A) = χ(B) = 0` needs the parity fact "an orientable surface with one boundary circle has odd
  `χ`". The tree has parity only for closed surfaces in three-space; capped sides live in `E × ℝ`,
  and there is no lemma that capping preserves orientability (`IsOrientable.double` is the only
  gluing result). With a capping-orientability lemma the case closes by a short argument (an
  orientable closed surface with `χ ≠ 2` has a nonseparating circle,
  `exists_isPLSphere_one_isPreconnected_sdiff`; its annulus complement capped twice has
  `χ + 2 ≤ 2`).
- Stuck goal 2 (nonseparating case; no parity needed, routine but long, est. 800–1200 lines):
  annulus complement of `G` avoiding `K` (`exists_connected_annulus_complement`) is an annulus
  (`exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero`); in the prism sphere, the disk
  decomposition of `K` (`exists_disk_decomposition_of_isPLSphere_one_subset_two`) either puts both
  end disks on one side (then `K` bounds a PL disk, is null in `S`, contradicting `hKgen` since
  `π₁(S) ≅ ℤ`) or separates them (then `exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk` makes
  `K` and an end circle the ends of a PL annulus); missing only the transfer "the two ends of an
  annulus in `S` carry `π₁(S)` together" (square homotopy in `C × I`, `Path.Homotopic.prod`).
  Cutting along `K` instead of `G` avoids goal 1 but needs "a generator-carrying boundary circle
  does not separate the torus", whose last case is the same parity fact (or `H₁(·; ℤ/2)`).
- Compiles: 1 external probe (≈40 s).

## exists_isPLCell_frontier_of_polygon_nullhomotopic — STUCK

- File: `DifferentialGeometry/Topology/PiecewiseLinear/IsPLCellFrontierOfPolygonNullhomotopic.lean.wip`
  (imports the previous WIP module). Proposed sub-leaf (grepped, unused):
  `IsCombinatorialSolidTorus.false_of_isPreconnected_sdiff_of_nullhomotopic`. The leaf is a
  `by_cases` from it and the 28.9 sub-leaf above (checked in the same probe).
- Statement: TRUE (reviewer's argument verified: a nonseparating `G` null in `S` is a meridian,
  linking a generator of `Z` once, impossible for a loop missing `Δ`).
- Stuck goal: the separating case is goal 1 above; the nonseparating case needs a linking or
  intersection-number invariant of loops in `ℝ³ \ G` (none in the tree: grep for linking,
  intersection number, Alexander duality finds nothing) and the identification of `G` as a
  meridian (the open product-coordinate leaf of `Skeleton/Section28Annuli.lean`).
- Compiles: shared with the probe above.

## exists_polygon_carrier_of_spine — STUCK

- File: none (no Lean attempt beyond the analysis; no `.wip`).
- Statement: TRUE (checked the degenerate positions: `S₁ ⊆ int S₂` is excluded by `hZ₀S₂`,
  `S₂ ⊆ int S₁` makes the whole boundary torus available; no general position is needed because
  the homotopy is put in general position inside `int S₁`).
- Stuck goal: the whole of 28.11 plus extraction. Needed and absent: a PL singular annulus
  `S¹ × I → int S₁` from a spine loop of `Z₁` to a loop of `Z₀`, in general position with respect
  to the surface `frontier S₂` (the tree's singular general position, `SingularGeneralPosition`,
  `SingularLevelPolygons`, is for height functions and disks, not for a map transverse to a
  surface); the preimage polygons separating the ends; and the extraction of one embedded PL
  circle in the open set `frontier S₂ ∩ int S₁` carrying `π₁(S₂)` from a singular loop there
  (28.8, again torus-curve classification). Estimated several thousand lines; not started.

# Batch 4 (torus-curve chain)

## Parity brick: orientable gluing and Euler parity of orientable surfaces — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/OrientableSurfaceEulerParity.lean`
  (584 lines, SHA-256 `55e0bc52945628860865986e1a7de0041bfe0f24e830805687f41dad5e0c24f4`).
- Import line to register (81 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.OrientableSurfaceEulerParity`
- New public names (grepped tree-wide, unused before):
  `SimplicialBoolCocycle.isCoboundary_of_isCoboundary_ofLe` (a `ℤ/2` cocycle on `M` covered
  edgewise by `P`, `Q` is a coboundary if it is one on `P` and on `Q` and the common vertices
  span a subcomplex `I` with preconnected edge graph), `IsOrientable.of_faces_eq_union`,
  `IsOrientable.of_space_eq_union` (any combinatorial `n`-manifold triangulating `K ∪ L`, `K`, `L`
  orientable `n`-manifolds with preconnected `K ∩ L`, is orientable; this is form (a): capping a
  boundary circle keeps orientability), `IsOrientable.of_space_eq_union_union` (three pieces
  `K ∪ L₀ ∪ L₁`, `L₀ ∩ L₁ = ∅`), `IsCombinatorialManifold.even_eulerChar_of_isOrientable`
  (closed connected orientable surface in any finite-dimensional space: `χ` even),
  `IsCombinatorialManifoldWithBoundary.odd_eulerChar_of_isOrientable` (form (b): connected,
  orientable, boundary one PL circle: `χ` odd),
  `IsCombinatorialManifoldWithBoundary.eulerChar_le_one_of_isPLSphere_one`,
  `IsCombinatorialManifoldWithBoundary.eulerChar_nonpos_of_boundary_eq_union` (two disjoint
  boundary circles: `χ ≤ 0`), `IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_of_eulerChar_eq_one`
  (connected surface bounded by a PL circle `J` with `χ = 1` is a PL disk with rim `J`); local
  instance `finite_faceStarComplex_faces_orientableGluing`. Private helpers: cone capping of one
  or two boundary circles in `E × ℝ` (with orientability transfer), the induction on `2 - χ`.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\OrientableSurfaceEulerParity.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~16:30 local, second compile).
- Axiom audit: `AuditOpusC8.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC8.lean with no diagnostics;
  shared outputs unchanged.` (16:32): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: orientability is the coboundary property of `orientationCocycle` on the barycentric
  subdivision (`orientationCocycle_isCoboundary_iff`), restricted to subcomplexes by
  `orientationCocycle_parity_of_faces_subset`. On a triangulation `A ∪ B` (common subdivision,
  `exists_simplicialComplex_space_union`), every barycentric edge lies in `bary A` or `bary B`
  (top of its flag), and a common barycentric vertex is the centroid of a common face
  (`injOn_faces_of_mem_openSimplex`), so the overlap is `bary (A ∩ B)`, whose edge graph is
  preconnected (`edgeGraph_preconnected_of_isPreconnected_space`); the two trivialisations differ
  by a constant there. Parity: if `χ(K) ≠ 2`, `exists_isPLSphere_one_isPreconnected_sdiff` and
  `exists_connected_annulus_complement` give an orientable `R` with `χ(R) = χ(K)` and two boundary
  circles; cones above and below `R × {0}` (`exists_closed_of_disk_pair`) give an orientable closed
  surface with `χ + 2 ≤ 2` (`faceEulerChar_le_two`); strong induction on `2 - χ`. One boundary
  circle: cap once. Disk recognition: the capped surface has `χ = 2`, is a PL sphere
  (`isPLSphere_two_of_faceEulerChar_eq_two`), and `IsPLSphere.isPLBall_closure_sdiff`,
  `closure_sdiff_eq_sdiff_image_stdSimplexBoundary`, `image_stdSimplexBoundary_complement`
  identify `K × {0}` as the complementary disk with rim `J × {0}`.
- Hypotheses: only the stated manifold, orientability, connectivity and boundary hypotheses; the
  realisation space is any finite-dimensional real normed space.
- Compiles: 2 module checks + 1 audit.

## Moise 28.9: separating PL circle on a PL torus bounds a disk — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/SeparatingPolygonDisk.lean`
  (74 lines, SHA-256 `0424d009621dcd833ed8dbba6b9e6764aca458a6d944bf23dab7ad02cf8bb3b0`); imports the parity brick.
- Import line to register (74 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk`
- New public names (grepped tree-wide, unused before):
  `IsCombinatorialManifold.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff` (closed
  connected orientable surface in any finite-dimensional space with `0 ≤ χ`: a separating PL
  circle `J` bounds a PL disk `Δ ⊆ |K|`, `J = r '' ∂Δ²`) and
  `IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff` (the same on a PL torus
  `T ⊆ ℝ³`, output in the exact shape of the frozen leaf's second alternative with `T` in place of
  `frontier S`).
- NAME NOTE: the proposed `IsCombinatorialSolidTorus.exists_isPLCell_frontier_of_not_isPreconnected_sdiff`
  would only be `IsPLTorus...` applied to `hS.isPLTorus_frontier` (a one-line alias, forbidden by
  the worker rules); the solid torus plays no role, so the natural theorem is stated for PL tori
  and the assembly applies it to `frontier S` directly.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SeparatingPolygonDisk.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~16:34 local, first compile).
- Axiom audit: `AuditOpusC9.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC9.lean with no diagnostics;
  shared outputs unchanged.` (16:35): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: `exists_manifold_pair_of_separating_circle` gives the two sides `A`, `B` (connected,
  orientable, boundary `J`, `A ∪ B = |K|`, `A ∩ B = J`); `χ(K) = χ(A) + χ(B)`
  (`eulerChar_eq_add_of_space_union_of_isPLSphere_one`); both are odd and `≤ 1` (brick), so with
  `χ(K) ≥ 0` one equals one and is a PL disk with rim `J`
  (`exists_isPLHomeomorphOn_of_eulerChar_eq_one`). Torus: `IsPLTorus.exists_combinatorial_triangulation`,
  `isOrientable_euclidean_three`, `χ = 2 - β₁` (`eulerChar_eq_two_sub_bettiOne_of_isOrientable`)
  and `IsPLTorus.bettiOne_le_two`.
- Hypotheses of the torus theorem: `IsPLTorus T`, `IsPLSphere 1 G`, `G ⊆ T`,
  `¬ IsPreconnected (T \ G)`; producers: `IsCombinatorialSolidTorus.isPLTorus_frontier` for `T`.
- Compiles: 1 module check + 1 audit.

## IsCombinatorialSolidTorus.carriesFundamentalGroupOnto_of_isPreconnected_sdiff — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/NonseparatingPolygonCarrier.lean`
  (546 lines, SHA-256 `4e67aea8f55ba7fcbff1f994692dc7fe0fc87fd4b65f4b06f01a770aa3a97886`);
  imports the parity brick and `SeparatingPolygonDisk`.
- Import line to register (80 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier`
- New public names (grepped tree-wide, unused before; the `.wip` files only):
  `surjective_fundamentalGroup_map_of_homotopy` (a homotopy `F₀ ≃ F₁` transfers surjectivity of
  `π₁` from `F₁` to `F₀`, via `Path.Homotopic.map_trans_evalAt`),
  `carriesFundamentalGroupOnto_image_zero_of_image_one` (the annulus transfer: `f` continuous on
  `C × [0,1]` into `T`, `C` compact, `f (·,1)` injective: if `f (C × {1})` carries `π₁(T)` then
  so does `f (C × {0})`), `IsTopologicalSolidTorus.isPathConnected`,
  `IsTopologicalSolidTorus.not_simplyConnectedSpace`,
  `IsTopologicalSolidTorus.not_carriesFundamentalGroupOnto_of_subset_isPLBall` (no nonempty
  subset of a PL ball inside a solid torus carries its `π₁`),
  `IsPLSphere.exists_disk_or_annulus_of_subset_prism_lateral` (a PL circle in `∂Δ² × (0,1)`
  bounds a PL disk in `∂Δ² × [0,1]`, or a PL embedding of `∂Δ² × [0,1]` into itself fixes the
  bottom circle and takes the top circle onto it), and the sub-leaf itself with the statement
  proposed by the previous worker (unchanged). Private: the prism-sphere lemma
  `IsPLSphere 2 (Δ² × {0,1} ∪ ∂Δ² × [0,1])` (the construction of `TorusOfOrientableEulerCharZero`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\NonseparatingPolygonCarrier.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 ~16:49 local, fifth compile).
- Axiom audit: `AuditOpusC10.lean` (this module and the assembly below) — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC10.lean with no diagnostics;
  shared outputs unchanged.` (16:52): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route: `T = frontier S` is a PL torus (`isPLTorus_frontier`), triangulated orientably by `L`;
  `exists_connected_annulus_complement` with `U = T \ K` gives `R` (connected, orientable,
  `χ(R) = χ(L)`, boundary `G₋ ∪ G₊`, bicollar `ρ : G × [-1,1] → W`, `W ∩ K = ∅`);
  `χ(R) ≤ 0` (brick) and `χ(L) = 2 - β₁ ≥ 0` give `χ(R) = 0`, so `R` is an annulus
  `h : ∂Δ² × [0,1] → R` (`exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero`); `K ⊆ R` misses
  `∂R`, so `K' = h⁻¹ K ⊆ ∂Δ² × (0,1)`. Disk case: `h(D)` is a PL ball in `S` containing `K`,
  contradicting `hKgen` (a solid torus is not simply connected). Annulus case: transfer along
  `h ∘ ψ` (ends `G₋`, `K`) and then along `(x,t) ↦ ρ(x,-t)` (ends `G`, `G₋`). Dichotomy: the disk
  decomposition of `K'` in the prism sphere (`exists_disk_decomposition_of_isPLSphere_one_subset_two`);
  the end disks lie on one side each (`isPreconnected_iff_subset_of_disjoint_closed`); if on the
  same side, the other disk lies in the lateral annulus; otherwise
  `exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk` (fix the bottom disk, send the top side onto
  the top disk) and `IsPLHomeomorphOn.image_image_stdSimplexBoundary` (rim to rim) give `ψ`.
- Hypotheses of the sub-leaf and producers: `hS : IsCombinatorialSolidTorus S`, `hK`, `hG`
  (PL circles), `hKS`, `hGS` (in `frontier S`), `hKgen`, `hGK : Disjoint G K`,
  `hnonsep : IsPreconnected (frontier S \ G)` (the `by_cases` branch of the assembly). All are
  used (zero-diagnostic compile).
- Compiles: 5 module checks (errors fixed: universe/notation/`Σ` and `₋` identifiers,
  motive-dependent rewrites of `FundamentalGroup.map`) + 1 audit.

## carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/CarriesGeneratorOrIsPLCellOfDisjointCarrier.lean`
  (36 lines, SHA-256 `6da2712beb0f828e7c63d2c13fb5b0d19ed39b516193024d4278a0306362cb2e`);
  imports `NonseparatingPolygonCarrier` and `SeparatingPolygonDisk`. The name coincides with the
  untracked `CarriesGeneratorOrIsPLCellOfDisjointCarrier.lean.wip`, which was not touched and can
  be deleted by the lead.
- Import line to register (96 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.CarriesGeneratorOrIsPLCellOfDisjointCarrier`
- New public names: the frozen leaf only; statement byte-identical to
  `Skeleton/Section31CanonicalConfiguration.lean:467` (checked by string comparison after CRLF
  normalization; same `open Set Topology`, same namespace, no `variable` context in `Leaves`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CarriesGeneratorOrIsPLCellOfDisjointCarrier.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 16:51 local, first compile).
- Axiom audit: `AuditOpusC10.lean`, as above.
- Route: `by_cases hsep : IsPreconnected (frontier S \ G)`; nonseparating:
  `IsCombinatorialSolidTorus.carriesFundamentalGroupOnto_of_isPreconnected_sdiff`; separating:
  `IsPLTorus.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff` on
  `hS.isPLTorus_frontier` (whose output is literally the second alternative).
- Compiles: 1 module check + the shared audit.

# Batch 5 (orientable descent step)

## NormalSingularCellData.exists_descendingSurgery_of_adaptedCleanCap — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/ClosedBranchDisjointDescent.lean`
  (504 lines, SHA-256 `6be118256390d025a89e97e286cc3fc8c6bc419af85ace3f84d09d3aed4f5395`).
- Import line to register (92 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchDisjointDescent`
- New public names (grepped tree-wide, unused before):
  `NormalSingularCellData.branchCarrier_subset_or_disjoint_doublePointSet_sdiff_interior` (whole
  or nothing for the region `D.domain \ interior K` kept by a closed `K` whose frontier carries
  no double point) and the leaf itself (statement byte-identical to
  `Skeleton/DescentStepOrientable.lean:172`, same `universe u v w`, namespace
  `NormalSingularCellData`, same `variable` block, `open Set Topology`; string comparison).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LoopTheorem\ClosedBranchDisjointDescent.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22 17:11 local, second compile; host guard 1 lean process).
- Axiom audit: `AuditOpusC11.lean` — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC11.lean with no diagnostics;
  shared outputs unchanged.` (17:12): closure within `propext`, `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route (disjoint analogue of `exists_isNestedDiskReplacementCell` + nested descent): `G = Δ` on
  `E'`, `G = D` off `E'` (`IsPLOn.piecewise_of_isClosed`, seam `frontier E'` where `Δ = D`).
  A point of `interior E'` never shares its image with a point of `D.domain` (`hΔmeet` +
  injectivity of `Δ`), so `doublePointSet G = doublePointSet D (D.domain \ interior E')`;
  `frontier E' ⊆ E' \ E` has no double points (`hE'clean`), so the fibres of double points of `G`
  lie off `E'`; fibre equality near them gives the crossing charts
  (`HasPLNormalDoubleCrossingAt.of_eventually_eq_fiber`), relative openness comes from
  `doublePointSet_mem_nhdsWithin_of_pullback` with `r = id` and `S = D '' frontier E'`, and the
  triangulation from `restrict_to_clopen_doublePointSet`. `c` disappears (`T ⊆ interior E'`,
  `D` injective on `Q ⊇ J`); branch injection by the new whole or nothing lemma and
  `DescendingSurgery.ofBranchInjection`. Side, buffer, boundary loop inherited.
- LEAD DECISION: the frozen statement carries eleven hypotheses the surgery does not use
  (`hc`, `hJ`, `hT`, `hJT`, `hQsub`, `hclean`, `hk`, `hkT`, `hkcompat`, `hdisjoint`, `hQE'`);
  they are named with `let _ := …` (the AGENTS.md pattern) so that the frozen statement compiles
  without an unused-variable diagnostic. A strictly stronger restatement without them is possible.
- Compiles: 2 module checks + 1 audit.

## exists_plCrossSeamReading_of_isCrossRegluedCell — CLOSED

- Files (all new, `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/`):
  - `CrossSeamTubePages.lean` (1144 lines, SHA-256
    `15bc4ffcbe1611139e14f9dcb5159d8c6753d3418df03ec2e3d3f0eea0f20818`)
  - `CrossSeamTubeTransverse.lean` (566 lines, SHA-256
    `5b47037f064fdef4b4f8af565784077d10768f5e0d13c85411b4f401de746748`)
  - `CrossSeamTubeReading.lean` (231 lines, SHA-256
    `f163f6d13e639e36b6c0fdbc10fcb4cff64d70283d64940e9f606ff118d4df65`)
  - `CrossRegluedCellReading.lean` (850 lines, SHA-256
    `fdd9c68d361e5156aaa8ce8f2bf80fff76727aac1535dfdd26b8f456e5f23638`), contains the leaf.
- Import lines to register, in dependency order (83, 88, 85, 88 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubePages`
  `import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubeTransverse`
  `import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubeReading`
  `import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellReading`
- New public names (77, each grepped tree-wide with `grep -rlw`, none used before; the four
  defs have no underscore): `CrossSeamTubePages`: `crossRayOf`, `crossDirOf`, `crossSheetOf`,
  `crossOpenSheetOf`, `crossSeamPage` (defs) and `crossRayOf_sdiff_eq`,
  `crossRayOf_subset_crossingArc`, `crossRayOf_subset_spliceSquare`, `zero_mem_crossRayOf`,
  `crossOpenSheetOf_subset_crossSheetOf`, `crossSheetOf_subset_spliceCylinder`,
  `crossOpenSheetOf_subset_spliceCylinder`, `crossSheetOf_subset_crossingFigure`,
  `crossSheetOf_eq_union`, `disjoint_crossOpenSheetOf_spliceCore`,
  `spliceCore_subset_crossSheetOf`, `convex_crossOpenSheetOf`,
  `smul_crossDirOf_mem_crossOpenSheetOf`, `mem_closure_crossOpenSheetOf`,
  `exists_mem_crossOpenSheetOf`, `crossRayOf_inter_subset`, `crossSheetOf_inter_subset`,
  `isHPolytope_crossSheetOf`, `isHPolytope_spliceCore`, `crossQuarterTurn_smul_crossDirOf`,
  `crossOpenSheetOf_eq_image`, `image_crossQuarterTurn_crossOpenSheetOf`,
  `image_crossQuarterTurn_crossSheetOf`, `continuousOn_invFunOn_of_isCompact_of_forall_eq`,
  `exists_mem_nhds_inter_image_subset_image_inter`, `exists_mem_nhds_forall_mem_of_isCompact`,
  `crossSeamPage_subset`, `crossSeamPage_subset_preimage`, `exists_mem_crossSeamPage_apply_eq`,
  `notMem_crossSeamPage_of_forall_mem`, `exists_forall_mem_or_forall_mem_of_crossOpenSheetOf`,
  `exists_eq_invFunOn_of_mem_of_crossSeam`, `crossSeamPage_class`, `crossOpenSheetOf_eq_sdiff`,
  `zero_mem_closure_crossRayOf_sdiff`, `IsPLBall.exists_isOpen_isPreconnected_inter_interior`,
  `mem_of_apply_mem_image_of_injOn`, `eq_invFunOn_or_eq_invFunOn_of_crossSeam`,
  `forall_mem_of_subset_crossSeamPage`, `crossSeamPage_eq_union`, `injOn_crossSeamPage`,
  `image_crossSeamPage`, `bijOn_crossSeamPage`, `inter_preimage_invFunOn_eq`,
  `isPolyhedron_crossSeamPage`, `isPLHomeomorphOn_crossSeamPage`,
  `continuousOn_invFunOn_crossSeamPage`, `mem_frontier_iff_of_mem_crossSeamPage`,
  `exists_mem_crossSeamPage_of_mem`, `crossSeamPage_wall`; `CrossSeamTubeTransverse`:
  `crossOpenSheetOf_subset_sdiff`, `pos_of_isPreconnected_of_ne_zero`,
  `neg_of_isPreconnected_of_ne_zero`, `norm_crossDirOf`, `crossWedge_ne_zero`,
  `not_crossWedge_of_succ`, `exists_forall_mem_of_crossSeamPage_ownership`,
  `exists_two_sides_of_crossSeamSheet`, `exists_opposite_crossSeamPage`;
  `CrossSeamTubeReading`: `isOpen_image_crossSeamBox`, `disjoint_crossSeamPage_of_class`,
  `nonempty_plCrossSeamReading_of_crossSeamPage`; `CrossRegluedCellReading`:
  `false_of_three_mem_fiber`, `false_of_isOpen_inter_subset`,
  `isPreconnected_inter_preimage_crossOpenSheetOf`, `nonempty_inter_preimage_crossOpenSheetOf`,
  `disjoint_inter_preimage_crossOpenSheetOf`, `crossSeamPage_subset_of_three_closed`,
  `exists_isOpen_forall_mem_crossSeamPage`, `crossSeamPage_comp_crossQuarterTurn`,
  `nonempty_plCrossSeamReading_comp_crossQuarterTurn` and the leaf (statement byte-identical to
  `Skeleton/DescentStepOrientable.lean:235`, top level in the same namespace with
  `open Set Topology`; string comparison of the text from `theorem` to `:= by`).
- Checker (2026-09-22, local time, host guard 0 lean processes), in dependency order, after the
  last edit (three `/-! ### … -/` section headers removed from `CrossSeamTubePages.lean`):
  18:44 `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LoopTheorem\CrossSeamTubePages.lean with no diagnostics; shared outputs unchanged.`
  18:44 `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LoopTheorem\CrossSeamTubeTransverse.lean with no diagnostics; shared outputs unchanged.`
  18:45 `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LoopTheorem\CrossSeamTubeReading.lean with no diagnostics; shared outputs unchanged.`
  18:45 `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LoopTheorem\CrossRegluedCellReading.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit: `AuditOpusC12.lean` over all four modules — `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC12.lean with no diagnostics;
  shared outputs unchanged.` (18:46, rerun after the last edit): closures within `propext`,
  `Classical.choice`,
  `Quot.sound`; the thirteen environment linters pass.
- Route. The four half sheets are indexed cyclically by `Fin 4` (`e₁, e₂, -e₁, -e₂`, so the
  quarter turn is `i ↦ i + 1`). For a map `f` of a compact `Dom` over the tube, the page
  `crossSeamPage chart f Dom i` is the closure of the part over the open `i`-th sheet.
  (1) `crossSeamPage_class`: if `f` is injective over the open sheets and covers them, and the
  preimage of the core is two disjoint closed arcs `J₁`, `J₂` each carried bijectively onto the
  core, every page contains exactly one of them and misses the other (local dichotomy along the
  core: the preimage of a small box of an open sheet is the continuous image of a convex set,
  hence follows one of the two core preimages; then connectedness of `[0, 1]`). Pages are
  polyhedra (`IsPolyhedron.closure_sdiff` of two PL preimages), `invFunOn chart ∘ f` is a PL
  homeomorphism of each page onto its sheet, the boundary clause holds (core end points are
  limits of page points on `BdM`), and the wall clause holds (`chart` of the open box is open by
  invariance of domain; interiors of PL disks are locally preconnected).
  (2) `exists_opposite_crossSeamPage`: the two-sided crossing at `chart (0, 0, 1/2)`
  (`hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary`, normal form
  `exists_linearEquiv_normalForm`) forces each arc onto two opposite sheets: each arc has pages
  on both sides of its plane (points `h⁻¹ L⁻¹ (0, ±ε, 0)`), and two adjacent pages of one arc
  would give a segment through the open quadrant on which the other functional changes sign
  without vanishing (`not_crossWedge_of_succ`, intermediate value theorem).
  (3) For the leaf: `D`'s pages over `A` lie one in `U₁` and one in `U₂`, those over `C` one in
  `U₂` and one in `U₃` (each open page is preconnected and misses `A ∪ C`; near the interior
  point of `A` over the middle of the core both sides of `A` occur, else an open set would lie in
  `U₁ ∩ U₂ = A`). The cross reglue `G` has preimage arcs `P' ∩ h⁻¹(P ∩ Q)` and `P' ∩ Q'`; its
  pages sit in `P' ∩ h⁻¹P`, `P' ∩ h⁻¹Q`, `Q'`, matching `U₁`, `U₂`, `U₃` through `f₁ ∘ h`,
  `f₂ ∘ h`, `f₃`, so each arc of `G` gets one page of `A` and one of `C`, i.e. two adjacent
  sheets. Pairs `{e₁, -e₂}`, `{-e₁, e₂}` give the reading in `T.chart`
  (`nonempty_plCrossSeamReading_of_crossSeamPage` via
  `exists_plCrossSeamReading_of_four_source_pages`), the other adjacent pairing gives it in
  `T.chart ∘ crossQuarterTurn` (`crossSeamPage_comp_crossQuarterTurn`). Properness of `G` near
  the tube is derived from `G '' frontier G.domain = D '' frontier D.domain` and
  `doublePointSet G = doublePointSet D`.
- Hypotheses: every hypothesis of the frozen statement is used; no LEAD DECISION.
- Compiles: 25 module checks (all four modules, including two full re-verifications) + 2 audits.

## not_branchPreimage_eq_of_isOrientable — STUCK

- No file. The frozen statement is, up to the name `F` of the ambient space, the statement of
  `NormalSingularCellData.not_branchPreimage_eq_of_isOrientable` of
  `Skeleton/ClosedBranchCaseOne.lean:187` (checked by reading both), whose proof there is complete
  from proved producers (`exists_isMarkedBranchCollar`,
  `isOrientable_derivedNeighborhood_of_isSubdivision`,
  `exists_sourceRayTransport_of_isSourceTrackedBranchTube`, `SourceRayTransport.isSheetExchange`,
  `IsCylindricalDiagram.not_closedBranchCase1`, ...) and one open leaf. Skeleton modules may not
  be imported, so the leaf closes exactly when that open leaf is proved in a real module.
- Exact remaining goal (`Skeleton/ClosedBranchCaseOne.lean:169`, verbatim):
  `exists_isSourceTrackedBranchTube (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
  (hL : IsCombinatorialManifold 3 L) : letI := combinatorialChartedSpace L hL; ∀ D BdM B hD c,
  ¬hD.singularSet.IsBoundaryBranch c → ∀ J Q C τ ρ sheet, IsPLSphere 1 J →
  hD.IsMarkedBranchCollar c J Q C τ ρ sheet → ∃ Pc (_ : Finite Pc.faces) N (_ : Finite N.faces)
  φ u r, IsSourceTrackedBranchTube hD c Subtype.val L J ρ N Pc φ u r`: a cylindrical diagram
  of a derived neighbourhood `derivedNeighborhood R Lc` (`R` a finite subdivision of `L`) over a
  `2`-ball cross section, with PL end map permuting four cyclically ordered marked points and the
  four crossing rays realised by continuous source arcs in `J` on fixed collar sides.
- Verified missing (grep): `IsSourceTrackedBranchTube` is constructed nowhere; the only
  `IsCylindricalDiagram` producers (`exists_isCylindricalDiagram_eqOn_eqOn`,
  `exists_isCylindricalDiagram_of_annulus_bicollar`) start from given product or annulus data,
  not from a branch circle. Gemini G088 confirmed: not a one-lemma gap.
- Tube-free alternative checked and not available: the local sign
  `ε(a) = orientation of (carrier direction, collar normal of the sheet through a, collar normal
  of the sheet through τ a)` would be locally constant along the connected `J` and change sign
  under the deck involution `τ`, but it needs an orientation sign of the marked charts
  `sheet a : OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)` relative to the combinatorial
  `CoherentOrientation` of `L`; `Orientation.lean` is purely combinatorial and
  `IsMarkedCrossingChartAt` carries no PL clause, so this bridge (local constancy of the sign of
  an injective PL map, chart versus simplex orientation) is itself a new theory.

## isPLBoundaryTubeProducer_double — STUCK

- No file. Exact remaining goal: the frozen statement itself, i.e. `IsPLBoundaryTubeProducer`
  at the double: for every normal singular cell `D`, boundary branch `c`, side `W` with
  `IsPLBoundarySide D W BdM` and buffer `B`, a tube `U` with `T : CrossSeamTubeData hD c U`,
  `Nonempty (PLSeamTubeChart M T.chart)`, `T.chart '' spliceCylinder ⊆ W`,
  `T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks` and the end disks in the
  `B`-buffer. This is the relative regular neighbourhood of the branch arc, the long-standing
  `IsCrossSeamTubeProducer` gap (cited as the missing input in `BranchCollarPrism`,
  `BranchSeparation`, `LuneCell`, ...; `HANDOFF_CODEX_L.md` §81.4: "a chart along the whole
  branch").
- Verified missing: the tree has only the gluing step `exists_chart_branch_chain` /
  `exists_openPartialHomeomorph_branch_chain` (`BranchChainChart.lean`), which assumes the global
  straightening map `Φ` (injective, PL homeomorphic on each chart piece, sheets on coordinate
  planes) is already given; nothing constructs `Φ` along the arc from the pointwise crossing
  charts, and there is no derived-neighbourhood-is-a-ball-with-cross-trace theorem for an arc.
  `IsPLBoundarySide` gives half-space pair charts only at points of `D '' frontier D.domain`.
  Gemini G083 confirmed.

## NormalSingularCellData.exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk — STUCK

- No file. Exact remaining goal: the frozen conclusion `∃ E' Δ, IsPLBall 2 E' ∧ E ⊆ interior E'
  ∧ E' ⊆ interior D.domain ∧ Disjoint Q E' ∧ (E' \ E) ∩ doublePointPreimage D D.domain = ∅ ∧
  Δ.domain = E' ∧ InjOn Δ E' ∧ Δ '' E' ⊆ V ∧ EqOn Δ D (frontier E') ∧
  Δ '' E' ∩ D '' D.domain = D '' frontier E'`. Its geometric input is a PL product
  neighbourhood of the embedded clean disk `D '' Q` inside `V`, adapted to the second sheet along
  `D '' J = D '' T`: a PL embedding `Π : Q × [-1, 1] → V` with `Π (·, 0) = D` on `Q`, meeting
  `D '' D.domain` only in `D '' Q` and in the image of a collar of `T` outside `E`, which lies on
  the wall `Π '' (J × [0, 1])`; then `Δ` is `Π '' (Q × {δ}) ∪ Π '' (J × [0, δ])` pulled back to
  `E'` = `E` plus a thin collar.
- Verified missing: the prism, collar and push-off lemmas of the tree
  (`IsPLBall.exists_collar_of_properly_embedded_disk`,
  `IsPLBall.exists_pushOff_of_properly_embedded_disk`,
  `IsCombinatorialManifold.exists_collar_of_spanning_disk`,
  `IsPLBall.exists_centered_prism_subset_of_boundary_neighborhood`,
  `IsPLBall.exists_prism_of_disjoint_frontier_disks`) all live in an ambient normed space of
  `finrank 3`, for a properly embedded disk in a combinatorial ball or a disk spanning a closed
  surface there; here `M` is an abstract `HasGroupoid M (plGroupoid 3)` manifold, `D '' Q` need
  not lie in one chart, its boundary circle is interior to `M` and crossed by the `T` sheet, and
  the only triangulated neighbourhood (`SingularTwoCell.exists_compact_piece_neighborhood`) lives
  in `EuclideanSpace ℝ (Fin T.ambientDim)`, not of dimension three. Gemini G085 confirmed.

# Batch 6 (branch tube)

## exists_isSourceTrackedBranchTube — STUCK (statement obstruction on the reviewed route)

- No file. Frozen statement: `Skeleton/ClosedBranchCaseOne.lean:169` (input: a closed branch `c`
  with one-circle preimage `J`, the marked collar `hD.IsMarkedBranchCollar c J Q C τ ρ sheet`
  with an arbitrary given PL collar `ρ`; output: `IsSourceTrackedBranchTube`).
- Obstruction found (checked by hand computation, not by Lean): the clause `realisation` asks,
  for every `t`, `φ (r i, t) = ι (D (ρ (a i t, s i t)))` together with
  `D (a i t) = branch map (e t)` for a homeomorphism `e`. Hence `a i` is injective on `[0, 1)`
  and the curve `t ↦ φ (r i, t)`, which lies in `∂N ∩ D '' D.domain` (the lateral boundary of a
  cylindrical diagram of the solid torus `N` is `∂N`, by invariance of domain), must be a strict
  graph over `J` in the given collar coordinates `(w, s) = ρ⁻¹`. On the reviewed route
  (`N = derivedNeighborhood R (restrict R Γ)` for a subdivision `R` in which the branch `Γ` and the
  image `Z` are subcomplexes, as in `exists_circle_subcomplex_branchCarrier`) this fails wherever
  `D ∘ ρ` is affine on a triangle `Δ = [p, q, r]` of `R` with `[p, q] ⊆ Γ`: `∂N ∩ Δ` is the path
  through the second-derived points `mid(p, m_pr)`, `ctr(p, m_pr, b)`, `mid(p, b)`,
  `ctr(p, m_pq, b)`, `mid(m_pq, b)`, `ctr(m_pq, q, b)`, `mid(q, b)`, `ctr(q, m_qr, b)`,
  `mid(q, m_qr)`, whose coordinates along `[p, q]` (with `r` at `x_r`) have consecutive
  increments `(1 - 2 x_r) / 18` at the second step and `(2 x_r - 1) / 18` at the seventh; they
  cannot both be positive, so `w` is not strictly monotone there for any apex position. Taking `L`
  fine relative to an affine patch of `D ∘ ρ` (any subdivision of `L` is then fine too) makes this
  unavoidable for every `R`. Non-subcomplex choices of `R`, `Lc` are not excluded by this argument,
  so the statement is not refuted, but the reviewed route cannot prove it.
- Consumer check: `exists_sourceRayTransport_of_isSourceTrackedBranchTube` uses `hreal` only at
  `t = 0` and `t = 1` (plus `hbase` for all `t`). Even an endpoint version still asks the four
  base points `φ (r i, 0)` to sit on the `ρ`-transverse arcs over one branch point `e 0`, which a
  derived-neighbourhood meridian disk (a cone over its interface circle) does not give either.
- LEAD DECISION needed: restate `realisation` in terms of the half sheet (preimage point, side)
  on which each ray lies at `t = 0` and `t = 1`, without exact collar coordinates, or drop
  `derived` and build the tube adapted to `ρ`. Items 3 (`not_branchPreimage_eq_of_isOrientable`)
  and the ClosedBranchCaseOne assembly wait on this.

## isPLBoundaryTubeProducer_double — IN PROGRESS (route and verified bricks)

- Route (chart by chart, no triangulation of the tube): along the branch arc, consecutive
  straightening charts are joined by the conical extension of their transition at the junction
  point; the conical extension is a PL homeomorphism of the whole model, preserves the cross and
  its axis, and is defined as far along the arc as needed, so finitely many charts (Lebesgue
  number) give one global straightening map. The last junction distorts the far end plane; the
  conical extension there is cylindrical (commutes with translation along the axis), so the
  boundary is a PL graph over the cross-section and a vertical clamp removes it.
- Verified bricks (each module: checker "Verified ... with no diagnostics; shared outputs
  unchanged"; no sorry/axiom/set_option; statements new):
  `ConicalGermExtension` (292 lines): `conicalGermExtension`,
  `IsPLHomeomorphOn.exists_isPLHomeomorphOn_univ_homogeneous`, `forall_mem_iff_of_homogeneous`.
  `ArcStraighteningJunction` (298): `crossPlanes`, `coreSegment`,
  `IsPLHomeomorphOn.restrict_of_image_eq_inter`, `exists_isOpen_injOn_of_isCompact`,
  `exists_junction`.
  `ArcStraighteningStep` (504): `isPLHomeomorphOn_union_of_eqOn`, `axisFlip`,
  `exists_arcStraightening_step` (one interior chart).
  `ArcStraighteningEnds` (417): `exists_arcStraightening_base`, `clampShift`,
  `verticalClamp`, `isPLHomeomorphOn_verticalClamp`, `add_axis_of_homogeneous`.
  `ArcStraighteningFinal` (478): `exists_arcStraightening_final` (end chart, flat top).
  `ArcStraightening` (168): `exists_arcStraightening` — the global straightening map along an
  arc in any finite dimensional ambient space, from interior charts and two end charts.
- Remaining for the leaf: (a) interior straightening charts for a normal cell in the ambient
  coordinates of the double (crossing chart + two-sidedness + normal form); (b) adapted end
  charts at the two boundary points of the branch, where the crossing chart and the side chart
  `IsPLHalfSpacePairAt` must be merged (the four-spoke disk step); (c) assembly into
  `CrossSeamTubeData`, `PLSeamTubeChart`, side, boundary and buffer clauses.
- Update (same item): the whole producer is now proved modulo adapted end charts only.
  `LoopTheorem/BoundaryBranchTubeCharts` (259 lines): `exists_straighteningChart_of_notMem_boundary`
  (interior charts from the two-sided crossing chart, ambient coordinates of any finite
  combinatorial 3-manifold). `LoopTheorem/BoundaryBranchArc` (232):
  `NormalSingularSetTriangulation.exists_arc_of_isBoundaryBranch` (the arc with exactly its two
  ends on `BdM`). `LoopTheorem/BoundaryBranchTube` (471): `exists_plSeamTube_of_straightening`,
  `nonempty_plSeamTubeChart_of_isPLHomeomorphOn` and
  `isPLBoundaryTubeProducer_of_exists_endChart` (all verified, no diagnostics). Its single
  hypothesis: at every boundary double point `y` of a normal cell on a PL boundary side there is a
  PL homeomorphism `ψ` from an open `V ∋ 0` of the model onto `L.space ∩ Ω` with `ψ 0 = y` reading
  the cell as `crossPlanes ∩ {0 ≤ t}`, the double set as `{p.1 = 0, 0 ≤ t}`, `W` as `{0 ≤ t}` and
  `BdM` as `{t = 0}` (merging the boundary crossing chart with the side chart; four-spoke disk).

## isPLBoundaryTubeProducer_double — DONE

- Leaf: `LoopTheorem/BoundaryTubeProducerDouble.lean` (33 lines). Frozen statement byte-identical
  (text compared by script with `Skeleton/DescentStepOrientable.lean:163`); no frozen hypothesis
  dropped. Proof: `isPLBoundaryTubeProducer_of_exists_endChart` fed with
  `exists_endChart_of_mem_boundary`, both at `L := double 3 K`.
- The single remaining hypothesis of the entry above (adapted end charts) is now proved:
  `CircleFourPoints` (326 lines): `exists_isPLHomeomorphOn_circle_four_points` (a circle with a
  cut pair and two middle points maps onto any circle with four marked points, some relabelling),
  subarcs, reversal, concatenation; reuses `isPLHomeomorphOn_mul_add_Icc` of
  `LateralAnnulusLevels`.
  `FourSpokeSphere` (312): `exists_isPLHomeomorphOn_fourSpokeSphere` (sphere = two disks along an
  equator, four upper spokes; four-page theorem in planar coordinates on the upper disk, boundary
  extension on the lower disk).
  `CrossQuarterLink` (434): `crossQuarter`, `crossQuarterTriangle`, `exists_quarterLink_complex`
  (triangulation adapted to `t = 0` with the four image quarters as subcomplexes; each quarter
  link is an arc from the image of the half axis to the image of the leaf ray, pinned by an angle
  function).
  `CrossHalfSpaceNormalForm` (557): `exists_homogeneous_normalForm_crossHalfSpace` (the merge in
  the model: for a homogeneous PL homeomorphism `G` carrying the half cross into `{t ≥ 0}` and
  meeting `t = 0` in the flat cross, a homogeneous PL `Θ` with `Θ⁻¹ (G '' half cross)` = half
  cross, same for the half axis, preserving `t ≥ 0` and `t = 0`; link homeomorphism, cone
  extension, conical extension).
  `LoopTheorem/BoundaryBranchEndChart` (520): `eventually_mem_frontier_iff_of_halfPlane_sheet`
  (invariance of domain: on a boundary crossing sheet the frontier of the source is the edge of
  the half plane), `exists_boundaryCrossing_straighteningChart`, `exists_endChart_of_mem_boundary`.
- Correction to the progress entry above: `LoopTheorem/BoundaryBranchArc` has 230 lines.
- Verification: all fifteen Batch 6 modules (the nine listed above plus these six) compiled in
  dependency order, each "Verified ... with no diagnostics; shared outputs unchanged"; audit
  `AuditOpusC14.lean` over the fifteen modules (axioms within propext, Classical.choice,
  Quot.sound; the thirteen environment linters): "Verified ... with no diagnostics".
- Item 3 (`not_branchPreimage_eq_of_isOrientable`) still waits on item 1 (LEAD DECISION above).

# Batch 7 (compact Section 34)

Read first: digests AS and BG, the docstring of `Skeleton/Section34Compact.lean`. All ten leaves
are proved (or not) against the frozen text, in new files importing only real modules.

## exists_compactCutAndGraph — STUCK (deep; no counterpart in the tree)

- No file. The leaf is the whole of Lemma 1, Lemma 2's configuration and the compatible
  subdivision (pages 239--240) for a ball with boundary. Its non-compact counterpart, the cut
  producer `ControlledGraphNeighborhood`, is itself still a skeleton (5 + 3 leaf `sorry`s), so
  nothing can be adapted; `Section34Control` (P0) supplies only a triangulation and carriers.
- Missing pieces, each a separate producer of real size:
  (a) a triangulated outer collar of `C` inside `V` carrying a subdivision of `K`, so that the
      vertex balls of boundary vertices can leave `C` (`⋃ src = C ∪ N`, `N ⊄ C`);
  (b) PL cell certificates and the exact boundary and meet formulas for the ten cut kinds of a
      derived neighbourhood of the subdivided 1-skeleton cut by the simplices of `K`: face disks
      `closure (conv s \ N)`, tetra balls, patches, face and edge arcs, marked points, outer faces
      and outer arcs (`SplittingDiskRim`/`TubeOfGraphDualCells` cover only graph dual cells and
      splitting disks of a graph with all vertices interior to the complex);
  (c) the link condition as a consequence of the combinatorial manifold certificate (AS: OPEN);
  (d) the joint choice with 33.1: `Moise331` returns its own complex `T` and derived
      neighbourhood, with no compatibility with `K`, so `f₁` has to be restricted to a
      sub-neighbourhood `N` compatible with `K'`, and `f₁ '' N ∈ 𝓝ˢ (h '' Γ)` then needs a
      degree-type argument for `f₁` close to `h`;
  (e) for every face, the nested tori `S₁ ⊆ interior T_s ⊆ T_s ⊆ interior S₂` with toroidal
      shell and `IsSpine S₁ (h '' rim)`, and `IsCombinatorialSolidTorus T_s` (cyclic gluing of
      the vertex ball images, `CyclicBallUnion`);
  (f) the thin exterior clause 5(7), [ASSERTED] in the book.
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 933.

## exists_compactFaceEnvelopes — DONE

- File `Section34CompactFaceEnvelopes.lean` (imports `Section34CompactVocabulary`, a verbatim hoist
  of the skeleton's vocabulary lines 184--922, plus `TopologicalCellNestedShell` and
  `Topology.InvarianceOfDomainManifold`). Statement and variable block byte-identical.
- `env s` = thickening of `h '' conv s` by `δ`, minus the non-incident vertex balls, inside the
  incident carriers' interiors, minus `A s \ interior T_s`. `A s` is the capping ball
  `Moise305Tame.exists_isPLBall_capping`: the homeomorphism `x ↦ x + η min 1 (dist (u x) rim) • n`
  (`n` a unit normal of the face) lifts `conv s` off itself except along the rim; the image of a
  thin closed thickening is a topological cell, and 30.5 gives the PL ball. `δ` is the minimum of
  the pair radii (two distinct faces meet in the graph skeleton, inside the vertex balls) and the
  exterior radii (a path to a far point misses a thickening of the thin obstacle, and the ray
  beyond it misses the thick one).

## exists_compactFaceShellBalls — DONE (hypothesis `hgraph` dropped, linter-forced)

- Same file. `h` of a closed thickening of `conv s` inside `V ∩ h⁻¹ (env s)` is a topological cell
  with `h '' conv s` in its interior (invariance of domain); 30.5 gives the ball, boundary its
  frontier. `hgraph` is never used; with it the linter reports "Variable name `hgraph` is not
  explicitly referenced" (checked), so it is dropped. Otherwise byte-identical.

## exists_compactFaceBallsGeneralPosition — DONE

- File `Section34CompactGeneralPosition.lean`; statement and variable block byte-identical, all
  four hypotheses used. The face torus is a combinatorial solid torus (graph frame), so its
  frontier is a PL torus (`IsCombinatorialSolidTorus.isPLTorus_frontier`) and any triangulation
  is a closed combinatorial surface; no local planarity of the vertex-ball union is needed. The
  incident splitting circles lie on it (the splitting disk is the meet of its two end balls, no
  third vertex ball meets it by clause 26, two-ball frontier lemma), are disjoint, and form a
  subcomplex after subdivision. The given face ball need not contain a compact `h '' σ` (the leaf
  has no continuity of `h`), so the transverse ball is taken around a PL ball containing the face
  ball in its interior (`IsPLBall.exists_isPLBall_subset_interior_of_isOpen`).

## compactTraceHomology — DONE (hypotheses `hcut` and `hgp` dropped, linter-forced)

- File `Section34CompactTraceHomology.lean`. The generator clause gives `H₁` carrying for the rim
  (`T_s` path-connected as a solid torus); `IsPLCellOn.carriesFirstHomologyOnto_inter_interior`
  with Lemma 4's auxiliary ball `A` (from the envelopes; `B ∩ A ⊆ env s ∩ A ⊆ Int T_s`) gives
  `∂B ∩ Int T_s`; `CarriesFirstHomologyOnto.inter_frontier_of_chart` (identity chart) gives the
  whole trace `∂B ∩ ∂T_s`, integral and surjective, as warned. Its complexes triangulate the
  polyhedron `∂B ∩ T_s` with `∂B ∩ ∂T_s` as a subcomplex; no transversality is needed, so `hgp`
  is unused, and nothing of the cut frame is used. With them the linter reports both as "not
  explicitly referenced" (checked). The assembly call must drop the two arguments.

## compactTrace_of_noOperation — STUCK (deep; Lemmas 9--11, 28.8)

- No file. Its non-compact counterpart `section34Trace_of_noOperation` is itself a skeleton leaf.
- Missing, each a separate producer: (a) the trace `∂C_σ ∩ ∂N''` is a finite disjoint union of
  PL circles: turn the pointwise `HasPLCrossingAt` of the invariants into a closed combinatorial
  1-manifold (the tree has this only for complexes with transverse faces,
  `exists_isPLSphere_cover_inter_of_transverse_faces`); (b) a trace circle zero in `H₁ (N''_σ)`
  bounds an innermost disk on `∂N''_σ` off the other circles, which is an Operation 1 disk
  (PL Schoenflies on a PL torus/sphere; 28.8 is not stated in the tree); (c) with no bigon, a
  circle essential in the solid torus meets every incident splitting circle exactly once
  (intersection numbers with meridian disks); (d) `0 < r σ` from the nonempty trace, which the
  generator clause gives.
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 1049.

## exists_compactFaceDisks — STUCK (sub-leaf proved: vertex-ball meets)

- Proved brick, file `Section34CompactSplitDiskIntersection.lean`:
  `Section34CompactCutFrame.exists_splitDisk_eq_inter_vertexBall` (two distinct meeting vertex
  balls meet exactly in a splitting disk). New case against the non-compact version: an outer face
  is below no two vertex balls (`not_outerFace_subset_inter_vertexBall`): a boundary point of it
  lies in a proper face, and every proper kind is excluded (splitting kinds would put the outer
  face inside a splitting disk of the same dimension).
- Missing: (a) PL Schoenflies for a PL circle on the PL sphere `∂C_σ` and an innermost trace
  circle whose disk misses `⋃ V''_w` (the other side would make the class zero in `H₁`); (b) the
  cyclic structure of the incident vertices and edges on `∂σ` (each incident vertex has exactly
  two incident edges) and the fact that the relative interior of a splitting disk image lies in
  the interior of the union of its two end balls, which make each `D''_σ ∩ V''_w` one arc between
  two consecutive marked points; (c) the sub-arc of a PL circle between two points is a 1-cell.
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 1064.

## exists_compactResidualBalls — STUCK (deep; P7)

- No file; non-compact counterpart `exists_section34ResidualBalls` is a skeleton leaf. Needs the
  unbounded-component rule for the patches, the empty-sector certificate for the edge arcs, and
  the outer faces and outer arcs of the target with their tilings; none exists in the tree.
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 1085.

## compactSourceFace_iff_cutLe — STUCK (not "short")

- The containment steps of `Section34CompactCutStep` follow from the frame formulas except two:
  `faceArc a ≤ outerFace o` needs `src (.faceArc a) ⊆ closure (srcBd (.vertexBall o.1) \ (C ∪ ⋃
  D_e))`, and `markedPoint p ≤ outerArc q` needs the marked point in `closure (srcBd (.splitDisk
  q.1) \ C)`: both say that `N` crosses `∂C` at the face arcs and marked points of boundary faces,
  which no clause states; only a PL argument on the boundary circle of the outer face (its
  boundary formula) could force it. The converse needs, e.g. for `markedPoint p ⊆ outerArc q`,
  that `σ = p.1.1` is a boundary face from one point of it in `∂C`, again a local position fact.
  Pure containment cases (all pairs of equal dimension, the vertex-ball cases) are covered by
  the brick above and clause 10.
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 1111.

## compactTargetRecognition — STUCK

- Needs the explicit description of `Section34CompactCutLe` for all 10 × 10 kinds (induction on
  `ReflTransGen`), the brick above for the vertex-ball images, and target position facts not in
  the residual bundle: the relative interior of a splitting disk image lies in the interior of the
  union of its end balls (for `D''_σ ∩ E''_e = P''`), and a face arc of an interior face is not in
  the target outer face (for `D''_σ ∩ O''_w`).
- Exact remaining goal: the frozen statement at `Skeleton/Section34Compact.lean` line 1115.

## Batch 7 summary

- DONE 4 of 10: `exists_compactFaceEnvelopes`, `exists_compactFaceShellBalls` (drops `hgraph`),
  `exists_compactFaceBallsGeneralPosition`, `compactTraceHomology` (drops `hcut`, `hgp`); all
  drops linter-forced; the assembly calls must drop those arguments. STUCK 6: leaf 1 and 6--10.
- Files (LF, no docstrings/comments, ≤ 100 codepoints): `Section34CompactVocabulary` (774 lines,
  verbatim hoist of skeleton lines 184--922, names duplicate the skeleton's by design),
  `Section34CompactFaceEnvelopes` (608), `Section34CompactGeneralPosition` (428),
  `Section34CompactTraceHomology` (98), `Section34CompactSplitDiskIntersection` (248, brick).
- `Section34CompactGeneralPosition` imports `LoopTheoremDiskPrism`, absent from the shared build;
  compiled privately (no diagnostics).
- Audit `AuditOpusC15.lean` (five modules): verified, no diagnostics (axioms ⊆ {propext,
  Classical.choice, Quot.sound}, thirteen linters clean).

# Batch 8 (smoothing: annulus taming, sphere recognition)

## exists_homeomorph_smooth_annulus_of_isClosedEmbedding — CLOSED

- Endpoint: `SmoothAnnulusTaming.lean`, namespace `DifferentialGeometry.Topology.PiecewiseLinear`,
  with the skeleton's `open Set Topology Manifold`, `open scoped Manifold ContDiff`,
  `universe u` and `variable {E F …}`. Statement identity: lines 210–220 of
  `Skeleton/PLSmoothingCompact.lean` (name, binders, conclusion) are byte-identical to the
  module's statement (checked with `diff`); no hypothesis dropped. The lead must delete the
  skeleton copy when wiring (same fully qualified name).
- Route (review ruling followed: only the image is smoothed; the boundary isotopy starts at the
  identity and extends through the collar): half-annulus parametrization `e` of `range ψ` in
  `∂M` (`exists_halfAnnulus_param_of_isClosedEmbedding`); shrink isotopy onto
  `e{a ≤ ‖v‖ ≤ b}` (`exists_isotopy_shrink_halfAnnulus`); chart `Φ` with `Φ (2 • v) = e v`
  on `1 < ‖x‖ < 2`; core-circle smoothing of `Φ` (`exists_isotopy_smooth_annulus_core`: isotopy
  `G`, band `|‖x‖ - 3/2| < δ`, chart `c = G 1 ∘ Φ` with `c.symm` in the maximal atlas); radial
  squeeze in the chart onto `3/2 ≤ ‖x‖ ≤ 3/2 + δκ/2`; `θ` from
  `exists_homeomorph_of_boundary_isotopy`; `f = c ∘ j` with the band chart `j` of `S¹ × ℝ`
  (`exists_sphereProd_band_openPartialHomeomorph`), a smooth embedding into `M` by
  `isSmoothEmbedding_coe_of_boundary_openPartialHomeomorph`.
- Files (all new, LF, no declaration docstrings or comments, ≤ 100 codepoints), lines, SHA-256:
  - `Topology/LocalDegree/InjectiveDeterminantSign.lean` 187
    c04619c6a23ab33862993bada0e6f60859c68e0c7c90d6b2e5b3cec69a811b92
  - `Topology/PiecewiseLinear/SmoothedRampPath.lean` 327
    fa4a77ded513421ad0133ceda6e01bbd053e3fe1d5380614c293f0e731043831
  - `Topology/PlanarJordan/StripExtension.lean` 627
    69e70a6442334b868cc57c4f41b05873e75601014bcebc5cc9425ecc9f51866d
  - `Topology/PlanarJordan/PlanarLocalAffine.lean` 116
    06d885bdadb295210f2ed45dc17340a252ffcc508abe52f4431f7cde28a0c869
  - `Topology/PlanarJordan/PlanarSmoothCore.lean` 822
    9f16019475d77f1530a147ba736bf07f1fa51858a46dae2c67f7b91f781da897
  - `Topology/PlanarJordan/PlanarTubeSmoothing.lean` 604
    d546edbacfe90a6555e3d66c7e61e3cd6a458a4c3ec66c22aa29b233825a5de1
  - `Topology/PlanarJordan/PolarStrip.lean` 244
    50a23493bed20905f09a991ccba9a88f390277045ff46cbd544fd254325a1217
  - `Topology/PlanarJordan/PlanarArcSmoothing.lean` 261
    58508aa3ec4e704b97cdb2e74823a6b4da21f8f9bb21088d9c0d3894e98633df
  - `Topology/Manifold/PolarBandChart.lean` 210
    e5b05cb4b81181f53ebb0fdda2288a112119591196f5a336412d5cbe1adc0596
  - `Topology/Manifold/AnnulusCoreSteps.lean` 356
    d28563072e5a7cafb205ffe23c185ae3136734a4e1a03485aa62c7ab85bf5b2a
  - `Topology/Manifold/AnnulusCoreSmoothing.lean` 753
    361a73b0712b1d078383ae2ba4be5b105ebe3a7597910333a0f670f44999e55e
  - `Topology/PiecewiseLinear/SurfaceAnnulusShrink.lean` 607
    0720dd5a5d157a7eea19f2ff24115db380c87933610770afc9aa155e08032bd9
  - `Topology/PiecewiseLinear/RadialAnnulusSqueeze.lean` 196
    5479a8221140ebf3245c8644272c5af08961bdb6f9c90ebfa5a7c6c19d4ed2af
  - `Topology/PiecewiseLinear/BoundaryAnnulusEmbedding.lean` 130
    d83438b6369a44f3e771af9bb6a6fc15768663417e295af90b1743893aee890d
  - `Topology/PiecewiseLinear/SphereBandChart.lean` 206
    152e6b54a9671ac9b8c45b2ac71b7a006afcef38f92ed945e59f6939c70debb7
  - `Topology/PiecewiseLinear/AnnulusTamingSteps.lean` 226
    a43ab8a3dc861d488bb24045dbd7d762d93cef8ebcbf5a6cfb66944abad59f58
  - `Topology/PiecewiseLinear/SmoothAnnulusTaming.lean` 165
    704bcc531a216c4ae34a79e3dca0d722850911629a809dbeba324fb5dcc60b2c
- Checker, final versions, each exactly `Verified D:\differential-geometry-moise-int\DifferentialGeometry\<path> with no diagnostics; shared outputs unchanged.`
  for the seventeen paths above (`<path>` with backslashes). The chain StripExtension →
  PlanarSmoothCore → PlanarTubeSmoothing → PolarStrip → PlanarArcSmoothing → PolarBandChart →
  AnnulusCoreSteps → AnnulusCoreSmoothing → SmoothAnnulusTaming was re-verified in order on
  2026-09-23 (~15:30–15:55 UTC) after the two audit fixes below; the other eight are unchanged
  since their verification.
- Audit fixes: (1) `interior_closedSquare_zero_one` duplicated
  `Schoenflies.interior_closedSquare_zero_one` (`External/Schoenflies/ModelCurve.lean`): deleted,
  the Schoenflies lemma is used. (2) `unusedArguments`: the `IsManifold` instance was removed
  from `contDiffOn_chart_comp_of_mem_maximalAtlas` and `exists_isotopy_smooth_polar_arc`.
- Hypotheses of the endpoint: those of the skeleton leaf; all consumed (`T2Space`,
  `CompactSpace` by the collar extension `exists_homeomorph_of_boundary_isotopy`).

## exists_isSmoothEmbedding_sphere_of_isClosedEmbedding — STUCK (one sub-leaf)

- Statement TRUE (the image is a component of `∂M`, a closed smooth surface homeomorphic to `S²`;
  smooth structures on `S²` are unique). No counterexample.
- Proved bricks (new files):
  - `Topology/PiecewiseLinear/BoundarySphereComponent.lean` 111
    4fcd6844a987e9e628f85c3df2b7816ce91ce958f26439c99d76cb0d304dfa38 —
    (i) `isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding` (the image is clopen in
    the boundary surface; open by invariance of domain through stereographic charts),
    (ii) `exists_opens_boundaryManifold_homeomorph_sphere` (an open, closed, compact subsurface
    `W` of `BoundaryManifold (𝓡∂ 3) M` with `↑'' W = range ψ` and `W ≃ₜ S²`), and
    `nonempty_homeomorph_stdSimplexBoundary_three_sphere`.
  - `Topology/PiecewiseLinear/BoundarySurfaceEmbedding.lean` 118
    efd80c97c157b71b195a018de681ff8f212d9ffed2dac5bf8b63ab6eb385c65f —
    `isSmoothEmbedding_coe_of_boundary_surface_openPartialHomeomorph` and
    `isSmoothEmbedding_coe_of_diffeomorph_boundary_opens` (a diffeomorphism `N ≃ₘ W` onto an open
    subsurface of `∂M` is a smooth embedding into `M`).
  - Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BoundarySphereComponent.lean with no diagnostics; shared outputs unchanged.`
    and `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BoundarySurfaceEmbedding.lean with no diagnostics; shared outputs unchanged.`
- Probe `claude-moise-agent-c/ProbeSphereRecognition.lean` (checker `-Audit`): the leaf, verbatim
  (statement `diff`-identical to skeleton lines 223–229), is proved from (ii), the bridge and ONE
  sub-leaf; output: exactly one diagnostic, `ProbeSphereRecognition.lean:16:8: warning:
  declaration uses 'sorry'` (sorry count 1, nothing else).
- Missing sub-leaf (not proved, not reachable in this lease):
  `nonempty_diffeomorph_sphere_of_homeomorph_sphere {S : Type} [TopologicalSpace S] [T2Space S]
  [CompactSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  (h : S ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : Nonempty (sphere … ≃ₘ⟮𝓡 2, 𝓡 2⟯ S)`.
  Same content as `PHASE2_SMOOTHING_AUDIT.md` §2.6; no producer in the tree (no smooth planar
  Schoenflies, no Reeb theorem, no uniformization). Routes: Munkres smoothing of `h`
  (vertex step = `exists_isotopy_smoothing_surface_chart`, edge step = this batch's arc/tube
  smoothing, face step needs smooth Schoenflies in a chart with collar control plus extension of
  circle diffeomorphisms), or Morse (`exists_excellent_morse_function`, `χ = 2`, cancellation to
  two critical points, `Diff⁺(S¹)` connected, Reeb gluing).

## Batch 8 summary

- CLOSED 1 of 2 (annulus); sphere STUCK on one named sub-leaf, with its other inputs proved.
- Audit `AuditOpusC16.lean` over all nineteen modules: `Verified
  C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c\AuditOpusC16.lean with no diagnostics;
  shared outputs unchanged.` (axiom closure of every declaration within `propext`,
  `Classical.choice`, `Quot.sound`; thirteen linters clean).
- Aggregate import lines (not added to `DifferentialGeometry.lean`): one
  `import DifferentialGeometry.Topology.<path>` per file above (19 lines), e.g.
  `import DifferentialGeometry.Topology.PiecewiseLinear.SmoothAnnulusTaming`,
  `import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySphereComponent`,
  `import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySurfaceEmbedding`.

# Batch 9 isolated smooth-Schoenflies integration (2026-09-23)

Current lead: Claude. This lane follows the owner-supplied isolated-worktree plan.
Checkout D:/differential-geometry-smooth-int; branch codex/moise-smooth-integration;
initial HEAD 4b898b95fdb4532de0b1229d591177bc09b09e8f; initial tracked worktree clean.
Source batch revision 54ad4d8ec0408e71da2247daed5ecee2a574f7ec remains unverified.
Compiler token codex-smooth-integration-20260923; exact checkout and private output root
verified against the granted 334-module lease, expiring 2026-09-26T04:17:07.7791223Z.
The owner supplied the plan as this task's request; lane c executes step 3.
No Git writes, shared source/artifact writes, frozen statement edits or lease changes.
The compiler sequence is compile-order.txt: 144 modules, in recorded dependency order.
Every run invokes prepare-private-root-worktree.py with MOISE_CHECKOUT, then counts host
Lean processes and invokes the official checker with one process under this lease.
Receipts and wall times are saved under the private root/lane-c-verification-20260923.
Only header/module-docstring fixes are authorized during cone replay; a real proof error
stops the sequence at that module. External audits and face replacement await a clean cone.

## Per-module cone verification

- [1/144] DifferentialGeometry.Topology.Diffeomorph.CompactIsotopyComposition: 11.616 s; SHA-256 8256588e1b9883028bda0df88370d78031e9e74a0b25ec20b8f841b6ad5148d7.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\CompactIsotopyComposition.lean with no diagnostics; shared outputs unchanged.
- [2/144] DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport: 15.654 s; SHA-256 20c3643bf629e2d33f729a85551d021750102b9b8f15645b6cffc2a3c9252a84.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\ODE\Flow\IntegralCurveTransport.lean with no diagnostics; shared outputs unchanged.

### Authorized header-only correction: DifferentialGeometry/Analysis/ODE/Flow/CompactSupport.lean

No existing attribution was present. Added the repository standard contributor header
and a mathematical module docstring; all original source bytes remain in order.
Before SHA-256 82354cec8bc2ee3fa54d0362f08a86ab33fbde50090ab2af29f6f075a38064dd; after 2814c0f5cb01bcbbc7e5b283897377468473b436c56a5bae95c0b259ba131710.

```diff
--- a/DifferentialGeometry/Analysis/ODE/Flow/CompactSupport.lean
+++ b/DifferentialGeometry/Analysis/ODE/Flow/CompactSupport.lean
@@ -1,8 +1,15 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import Mathlib.Analysis.Calculus.ContDiff.RCLike
 import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
 import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
 import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
 import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.Manifold
+
+/-! Global flows of compactly supported vector fields and their smooth dependence. -/
 
 noncomputable section
 
```


### Authorized header-only correction: DifferentialGeometry/Analysis/Calculus/SmoothExtension/Compact.lean

No existing attribution was present. Added the repository standard contributor header
and a mathematical module docstring; all original source bytes remain in order.
Before SHA-256 1bcf391c03ca804895d7eb03d0049479644c8d6b46b628aee6a626caca37dfab; after 751e5b252ed220b49405a92e3b13f297c56b9cef1e06ea7a4a82fbbcd2eb74a5.

```diff
--- a/DifferentialGeometry/Analysis/Calculus/SmoothExtension/Compact.lean
+++ b/DifferentialGeometry/Analysis/Calculus/SmoothExtension/Compact.lean
@@ -1,5 +1,12 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
 import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
+
+/-! Compactly supported smooth extensions agreeing near compact sets. -/
 
 open Filter Set
 open scoped Topology ContDiff Manifold
```


### Stopped at module 3/144

DifferentialGeometry.Analysis.ODE.Flow.CompactSupport: checker exit 1; 53.967 s.
Evidence: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\003-DifferentialGeometry.Analysis.ODE.Flow.CompactSupport-180659967.result.json and adjacent checker log.

### CompactSupport source-preserving line wrapping

The first replay had Lean exit 0 and ten long-line warnings, with no proof errors.
Wrapped only those lines to satisfy the required 100-codepoint linter. Removing whitespace
from the before/after source yields identical text; no declaration or proof term was changed.
This is a formatting correction under the zero-diagnostic delivery gate.

```diff
--- a/DifferentialGeometry/Analysis/ODE/Flow/CompactSupport.lean
+++ b/DifferentialGeometry/Analysis/ODE/Flow/CompactSupport.lean
@@ -46,11 +46,14 @@
     (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) (t : ℝ) :
     Function.Injective (fun x : M => curveAt v hcomplete x t) := by
   intro x y h
-  have hx : curveAt v hcomplete (curveAt v hcomplete x t) (-t) = curveAt v hcomplete (curveAt v hcomplete y t) (-t) := by
+  have hx : curveAt v hcomplete (curveAt v hcomplete x t) (-t) =
+      curveAt v hcomplete (curveAt v hcomplete y t) (-t) := by
     exact congrArg (fun z : M => curveAt v hcomplete z (-t)) h
-  have h1 : curveAt v hcomplete (curveAt v hcomplete x t) (-t) = curveAt v hcomplete x (t + (-t)) := by
+  have h1 : curveAt v hcomplete (curveAt v hcomplete x t) (-t) =
+      curveAt v hcomplete x (t + (-t)) := by
     exact (curveAt_add v hv hcomplete x t (-t)).symm
-  have h2 : curveAt v hcomplete (curveAt v hcomplete y t) (-t) = curveAt v hcomplete y (t + (-t)) := by
+  have h2 : curveAt v hcomplete (curveAt v hcomplete y t) (-t) =
+      curveAt v hcomplete y (t + (-t)) := by
     exact (curveAt_add v hv hcomplete y t (-t)).symm
   have hz : t + (-t) = 0 := by ring
   rw [h1, h2, hz, curveAt_zero v hcomplete x, curveAt_zero v hcomplete y] at hx
@@ -267,7 +270,8 @@
     (v : (x : M) → TangentSpace I x)
     (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
       (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
-    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
+    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
+    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
     ContMDiffAt I I ∞
       (fun x : M => curveAt v hcomplete x t₀) x₀ := by
   let γ : ℝ → M := curveAt v hcomplete x₀
@@ -554,7 +558,8 @@
         (hz.comp (t₀, x₀) (contMDiffAt_snd (p := (t₀, x₀))))
     have hΨat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
         (fun q : ℝ × M => Ψ q.2 q.1) (t₀, y) := by
-      exact (hΨsm (t₀, y) (by constructor <;> [exact ⟨by linarith, by linarith⟩; exact hyU])).contMDiffAt
+      exact (hΨsm (t₀, y)
+        (by constructor <;> [exact ⟨by linarith, by linarith⟩; exact hyU])).contMDiffAt
         (prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
           (hUopen.mem_nhds hyU))
     have hcomp := hΨat.comp (t₀, x₀) hpair
@@ -684,14 +689,16 @@
       dsimp [η] at hsub
       nlinarith [hts, htri]
     have hxU : curveAt v hcomplete x s ∈ U := htx.2
-    have hstep : curveAt v hcomplete x t = curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
+    have hstep : curveAt v hcomplete x t =
+        curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
       have hh := curveAt_add v hv1 hcomplete x s (t - s)
       rw [show s + (t - s) = t by ring] at hh
       exact hh
     rw [hstep]
     exact hagree (curveAt v hcomplete x s) hxU (t - s)
       ⟨(abs_lt.mp htε).1, (abs_lt.mp htε).2⟩
-  have hmain : ContinuousAt (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) (t₀, x₀) := by
+  have hmain : ContinuousAt
+      (fun p : ℝ × M => Ψ (curveAt v hcomplete p.2 s) (p.1 - s)) (t₀, x₀) := by
     have hfst : ContinuousAt (fun p : ℝ × M => p.1 - s) (t₀, x₀) :=
       (continuousAt_fst : ContinuousAt (fun p : ℝ × M => p.1) (t₀, x₀)).sub continuousAt_const
     have hsnd : ContinuousAt (fun p : ℝ × M => curveAt v hcomplete p.2 s) (t₀, x₀) := by
@@ -783,7 +790,8 @@
       dsimp [η] at hsub
       nlinarith [hts, htri]
     have hxU : curveAt v hcomplete x s ∈ U := htx.2
-    have hstep : curveAt v hcomplete x t = curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
+    have hstep : curveAt v hcomplete x t =
+        curveAt v hcomplete (curveAt v hcomplete x s) (t - s) := by
       have hh := curveAt_add v hv1 hcomplete x s (t - s)
       rw [show s + (t - s) = t by ring] at hh
       exact hh
@@ -841,7 +849,8 @@
       (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
     (hsupp : IsCompact (tsupport v)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x₀ : M) :
     ContMDiffAt I I ∞
-      (fun x : M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
+      (fun x : M => curveAt v
+        (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
   exact contMDiffAt_curveAt_slice_nonneg v hv
     (exists_globalIntegralCurve_of_compactSupport v hv hsupp) ht₀ x₀
 
@@ -852,7 +861,8 @@
       (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
     (hsupp : IsCompact (tsupport v)) (t₀ : ℝ) (x₀ : M) :
     ContMDiffAt I I ∞
-      (fun x : M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
+      (fun x : M => curveAt v
+        (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t₀) x₀ := by
   exact contMDiffAt_curveAt_slice v hv
     (exists_globalIntegralCurve_of_compactSupport v hv hsupp) t₀ x₀
 
```

- [3/144] DifferentialGeometry.Analysis.ODE.Flow.CompactSupport: 21.388 s; SHA-256 de23fbc9fd43d69b4d7ca889e6f93e2bdbb02eae7dc7d7e5ce4bfbe61b3b158a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\ODE\Flow\CompactSupport.lean with no diagnostics; shared outputs unchanged.
- [4/144] DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow: 14.84 s; SHA-256 723dcb9970613ef904aab06251b3429166a4632aa9b847c854515718fac3d07a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\TimeDependentFlow.lean with no diagnostics; shared outputs unchanged.
- [5/144] DifferentialGeometry.Analysis.Calculus.Cutoff.Basic: 15.872 s; SHA-256 d6a5a9a42b864a36a1dd354f5eaec6afa7388ce170e33dc8cdfdf92a3436f1c0.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\Cutoff\Basic.lean with no diagnostics; shared outputs unchanged.
- [6/144] DifferentialGeometry.Analysis.Calculus.Cutoff.Compact: 43.989 s; SHA-256 d8dcdf1a700a0ff22f1325564b6a3d409abd023be1824d1c8b8297d7d4ccd6ea.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\Cutoff\Compact.lean with no diagnostics; shared outputs unchanged.
- [7/144] DifferentialGeometry.Analysis.Calculus.ProportionalTransport: 17.471 s; SHA-256 2f4b3c5450b0b9be5633ea429461c464062142ad97579012d487925a105a9251.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\ProportionalTransport.lean with no diagnostics; shared outputs unchanged.
- [8/144] DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Sign: 14.126 s; SHA-256 07f7b4d276785eb3525e1cb7311927827a799cf6b23aac730c42b802cb72fbab.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\ODE\Flow\LinearODE\Sign.lean with no diagnostics; shared outputs unchanged.
- [9/144] DifferentialGeometry.Analysis.ODE.TimeDependentFlow.LevelTransport: 30.197 s; SHA-256 8e15ded7edeafe941ac733b20bacb624faace9f689269fc0d24455205c33f9fc.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\ODE\TimeDependentFlow\LevelTransport.lean with no diagnostics; shared outputs unchanged.
- [10/144] DifferentialGeometry.Topology.Diffeomorph.LevelTransport: 15.171 s; SHA-256 84ea961248f01e56d7b10dab5bc8df5ddf42f77986fbd961b3844799ede459cb.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\LevelTransport.lean with no diagnostics; shared outputs unchanged.

### Stopped at module 11/144

External.ClassificationOfSurfaces.Moise.GeometricTriangulation: checker exit 1; 11.244 s.
Evidence: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\011-External.ClassificationOfSurfaces.Moise.GeometricTriangulation-181202911.result.json and adjacent checker log.

## Replay scope boundary at module 11 (awaiting owner/Claude lead decision)

The first ten modules now have zero-diagnostic private receipts. Module 11,
External.ClassificationOfSurfaces.Moise.GeometricTriangulation, returned Lean exit 0
but emitted exactly three linter.style.haveILetI suggestions at lines 571, 572 and 610.
The zero-diagnostic checker therefore returned failure; this is not a proof error.
The live module SHA-256 remains
b399cadf687e0e1ae120af633fef2a1c53723a6e9164034b9269000676fde29f.

A proposed repair replaces only the three reported local letI binders with let.
The automatic approval reviewer REJECTED the attempted repair: the isolated plan
explicitly authorized header/module-docstring fixes, and this vendored proof-source
change exceeds that scope. The proposal has NOT been applied. There are no vendor
source or modification-log edits from this attempt. The owner was asked to approve
this exact correction or return the boundary to Claude lead; dependent compilation
is paused pending that decision, without changing compiler leases.

Reviewable patch:
C:/Users/liao9/AppData/Local/Temp/codex-smooth-integration/lane-c-verification-20260923/PROPOSED-geometric-triangulation-style.diff
The source modification script is prepared privately but was not executed after rejection.

Independent preparation checks of both entry modules completed. SmoothSchoenflies:
273 DifferentialGeometry modules in the preparation closure, 85 needing private objects.
BoundaryGermExtension: 314 in that closure, 116 needing private objects. Neither preparation
reports a required module outside the recorded 144 compile targets. These counts exclude
External modules because the prepare script traverses DifferentialGeometry imports only;
the 334-module build plan additionally accounts for vendored and retained prerequisites.
Preparation is not compilation or an axiom audit. The final cone remains unverified.

### GeometricTriangulation style-linter correction

Raw Lean exit 0; only three `linter.style.haveILetI` suggestions.
Applied the suggested local `letI` to `let` substitutions, with no public signature change.
Recorded in External/ClassificationOfSurfaces/MODIFICATIONS.md; this is a linter repair,
not a mathematical proof repair. No linter suppression or compiler-budget change.

```diff
--- a/External/ClassificationOfSurfaces/Moise/GeometricTriangulation.lean
+++ b/External/ClassificationOfSurfaces/Moise/GeometricTriangulation.lean
@@ -568,8 +568,8 @@
     exact ⟨T.Vertex, T.vertexFintype, T.vertexDecidableEq, T.faces,
       T.faces_card, ⟨T.homeo⟩⟩
   · rintro ⟨V, hVfinite, hVdecidable, F, hF, ⟨h⟩⟩
-    letI : Fintype V := hVfinite
-    letI : DecidableEq V := hVdecidable
+    let : Fintype V := hVfinite
+    let : DecidableEq V := hVdecidable
     exact ⟨{ Vertex := V, faces := F, faces_card := hF, homeo := h }⟩
 
 namespace GeometricTriangulation
@@ -607,7 +607,7 @@
 theorem faces_isDualConnected_of_isVertexStarConnected [ConnectedSpace S]
     (hstar : TriangleFamily.IsVertexStarConnected T.faces) :
     TriangleFamily.IsDualConnected T.faces := by
-  letI : ConnectedSpace T.realization :=
+  let : ConnectedSpace T.realization :=
     T.homeo.connectedSpace_iff.mpr inferInstance
   have hpre : IsPreconnected (GeometricRealization T.Vertex T.faces) := by
     simpa only [Subtype.range_val] using
```


### Owner authorization, 2026-09-23: resume past the style-only gate

The owner explicitly approved the three proposed GeometricTriangulation local-instance
substitutions and allowed style warnings to be retained today to prioritize completion.
The exact reviewed three-line patch has now been applied and recorded in MODIFICATIONS.md.
Further style-only warnings may be recorded without cleanup, but real compiler errors,
source/hash instability, unexpected axioms, or out-of-lease compilation remain blocking.
Raw diagnostic counts and logs will be preserved; a style-warning exception will not be
reported as a zero-diagnostic pass. Official checker and lease files remain unchanged.
- [11/144] External.ClassificationOfSurfaces.Moise.GeometricTriangulation: 16.155 s; SHA-256 e5b5b859233e2b0b13060c594aeff4bde559cec0fd05916cb33e94477bd95667.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\GeometricTriangulation.lean with no diagnostics; shared outputs unchanged.
- [12/144] External.ClassificationOfSurfaces.Moise.PlaneComplex: 21.945 s; SHA-256 4d2a093712dedb9e8b5d9011382c1cd6683460aac2d1566ea9eb02232bdcf8c0.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PlaneComplex.lean with no diagnostics; shared outputs unchanged.
- [13/144] External.ClassificationOfSurfaces.Moise.LineSubdivision: 34.507 s; SHA-256 2e837cd57813e43eb34d7fdadf3073958068ca3c56b3befb03b1aff99661c142.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\LineSubdivision.lean with no diagnostics; shared outputs unchanged.
- [14/144] DifferentialGeometry.Topology.Diffeomorph.DisjointSupport: 41.865 s; SHA-256 bca9c94f6523682cf1a3ea5428333cdd0afc2c50c91017d03b32c2b8e287bf6e.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\DisjointSupport.lean with no diagnostics; shared outputs unchanged.
- [15/144] DifferentialGeometry.Analysis.Calculus.SmoothTransition: 36.307 s; SHA-256 4dda22b6625d64aa76b9e863ca74d8bc2a546053504ac43c24aba0545f5f58cf.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\SmoothTransition.lean with no diagnostics; shared outputs unchanged.
- [16/144] DifferentialGeometry.Analysis.Calculus.SmoothMax: 11.543 s; SHA-256 0059282bee91a8e211894553a7ecaec9989404c8b047513f291db495587e7524.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\SmoothMax.lean with no diagnostics; shared outputs unchanged.
- [17/144] DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact: 34.142 s; SHA-256 751e5b252ed220b49405a92e3b13f297c56b9cef1e06ea7a4a82fbbcd2eb74a5.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\SmoothExtension\Compact.lean with no diagnostics; shared outputs unchanged.

### Required header/module-docstring: DifferentialGeometry/Topology/Manifold/InverseFunction/ContDiffOn.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 484074d98a59d0dbbce9de3633ea6d6f09536ba6126726da6248c7eaf5ef5850; after 8d3bdf7fcf4b3da1428e3c8b55dcf4b82ce610a06a6994bf1ce6726f45a1e093.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\Manifold\InverseFunction\ContDiffOn.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/Manifold/InverseFunction/ContDiffOn.lean
+++ b/DifferentialGeometry/Topology/Manifold/InverseFunction/ContDiffOn.lean
@@ -1,7 +1,14 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
 import Mathlib.Geometry.Manifold.LocalDiffeomorph
 import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
 import Mathlib.Geometry.Manifold.MFDeriv.Atlas
+
+/-! Local diffeomorphisms from smooth maps with invertible derivatives on open sets. -/

 noncomputable section
 open scoped ContDiff Manifold Topology
```

### Required header/module-docstring: DifferentialGeometry/Topology/Manifold/InverseFunction.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 b8627a58f90a899148ef7f105e7d52677e1d51edf61bd89f474b92a4082b6bd3; after 8fdeced4c1daee67f7ae8f51d6ea730fc3074d7a6d687a559998e34a3661551d.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\Manifold\InverseFunction.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/Manifold/InverseFunction.lean
+++ b/DifferentialGeometry/Topology/Manifold/InverseFunction.lean
@@ -1,8 +1,15 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
 import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
 import Mathlib.Geometry.Manifold.LocalDiffeomorph
 import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
 import Mathlib.Geometry.Manifold.MFDeriv.Atlas
+
+/-! Local inverse and partial diffeomorphism constructions from invertible derivatives. -/

 noncomputable section
 open scoped ContDiff Manifold Topology
```

### Required header/module-docstring: DifferentialGeometry/Topology/Manifold/OpenEmbedding.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 89551dfbfbd1aed1d19ee5686beb96ea508f12089c2d8447d86a04a62f8ad572; after 8d3237b339b00dc6ecdd401207685dbc55c3995d300ed8ea71457f5373543d4e.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\Manifold\OpenEmbedding.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/Manifold/OpenEmbedding.lean
+++ b/DifferentialGeometry/Topology/Manifold/OpenEmbedding.lean
@@ -1,6 +1,13 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
 import Mathlib.Topology.Algebra.Module.FiniteDimension
 import DifferentialGeometry.Topology.Manifold.InverseFunction
+
+/-! Open embeddings and diffeomorphisms onto images of injective immersions. -/

 noncomputable section

```

### Required header/module-docstring: DifferentialGeometry/Analysis/Calculus/MapConvergence/Composition.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 b27ce496158ba56a9d5a7e80b78ca5466f390e314e2cca772b0fa981d1e87341; after c0800618fffe850522911978bf7fd5910b4d7bdc1ce1d2a53556e103ffa6609f.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Analysis\Calculus\MapConvergence\Composition.lean.diff.

```diff
--- a/DifferentialGeometry/Analysis/Calculus/MapConvergence/Composition.lean
+++ b/DifferentialGeometry/Analysis/Calculus/MapConvergence/Composition.lean
@@ -1,8 +1,15 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
 import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Pi
 import DifferentialGeometry.Analysis.Calculus.Inverse.RingBounds
 import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
 import Mathlib.Topology.MetricSpace.Thickening
+
+/-! Smooth convergence on compact sets under composition and algebraic operations. -/

 set_option autoImplicit false

```

### Required header/module-docstring: DifferentialGeometry/Analysis/Calculus/Inverse/MovingImplicit.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 8d708eda228b45de010effb030015b044be304f818a82660cd4aaa27d00df9c1; after 4be44c5efb229d84b9f54bc624daef34fbcba2c9ec7b79e86d6a1079cd07a5c6.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Analysis\Calculus\Inverse\MovingImplicit.lean.diff.

```diff
--- a/DifferentialGeometry/Analysis/Calculus/Inverse/MovingImplicit.lean
+++ b/DifferentialGeometry/Analysis/Calculus/Inverse/MovingImplicit.lean
@@ -1,9 +1,16 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
 import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
 import Mathlib.Analysis.Calculus.ImplicitContDiff
 import Mathlib.Topology.IsLocalHomeomorph
 import Mathlib.Topology.MetricSpace.Thickening
 import Mathlib.Topology.Separation.Regular
+
+/-! Smooth implicit roots in compact tubes and their convergence. -/

 set_option autoImplicit false

```

### Required header/module-docstring: DifferentialGeometry/Topology/Connected/Loop.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 34a8c729bc089cfafc85b1c0eee52fa18f928ba7a4ca939d61fe348751c25e93; after 6e424743cf63eee84aaab7bb6035c2e533ccfa4cfad23b1cc7cb0f8c821ca404.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\Connected\Loop.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/Connected/Loop.lean
+++ b/DifferentialGeometry/Topology/Connected/Loop.lean
@@ -1,4 +1,11 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import Mathlib.Topology.Order.IntermediateValue
+
+/-! Connectedness of simple closed curves with one point removed. -/

 open Set

```

### Required header/module-docstring: DifferentialGeometry/Topology/LoopSpace/AffineLift.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 0c7c049c86a342e0d1ac6c536291d69eac8bd4bde43935e62192841afde924b4; after 024d6dbe3656db2fe1903e6126a3b9599b3fa1d19e3083940386a73dca6d9e4c.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\LoopSpace\AffineLift.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/LoopSpace/AffineLift.lean
+++ b/DifferentialGeometry/Topology/LoopSpace/AffineLift.lean
@@ -1,5 +1,12 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
 import DifferentialGeometry.Topology.LoopSpace.Lipschitz
+
+/-! Circle maps induced by affine-periodic real lifts. -/



```

### Required header/module-docstring: DifferentialGeometry/Topology/LoopSpace/HomeomorphismOrientation.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 cb90de177d03a2fc64a7945de8a0990ba799534dcb249894c21f7be148da524c; after 33554ea8a2580953a0a1a3d3db5bee20f73ee8157019f3abea40d1db631fb759.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\DifferentialGeometry\Topology\LoopSpace\HomeomorphismOrientation.lean.diff.

```diff
--- a/DifferentialGeometry/Topology/LoopSpace/HomeomorphismOrientation.lean
+++ b/DifferentialGeometry/Topology/LoopSpace/HomeomorphismOrientation.lean
@@ -1,6 +1,13 @@
+/-
+Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: DifferentialGeometry contributors
+-/
 import DifferentialGeometry.Topology.LoopSpace.HomeomorphismLift
 import DifferentialGeometry.Topology.LoopSpace.AffineLift
 import Mathlib.Topology.Order.IntermediateValue
+
+/-! Orientation alternatives for real lifts of circle homeomorphisms. -/



```

### Required header/module-docstring: External/ClassificationOfSurfaces/TriangleMeshCrosscut.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 ffc240ceaa7282ab0fd64171d8204a222ec64e1eab4b4ac67d7336530521403b; after 62b8e9f3051864c0f95286b36e3e85b1454867a8c49868f6fe2d8b3eaa53455d.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\External\ClassificationOfSurfaces\TriangleMeshCrosscut.lean.diff.

```diff
--- a/External/ClassificationOfSurfaces/TriangleMeshCrosscut.lean
+++ b/External/ClassificationOfSurfaces/TriangleMeshCrosscut.lean
@@ -8,6 +8,8 @@
 -/
 import External.ClassificationOfSurfaces.Moise.FreeTriangle
 import DifferentialGeometry.External.Schoenflies.JordanClosed
+
+/-! Partitioning triangle meshes along Jordan-domain crosscuts. -/

 open LeanEval.Topology.ClassificationOfSurfaces.Moise (TriangleMesh)

```

### Required header/module-docstring: External/ClassificationOfSurfaces/PrePolygonDeletion.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 0b52f138d0195ff1dab7a757eae4979a3467957321d0573533950d29732195de; after 4ad84e3f49c53fc1a892d23454d1c754620dfc1c74defa7f6dc069a359f32e2b.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\External\ClassificationOfSurfaces\PrePolygonDeletion.lean.diff.

```diff
--- a/External/ClassificationOfSurfaces/PrePolygonDeletion.lean
+++ b/External/ClassificationOfSurfaces/PrePolygonDeletion.lean
@@ -13,6 +13,8 @@
 import DifferentialGeometry.External.Schoenflies.PrePolygonSep
 import DifferentialGeometry.External.Schoenflies.Graph.K33Land
 import DifferentialGeometry.External.Schoenflies.JordanClosed
+
+/-! Polygonal regions obtained by deleting free triangles. -/

 namespace Schoenflies

```

### Required header/module-docstring: External/ClassificationOfSurfaces/PrePolygonTriangulation.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 17f68b191dea414fdceddc681edc63d1fdb39225f55e56c6c069167453e69ba8; after 92aed2d98627852b89ce273052b819b4a6e42c0aee3b1e07f97ab24c35cf2ea8.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\External\ClassificationOfSurfaces\PrePolygonTriangulation.lean.diff.

```diff
--- a/External/ClassificationOfSurfaces/PrePolygonTriangulation.lean
+++ b/External/ClassificationOfSurfaces/PrePolygonTriangulation.lean
@@ -10,6 +10,8 @@
 import DifferentialGeometry.External.Schoenflies.PrePolygonSep
 import Mathlib.Analysis.Convex.SimplicialComplex.Basic
 import Mathlib.Analysis.Normed.Affine.AddTorsorBases
+
+/-! Triangulations of closed polygonal Jordan regions. -/

 open LeanEval.Topology.ClassificationOfSurfaces.Moise
   (Plane PlaneComplex TriangleMesh planePoint planePoint_apply_zero planePoint_apply_one
```

### Required header/module-docstring: External/ClassificationOfSurfaces/TriangleMeshGeometricFree.lean

Added only missing module/header documentation; existing attribution retained.
Code after removing block comments and whitespace is identical.
Before SHA-256 693a9d0961a7246d7ffd3c86a50a8d305a4b731ce25191bc345c6b8cb0fa1656; after 892b3cb79c377adb40a275bfd903c3f28355f22d7bf8b456e0644ca45f238d9d.
Exact patch: C:\Users\liao9\AppData\Local\Temp\codex-smooth-integration\lane-c-verification-20260923\remaining-header-diffs\External\ClassificationOfSurfaces\TriangleMeshGeometricFree.lean.diff.

```diff
--- a/External/ClassificationOfSurfaces/TriangleMeshGeometricFree.lean
+++ b/External/ClassificationOfSurfaces/TriangleMeshGeometricFree.lean
@@ -1,11 +1,3 @@
-import External.ClassificationOfSurfaces.Moise.FreeTriangle
-import DifferentialGeometry.External.Schoenflies.JordanSeparates
-import Mathlib.Analysis.LocallyConvex.Separation
-import Mathlib.Topology.Separation.Connected
-import External.ClassificationOfSurfaces.Moise.FreeTriangleMove
-import External.ClassificationOfSurfaces.TriangleMeshCrosscut
-import External.ClassificationOfSurfaces.PrePolygonTriangulation
-
 /-
 Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
@@ -20,6 +12,16 @@
 The finite-exclusion density proof is retained privately from FreshDenseSelection.lean.
 See GEOMETRIC_FREE_EXISTENCE.json for the exact native source and provenance.
 -/
+import External.ClassificationOfSurfaces.Moise.FreeTriangle
+import DifferentialGeometry.External.Schoenflies.JordanSeparates
+import Mathlib.Analysis.LocallyConvex.Separation
+import Mathlib.Topology.Separation.Connected
+import External.ClassificationOfSurfaces.Moise.FreeTriangleMove
+import External.ClassificationOfSurfaces.TriangleMeshCrosscut
+import External.ClassificationOfSurfaces.PrePolygonTriangulation
+
+/-! Geometrically free triangles in meshes of polygonal Jordan regions. -/
+

 open LeanEval.Topology.ClassificationOfSurfaces.Moise (TriangleMesh)

```
- [18/144] DifferentialGeometry.Topology.FiberwiseHomeomorph: 9.206 s; SHA-256 bcdf1452388d488e017f50886b0460744f2906b99e895cfacc050669705a2edb.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\FiberwiseHomeomorph.lean with no diagnostics; shared outputs unchanged.
- [19/144] DifferentialGeometry.Topology.Diffeomorph.Fiberwise: 12.259 s; SHA-256 aba9795ecc704de008febd0e931833255ee34801b6e27d0180329d4029004338.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\Fiberwise.lean with no diagnostics; shared outputs unchanged.
- [20/144] DifferentialGeometry.Topology.Diffeomorph.LocalizedGraph: 13.627 s; SHA-256 adf799beb2992a0ac33edc53ff042b21e6a23c113d7f5a70008b12752ee8637a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\LocalizedGraph.lean with no diagnostics; shared outputs unchanged.
- [21/144] DifferentialGeometry.Topology.Planar.CornerRounding: 18.289 s; SHA-256 19955c5cdbb33f1971c1de716abf5c04ee4b97226b3935b7cb5d8b268e954a62.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\CornerRounding.lean with no diagnostics; shared outputs unchanged.
- [22/144] DifferentialGeometry.Analysis.Calculus.SmoothCorner: 12.292 s; SHA-256 48b56d063ab34b56c6cd995c13872126f8c2497cd72c060fd5ed1acfd68d4549.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\SmoothCorner.lean with no diagnostics; shared outputs unchanged.
- [23/144] DifferentialGeometry.Analysis.Calculus.CurveSubdivision: 36.301 s; SHA-256 12c0528f877586bb1f7fec930a6c2790e659f0bbb96adbfb93d57e7e4c0832d2.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\CurveSubdivision.lean with no diagnostics; shared outputs unchanged.
- [24/144] DifferentialGeometry.Analysis.Calculus.PolygonalRounding: 15.625 s; SHA-256 c36067a2000d49fdaa929213b12276d690c8641b77b5d85507646ce95bf6167c.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\PolygonalRounding.lean with no diagnostics; shared outputs unchanged.
- [25/144] DifferentialGeometry.Topology.PlanarJordan.LocalSides: 11.349 s; SHA-256 fac688b0b1f57c7d52ea1170bea39d3ab6b584d65eb966fbc715f5a42f3b0eb6.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\PlanarJordan\LocalSides.lean with no diagnostics; shared outputs unchanged.
- [26/144] External.ClassificationOfSurfaces.Moise.AmbientHomeomorph: 10.491 s; SHA-256 8903881795b59e9ab470d9209cf02a13f763c952220727454e1b3768ffdd949c.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\AmbientHomeomorph.lean with no diagnostics; shared outputs unchanged.
- [27/144] External.ClassificationOfSurfaces.Moise.ElementaryMove: 16.769 s; SHA-256 20b9fe1d543074e09d3621315d53f8860e93108544c94a70d93be8f92eb89db7.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\ElementaryMove.lean with no diagnostics; shared outputs unchanged.
- [28/144] External.ClassificationOfSurfaces.Moise.FreeTriangle: 13.193 s; SHA-256 65b813c47ce92b21b246736bb828cafd7af12f0940f3d6c66699892081e4f389.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\FreeTriangle.lean with no diagnostics; shared outputs unchanged.
- [29/144] External.ClassificationOfSurfaces.TriangleMeshCrosscut: 12.485 s; SHA-256 62b8e9f3051864c0f95286b36e3e85b1454867a8c49868f6fe2d8b3eaa53455d.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\TriangleMeshCrosscut.lean with no diagnostics; shared outputs unchanged.
- [30/144] DifferentialGeometry.Topology.Planar.PolygonVertexCharts: 15.557 s; SHA-256 ac9356e0f8f38c2d808313139baa7f55e98041693640c9a8b0c5509420b87d5b.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\PolygonVertexCharts.lean with no diagnostics; shared outputs unchanged.
- [31/144] DifferentialGeometry.Topology.Planar.VertexRoundingProfile: 13.949 s; SHA-256 c02db661cc976036d8b3ffafeeff26cad0874e7cb6a17b1679625e3858caa767.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\VertexRoundingProfile.lean with no diagnostics; shared outputs unchanged.
- [32/144] DifferentialGeometry.Topology.Planar.CornerNormalization: 14.842 s; SHA-256 018ad88404adee68d0868ddd54b812c5fd6e6cc0516ed2109bf7f93c1c6160b1.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\CornerNormalization.lean with no diagnostics; shared outputs unchanged.
- [33/144] DifferentialGeometry.Analysis.Convex.SegmentGerm: 9.297 s; SHA-256 e1348e54657ff1a730dd6e71ee0b74d724ad225e6046a113dab337fd7d117ad5.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Convex\SegmentGerm.lean with no diagnostics; shared outputs unchanged.
- [34/144] DifferentialGeometry.Topology.Planar.PolygonCorners: 12.223 s; SHA-256 f85f67da9bc8ee424776663e4f96b29a6232740b8f4e0c94f4c1df7f30e4427a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\PolygonCorners.lean with no diagnostics; shared outputs unchanged.
- [35/144] DifferentialGeometry.Topology.Planar.CornerReanchoring: 15.519 s; SHA-256 131ffe20ea93e1b5070508b7394c8e1194dc1d2b55c421174345713f2b776fea.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\CornerReanchoring.lean with no diagnostics; shared outputs unchanged.
- [36/144] DifferentialGeometry.Topology.Compactness.FiniteReplacement: 7.887 s; SHA-256 81e6ff8c9113c27f13d81fbbe25671c81cb435f0f62718c11efadd54bcb52685.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Compactness\FiniteReplacement.lean with no diagnostics; shared outputs unchanged.
- [37/144] DifferentialGeometry.Topology.Planar.VertexReplacement: 16.246 s; SHA-256 a7d7e9faf35c57bbe1a4939b38d513f65f036f247860bd2a5ca7fcad909b5d72.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\VertexReplacement.lean with no diagnostics; shared outputs unchanged.
- [38/144] DifferentialGeometry.Analysis.Calculus.RegularRegion: 12.034 s; SHA-256 7a5152fe9c78358a3c167dce04aed87236d142903ebd6ae21c139ac5adaf9126.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Calculus\RegularRegion.lean with no diagnostics; shared outputs unchanged.
- [39/144] DifferentialGeometry.Analysis.Convex.AffineBasis: 10.51 s; SHA-256 711d4ab7d8dcaf505d6a0a2d8ac21a1bfb8871b9312fe3fd42f89cebca8d2a8a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Convex\AffineBasis.lean with no diagnostics; shared outputs unchanged.
- [40/144] DifferentialGeometry.Analysis.Convex.TriangleComplement: 13.52 s; SHA-256 a5d92244d5a614009675bb90f42755b4f269553544d74a6729b54d837fa3b63a.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Convex\TriangleComplement.lean with no diagnostics; shared outputs unchanged.
- [41/144] DifferentialGeometry.Analysis.Convex.SegmentSigns: 9.084 s; SHA-256 789b0c59e9771c071e7a489515b6e5de8270cd8c66515004efa5d25989e4c664.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Analysis\Convex\SegmentSigns.lean with no diagnostics; shared outputs unchanged.
- [42/144] External.ClassificationOfSurfaces.Moise.CommonSubdivision: 13.793 s; SHA-256 5d949da03472d13edcc2d0649b2e419b3352d24d4b862613474d82b6519e5114.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\CommonSubdivision.lean with no diagnostics; shared outputs unchanged.
- [43/144] External.ClassificationOfSurfaces.Moise.ThinKiteMove: 18.595 s; SHA-256 8fe085394b4e1db8b113ab163e438d589a93df8c183b838cb2724d5988736f3e.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\ThinKiteMove.lean with no diagnostics; shared outputs unchanged.
- [44/144] External.ClassificationOfSurfaces.Moise.FreeTriangleMove: 16.622 s; SHA-256 89ba8a7ce3dae980698a8147ffea72d61a72aba311b377b43cdc7f141037df3f.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\FreeTriangleMove.lean with no diagnostics; shared outputs unchanged.
- [45/144] External.ClassificationOfSurfaces.Moise.ConeExtension: 15.755 s; SHA-256 465d923ca7ea26105b5710236e871e0fbad104736e4ccc2e99b2fb000583b05e.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\ConeExtension.lean with 1 owner-approved style warnings; 6 diagnostic lines retained; shared outputs unchanged.
- [46/144] External.ClassificationOfSurfaces.Moise.FinitePLHomeomorph: 13.569 s; SHA-256 9eb341d47703a0c2ea283fa796284aed74e3592e3de4972676e4dca497be7324.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\FinitePLHomeomorph.lean with no diagnostics; shared outputs unchanged.
- [47/144] External.ClassificationOfSurfaces.Moise.PLMoves: 11.918 s; SHA-256 6a20861deddc596eaa6a66019859afec3ad0c0f960026db93224f89936006e8d.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PLMoves.lean with no diagnostics; shared outputs unchanged.
- [48/144] External.ClassificationOfSurfaces.Moise.PolygonalJordan: 20.174 s; SHA-256 5ef0ebe4265ac5a62ee3d5368ecab854c81eb9fc12b5fd88dfa00b9f0a7ac315.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PolygonalJordan.lean with 1 owner-approved style warnings; 6 diagnostic lines retained; shared outputs unchanged.
- [49/144] External.ClassificationOfSurfaces.Moise.PolygonalPolyhedron: 18.798 s; SHA-256 c0f122c0616898ffa080e4b3e3c5865d0f031b72b1e4e971de906a3268a25e9f.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PolygonalPolyhedron.lean with no diagnostics; shared outputs unchanged.
- [50/144] External.ClassificationOfSurfaces.Moise.PolygonalCrosscut: 17.621 s; SHA-256 0420d5bd8c7b670506213a8d70c58553acf51e199628d396d9ee46507fd3c678.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PolygonalCrosscut.lean with 7 owner-approved style warnings; 42 diagnostic lines retained; shared outputs unchanged.
- [51/144] External.ClassificationOfSurfaces.Moise.PolygonalSchoenflies: 17.836 s; SHA-256 0344dadd7aa5dd24e5af709fd2d774ab165ced74343965237287efc0fcb665e9.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\Moise\PolygonalSchoenflies.lean with 1 owner-approved style warnings; 6 diagnostic lines retained; shared outputs unchanged.
- [52/144] External.ClassificationOfSurfaces.PrePolygonDeletion: 40.858 s; SHA-256 4ad84e3f49c53fc1a892d23454d1c754620dfc1c74defa7f6dc069a359f32e2b.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\PrePolygonDeletion.lean with no diagnostics; shared outputs unchanged.
- [53/144] DifferentialGeometry.Topology.Planar.PolygonGraphCharts: 33.57 s; SHA-256 d8a577424c513cd06c223aeeb40e362223248007de317f02226a1e80c70eb0ae.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\PolygonGraphCharts.lean with no diagnostics; shared outputs unchanged.
- [54/144] DifferentialGeometry.Topology.Planar.PolygonIsotopy: 35.768 s; SHA-256 4e016fdeca26f81ec2ee56490d6b1370ab5261c5ca6eb5682bc8bef1561f0b4d.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\PolygonIsotopy.lean with no diagnostics; shared outputs unchanged.
- [55/144] DifferentialGeometry.Topology.Planar.PolygonRounding: 161.347 s; SHA-256 4ed94241f260264de8693bd573ddeb9fa6e7c109c092d3a17d5f35f0ff18b5d5.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\PolygonRounding.lean with no diagnostics; shared outputs unchanged.
- [56/144] DifferentialGeometry.Topology.Diffeomorph.Radial: 15.49 s; SHA-256 85b1b5f51e97576190fec1dad06b4c3edb68f69f04841a1a9d011f2598a8aca3.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\Radial.lean with no diagnostics; shared outputs unchanged.
- [57/144] DifferentialGeometry.Topology.Diffeomorph.Convex: 14.388 s; SHA-256 94da4d41b42ed36e29d257f61b6f8681ac1e91dc575eb68391414e9306633c01.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Diffeomorph\Convex.lean with no diagnostics; shared outputs unchanged.
- [58/144] DifferentialGeometry.Topology.Planar.TriangleRounding: 20.994 s; SHA-256 84416a6659cf8c78030df9458e35b4f7353ffa0982d25b5b7741cb908658a066.
  Verified D:\differential-geometry-smooth-int\DifferentialGeometry\Topology\Planar\TriangleRounding.lean with no diagnostics; shared outputs unchanged.
- [59/144] External.ClassificationOfSurfaces.PrePolygonTriangulation: 16.559 s; SHA-256 92aed2d98627852b89ce273052b819b4a6e42c0aee3b1e07f97ab24c35cf2ea8.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\PrePolygonTriangulation.lean with no diagnostics; shared outputs unchanged.
- [60/144] External.ClassificationOfSurfaces.TriangleMeshGeometricFree: 58.609 s; SHA-256 892b3cb79c377adb40a275bfd903c3f28355f22d7bf8b456e0644ca45f238d9d.
  Verified D:\differential-geometry-smooth-int\External\ClassificationOfSurfaces\TriangleMeshGeometricFree.lean with no diagnostics; shared outputs unchanged.

## Owner-requested collaborator handover, 2026-09-23

The owner requested transferring the work to a faster-compiling collaborator. Lane c
stopped its own controller/checker and its subagents; a fresh process inspection found
zero matching lane compiler processes. No other worker, shared artifact or lease was changed.
The controller and checker were stopped at the start of target 61, before an accepted receipt.

Current-byte-checked consecutive pass count: 60/144. Of these, 56 have zero diagnostics;
four have the owner's approved style-only warnings (10 total): ConeExtension (1),
PolygonalJordan (1), PolygonalCrosscut (7), PolygonalSchoenflies (1). All raw logs and
counts are retained, and the warning-only receipts were reclassified during handover.
Last pass: target 60 External.ClassificationOfSurfaces.TriangleMeshGeometricFree.
Resume: target 61 DifferentialGeometry.Topology.Planar.PolygonDisk, StartIndex 60, Count 84.
No genuine proof error has been found. The complete cone, its two endpoints, final axiom
and linter audits, and the chart-level single-face lemma are not yet verified.

Portable handover:
C:/Users/liao9/AppData/Local/Temp/codex-smooth-integration/handover-to-collaborator-20260923/README.md
C:/Users/liao9/AppData/Local/Temp/codex-smooth-integration/handover-to-collaborator-20260923.zip
ZIP SHA-256 370924c7d46bbf59a5f7e32e7bc32e7b962ea7f9d7bd50ec19b47fae03f36c78.
The archive has 464 files and includes exact source overlays/patch, 16 vendor records,
compile plan, opt-in style classifier/checker, the 60 receipts and logs, historical helper
proof evidence, and explicitly UNVERIFIED planar/chart-level drafts. The archive checksum
and every packaged file hash were checked. Compiler binaries and leases are not included.

Published base: origin/codex/moise-smooth-integration at
4b898b95fdb4532de0b1229d591177bc09b09e8f. Fifteen tracked Lean files have this lane's
uncommitted header/style changes; the append-only log and ignored vendor MODIFICATIONS
also changed. No commits/pushes were made by this lane. The source patch excludes the
append-only log; its exact snapshot is provided separately.

A recipient on another host or source path must rebuild locally: these private receipts
bind the Windows worktree path and are progress evidence, not portable acceptance.
The actual lead remains Claude. No handover was sent to a historical Codex task or an
inferred recipient; the package is ready for the owner/current lead to route correctly.
