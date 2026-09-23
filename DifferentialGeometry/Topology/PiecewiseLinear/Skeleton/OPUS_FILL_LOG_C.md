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
