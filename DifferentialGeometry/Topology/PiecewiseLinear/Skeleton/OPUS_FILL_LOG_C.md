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
