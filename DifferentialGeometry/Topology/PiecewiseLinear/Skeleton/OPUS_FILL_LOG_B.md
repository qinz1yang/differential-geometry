# Opus fill log, lease b (`claude-agent-b-20260919`)

Target skeleton: `Skeleton/Section30Torus.lean` (frozen leaves 1, 2 and 4 of the seven).
Order of work: leaf `IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus` first
(most infrastructure present), then the recognition leaf, then the triangulation leaf.

## IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/NontrivialKernelInSolidTorus.lean`
  (SHA-256 `e491c21c7bc663fd9185bc3d4b44d8ae7d5d9cb8e1a53ab5d0194ed01700b283`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.NontrivialKernelInSolidTorus`
- New public names (grepped tree-wide, unique):
  `IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus` (the leaf, statement
  byte-identical to the skeleton, checked by script),
  `mem_interior_of_homeomorph_closedBall_prod_sphere`,
  `exists_ne_one_map_eq_one_of_multiplicative_intProd`.
- Success line (2026-09-22T20:31Z):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\NontrivialKernelInSolidTorus.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (external probe `claude-moise-agent-b/AuditLeaf3.lean`, `-Audit`): all three
  names depend on `[propext, Classical.choice, Quot.sound]` only.
- Route: invariance of domain (`isOpenMap_of_continuous_injective` on the charted
  `B² × S¹`) puts `φ⁻¹(B² × S¹)` in `interior S`; the radial homotopy
  `(t, x) ↦ φ⁻¹((1 - t)·v, θ)` stays in `interior S` and deforms the inclusion into
  `T → S¹ → interior S`; `ℤ² → ℤ` is never injective, and the kernel element is transported
  back through `pathToCircle_nullhomotopic_iff`.
- Gemini G016 claim ("missing ambient/intrinsic interior identification") was only half true:
  the full identification is not needed; the one inclusion used is three lines of existing
  invariance of domain.
- Compiles: 2 module checks (15 s each) + 1 audit.

## IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/TorusOfOrientableEulerCharZero.lean`
  (767 lines, SHA-256 `be43c41acb92fb0c75e9bd8e3dc8cbbd3fdb095451a6c7a259fe4951316b4784`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.TorusOfOrientableEulerCharZero`
- New public names (grepped tree-wide; unique apart from the skeleton's own `sorry` copy of the leaf):
  `IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero` (leaf,
  statement byte-identical to the skeleton, checked by script),
  `exists_cone_disk_of_isPLSphere_one`,
  `IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero`,
  `IsCombinatorialManifold.nonempty_homeomorph_torus_of_isPreconnected_sdiff`,
  `isPreconnected_insert_biUnion_convexHull_edgeGraphFace`,
  `IsCombinatorialManifold.exists_isPLSphere_one_isPreconnected_sdiff`.
- Success line (2026-09-22T21:01Z):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TorusOfOrientableEulerCharZero.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditLeaf1.lean`, `-Audit`): all six names depend on
  `[propext, Classical.choice, Quot.sound]` only.
- Route: tree/cotree gives a polygon `J` with connected complement whenever `χ ≠ 2`; the
  existing `exists_connected_annulus_complement` cuts along `J`; the complement `R` (χ = 0, two
  boundary polygons) is lifted to `E × ℝ`, capped by two cones on opposite sides, recognised as
  a sphere by `isPLSphere_two_of_faceEulerChar_eq_two`, and mapped onto a prism boundary by
  `exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk`, which identifies `R` with `∂Δ × [0,1]`;
  the bicollar and `R` glue (`isCylindricalDiagram_piecewise`) to a cylindrical diagram over a
  polygon, `isPLCirclePositive_of_isOrientable_cylindricalDiagram` + pseudo-isotopy untwist
  the end map, and `exists_homeomorph_prod_circle_of_eq_ends` gives `K ≃ₜ S¹ × S¹`.
- Hypothesis producers: `hL`, `hLc`, `hLo`, `hχ` are exactly the fields returned by
  `IsToroidalShell.exists_separating_surface_bettiOne_eq_two` in the skeleton assembly; the
  intermediate theorem additionally uses a polygon `J`, supplied by
  `exists_isPLSphere_one_isPreconnected_sdiff` from `hL`, `hLc` and `χ ≠ 2`.
- Gemini G014 claim ("classification of surfaces is not formalized") was literally true but
  not a blocker: the genus-one case only needed one cut, sphere recognition and the existing
  cylindrical-diagram monodromy API.
- Compiles: 9 module checks (12–15 s each) + 1 audit.

## IsPLTorus.exists_combinatorial_triangulation — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsCombinatorialTriangulation.lean`
  (865 lines, SHA-256 `61c6be8dc665fa9ed0587134f84960747c73b516081b30834f1d4f9129b8591e`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation`
- New public names (grepped tree-wide; unique apart from the skeleton's own `sorry` copy of the leaf):
  `IsPLTorus.exists_combinatorial_triangulation` (leaf, statement byte-identical to the
  skeleton, checked by script), `mem_nhdsWithin_image_of_homeomorph_sphere_prod`,
  `exists_ball_chart_of_homeomorph_sphere_prod`, `exists_mem_ball_apply_one_neg_of_injOn`,
  `affineIndependent_triple_of_mem_faces`, `linearCombination_triple_apply`,
  `mem_stdSimplex_triple`, `subset_or_subset_of_hinge`, `isPreconnected_ball_sdiff_center`,
  `biUnion_convexHull_superset_mem_nhdsWithin`, `mem_openSimplex_pair`,
  `false_of_maximal_face_of_card_le_two`, `exists_card_three_superset_of_homeomorph`,
  `range_vecCons_triple`, `exists_second_triangle_of_homeomorph`,
  `edgeGraph_geometricLink_connected_of_homeomorph`,
  `isCombinatorialManifold_two_of_homeomorph_sphere_prod`.
- Success line (2026-09-22T21:23Z):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsCombinatorialTriangulation.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditLeaf2.lean`, `-Audit`): all seventeen names depend
  on `[propext, Classical.choice, Quot.sound]` only.
- Route: any triangulation `K` of `T` (`IsPolyhedron.exists_simplicialComplex`) works.
  Invariance of domain on the charted torus gives (i) injective planar images are open in
  `T` and (ii) ball charts inside any neighbourhood. An explicit piecewise-affine planar
  parametrisation of two triangles hinged along an edge is then open in `T`, so no further
  face contains that edge (no 3-simplices, at most two triangles per edge); a half-plane
  argument through simplex coordinates excludes maximal faces of dimension ≤ 1 and edges in
  only one triangle; a chart ball minus its centre is connected, which rules out a
  disconnected vertex link (closed star split into two closed pieces meeting only at `v`).
  `isCombinatorialManifold_one_iff` + `isPLSphere_one_of_edgeGraph_connected` finish.
- Hypothesis producers: only `hT : IsPLTorus T` (polyhedron + torus homeomorphism), which the
  skeleton's `moise307_of_moise306_of_moise252` takes from `Moise306`.
- Gemini G015 claim ("requires link recognition and triangulating general 2-polyhedra"):
  triangulation already existed; topological link recognition was indeed absent, but only the
  two-dimensional case was needed and it follows from the existing invariance of domain.
- Compiles: 10 module checks (13–34 s each) + 1 audit.


(Lead note 2026-09-22: two modules renamed — `NonemptyHomeomorphTorusOfIsOrientableOfEulerCharEqZero` → `TorusOfOrientableEulerCharZero`, `ExistsNontrivialFundamentalGroupKernelInSolidTorus` → `NontrivialKernelInSolidTorus` — because their import lines exceeded 100 characters.)

# Batch 2

Target skeleton: `Skeleton/Section33Approximation.lean` (Moise 33.1), leaves in the order
tube product, Lemma 12, Lemma 8, Lemma 2, Lemma 9.

## section33_tube_product — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/DerivedNeighborhoodRayEmbedding.lean`
  (793 lines, SHA-256 `e9e4ff97d4254a49e121cde95625921ecda7be65ba519e553a8974028a1af451`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding`
  (the module also imports `Mathlib.Topology.LocalAtTarget` for `IsClosedMap.restrictPreimage`).
- New public names (grepped tree-wide, all unused before; the leaf is unique apart from the
  skeleton's own `sorry` copy and the assembly copy in `Skeleton/DerivedNeighborhoodComplement`):
  `barycentricCoordinate_pos_of_mem_openSimplex`, `barycentricCoordinate_eq_zero_of_notMem_vertices`,
  `sum_barycentricCoordinate`, `barycentricCoordinate_pos_of_forall_le`,
  `barycentricCoordinate_add_smul`, `add_smul_mem_convexHull_of_barycentricCoordinate_nonneg`,
  `barycentricCoordinate_vertex_of_mem`, `barycentricCoordinate_subcomplexBarycentricProjection`,
  `subcomplexBarycentricMass_eq_mul_of_barycentricCoordinate_eq_mul`,
  `subcomplexBarycentricProjection_eq_of_barycentricCoordinate_eq_mul`,
  `exists_barycentricCoordinate_le_of_mem_derivedNeighborhood`,
  `mem_derivedNeighborhood_of_barycentricCoordinate_le`,
  `barycentricCoordinate_eq_zero_of_mem_subcomplex`,
  `mem_subcomplex_of_barycentricCoordinate_eq_zero`,
  `notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le`,
  `mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt`,
  `frontier_derivedNeighborhood_space_subset`,
  `exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood`,
  `barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection`,
  `smul_add_smul_subcomplexBarycentricProjection_notMem`,
  `smul_add_smul_subcomplexBarycentricProjection_mem_interior`,
  `eq_of_smul_add_smul_subcomplexBarycentricProjection_eq`,
  `exists_mem_frontier_derivedNeighborhood_of_mem_interior`,
  `range_derivedNeighborhoodRay_of_subset_interior`,
  `isEmbedding_derivedNeighborhoodRay_of_subset_interior`,
  `nonempty_homeomorph_derivedNeighborhood_interior_sdiff_of_subset_interior`,
  `derivedNeighborhood_space_subset_interior`, and the leaf `section33_tube_product` (statement
  and `variable` block byte-identical to the skeleton, checked by script).
- Success line (2026-09-22T15:08:29-07:00):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedNeighborhoodRayEmbedding.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditBatch2Leaf1.lean`, `-Audit`, 15:09:26):
  `Verified ...\AuditBatch2Leaf1.lean with no diagnostics; shared outputs unchanged.` — every
  declaration of the module within `propext`, `Classical.choice`, `Quot.sound`; the thirteen
  environment linters pass.
- Route: in the first derived `A'`, `N = derivedNeighborhood A K` is the set where a vertex of
  `K'` carries a maximal barycentric weight (`mem_faceNeighborhood_space_iff` read globally
  through `barycentricCoordinate`); if `N ⊆ interior |A|`, a strict maximum gives an ambient
  neighbourhood inside `N` (continuity of the coordinates), and a tie with a noncore vertex is a
  frontier point (push towards that vertex). Along `(1 - t) b + t p(b)` the core weights scale
  by `1 - t + t / m(b)` and the others by `1 - t`, so the ray point misses `|K|`, lies in
  `Int N` for `t > 0`, and `t = m(x) (1 - c / a)` is read off `x` (injectivity); the inverse
  point `(x - t p(x)) / (1 - t)` is shown to lie on the frontier by the same weights (range).
  The embedding is the restriction of the compact map on `Fr N × [0,1]` to the preimage of
  `|K|ᶜ` (closed map, injective there). `derivedNeighborhood_space_subset_interior` supplies
  `N ⊆ interior |A|` from `IsCombinatorialManifoldWithBoundary (n + 1) A`, finrank `n + 1` and
  `|K| ⊆ interior |A|` via `frontier_space_eq_boundaryComplex_space_of_finrank`: a positive core
  weight at a boundary point would put a simplex of `K` into the boundary complex. The frozen
  leaf then follows the skeleton `DerivedNeighborhoodComplement` assembly (image transport by
  `nonempty_homeomorph_interior_sdiff_image_of_isCompact`).
- Side effect for the lead: the two UNREVIEWED leaves of `Skeleton/DerivedNeighborhoodComplement`
  (FREE_INPUTS B1.m) are proved here in general form: `isEmbedding_derivedNeighborhoodRay A K hA
  hKA hKint` is `isEmbedding_derivedNeighborhoodRay_of_subset_interior A K hKA
  (derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint)`
  (same for `range_…`), up to that skeleton's private `DecidableEq` instance, which is
  definitionally the classical one used here. No hypothesis of the skeleton leaves was needed
  beyond those; arbitrary subcomplexes (isolated vertices, nonpure, disconnected) are covered.
- Hypothesis producers: only `ht : IsTube K N C D Dbd h N'` (fields `derivedModel`, `unionEq`,
  `isNeighborhood`, `isEmbedding`, `imageEq`), produced by `exists_section33TubeFrame`.
- Gemini G042 / FILL_LOG item 5 blocker ("no regular-neighbourhood product producer") was true
  of the tree but not an obstruction: the barycentric ray and its continuity existed; the missing
  part was the weight bookkeeping above.
- Compiles: 4 module checks (≈13 s each) + 4 audit runs (two failed on a PowerShell-encoded
  probe, one on an unused `FiniteDimensional` instance, fixed).

## section33_faceEulerChar_handlePiece — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/HandlePieceEulerChar.lean`
  (1072 lines).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar`
  (it imports `DerivedNeighborhoodRayEmbedding` of the previous section and the batch-1 module
  `TorusOfOrientableEulerCharZero`, both to be registered first).
- New public names (grepped tree-wide, all unused before; the leaf is unique apart from the
  skeleton's own `sorry` copy): `fundamentalGroupoidLoopValue` (def, `V`-valued),
  `fundamentalGroupoidLoopValue_trans`, `fundamentalGroupoidLoopValue_cast`,
  `fundamentalGroupoidLoopValue_mk_eq_of_forall_apply_eq`, `fundamentalGroupoidLoopValue_loop`,
  `exists_linearMap_fieldHurewiczOne`, `finrank_fieldHomology_one_le_of_fundamentalGroup_map_bijective`,
  `IsPolyhedron.isPLHomeomorphOn_linearMap_image`, `IsConnected.union_biUnion`,
  `IsPolyhedron.eulerChar_biUnion`, `IsPLSphere.homologyEulerChar_eq_zero`,
  `IsPLBall.homologyEulerChar_eq_one`, `IsCombinatorialManifoldWithBoundary.eulerChar_add_card_le_two`,
  `IsPolyhedron.eulerChar_biUnion_of_inter`, `isEmbedding_derivedNeighborhoodRay_Ico_and_range`,
  `nonempty_homotopyEquiv_prod_Ico`, `nonempty_homeomorph_sdiff_image`,
  `IsHandleDecompositionOfTube.inter_inter_eq_empty`, `IsTube.isConnected_space_of_isConnected`,
  `IsTube.bettiOne_sdiff_image_eq`, `pathConnectedSpace_frontier_and_homologyEulerChar`,
  `two_mul_eulerChar_eq_sum_edgesAt`, and the leaf `section33_faceEulerChar_handlePiece`
  (statement and skeleton `variable` block byte-identical, checked by script; the section adds
  only a `local notation "E3"` used by helper lemmas).
- Success line (2026-09-22T15:57:04-07:00):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\HandlePieceEulerChar.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditBatch2Leaf2.lean`, `-Audit`, 15:57:55):
  `Verified ...\AuditBatch2Leaf2.lean with no diagnostics; shared outputs unchanged.` — all
  declarations of the module within `propext`, `Classical.choice`, `Quot.sound`; the thirteen
  environment linters pass.
- Route (the reviewer's "global Euler identity plus capping bounds", made unconditional):
  (1) degree-one Hurewicz factorization: every homomorphism `π₁(Y, y) → V` into a vector space
  factors through `H₁(Y; k)` (loop values `r_a · p · r_b⁻¹`; a singular 2-simplex's edge loop is
  null-homotopic because the standard simplex is simply connected); with `fieldHurewiczOne_span_range`
  this makes a `π₁`-bijection `S → Y` induce a surjection `H₁(Y) → H₁(S)`, so `b₁(S) ≤ b₁(Y)`.
  This does NOT use the sorried `HurewiczLowDegrees.lean`.
  (2) `N' - K' ≅ Fr N × [0,1)` (barycentric rays, closed-map argument as for the tube product,
  now on the half-open interval; `h` transports `N - K`), hence `b₁(N' - K') = b₁(Fr N)` and
  `H₁` finite dimensional; `Fr N` is the boundary complex of the derived neighborhood, connected
  because `#(other boundary components) ≤ b₂(N) = b₂(K) = 0` (`card_otherBoundaryComponent_le_bettiNumber_two`,
  orientability from a containing simplex), orientable, `χ = 2 χ(K)`; `K` is connected because
  `K' = h(p(h⁻¹ X))` for the connected `X` and the barycentric retraction `p`.
  (3) `χ(Bd X) = 2 - b₁(Bd X) ≥ 2 - b₁(N' - K') = 2 χ(K)` by `hiso`.
  (4) The pieces `(AK v).space = Cpp v ∩ Bd X` cover `Bd X`, pairwise meet in `∅` or a trace
  polygon, and have no triple points (`handleEdge`, `handleNonEdge`, `pseudoCellDisjoint`), so
  `χ(Bd X) = Σ χ(AK v)` (topological Euler characteristic, union formula on polyhedra).
  (5) Capping: lift `AK v` to `E3 × (I → ℝ)`, cone each of its `deg v` boundary polygons towards
  its own new basis direction (disjoint disks), glue (`exists_isCombinatorialManifold_space_union`),
  `faceEulerChar_le_two` gives `χ(AK v) + deg v ≤ 2`.  (6) `2 χ(K) = Σ (2 - deg v)` (handshake),
  so every inequality is an equality.
- Hypothesis producers: `hd` (Moise323 via `exists_section33HandleFrame`), `h2`, `h34`, `h56`
  (the Lemma 2-7 leaves), `hiso` (Lemma 10 leaf). No hypothesis of the leaf is unused; `hiso`
  enters only through (1)-(3).
- Gemini G044 / FILL_LOG item 7 blocker ("no capping / global Euler bridge; `hiso` has no
  consumable Hurewicz lemma") was true of the tree and is now filled by (1) and (5).
- Compiles: 12 module checks (≈11–17 s each) + 1 audit (≈50 s).
