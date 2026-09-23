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
  (1069 lines, SHA-256 `bf31e7cfc4cc4ccba25abebbf22c0bfbc33a1361516649b10fd7cddc10ad481b`).
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

## section33_disk_meets_graph (Lemma 8) — STUCK (not attempted in Lean; analysis only)

- File: none (no `.wip`; no Lean attempt was started).
- Verdict on truth: no counterexample. Under the frozen hypotheses `v₁ ∈ e₁` is forced
  (`∂Δ ⊆ Cpp v₁ ∩ Ec e₁` is non-empty, and `Cpp v₁ ∩ Ec e = ∅` for `v₁ ∉ e` by `handleEdge`,
  `handleNonEdge`, `pseudoCellDisjoint`), `hend` then gives a second edge at `v₁` and at the
  other end `u`, and the book's argument (p. 233) goes through.
- Missing bricks (each absent from the tree, grepped): (a) the combinatorial structure of compact
  pieces of the locally polyhedral open cell `Eint e \ {P'}` (a triangulation of a compact
  polyhedron in a topological 2-manifold is a combinatorial 2-manifold near that set; the tree
  has this only for the torus, `isCombinatorialManifold_two_of_homeomorph_sphere_prod`), needed to
  make `Δ ∪ (DJ − Int DJ₁) ∪ Δ₁` a PL 2-sphere; (b) planar Jordan in the cell chart of `Eint`
  to put the `Moise324` disk `DJ₁` inside `Int DJ` — note that `Moise324` as frozen gives no
  smallness of `DJ₁`, only of `Δ₁`; smallness follows from continuity of the chart
  `Eint ≅ open disk` at `P'`, not from the statement; (c) broken-line approximation of the arc
  `P'₁ v'₁ P'₂ ⊆ K'` avoiding `Δ` with a transverse crossing of `DJ` at a polyhedral point;
  (d) crossing parity against a PL sphere (available: `IsPLSphere.exists_isPLBall_complement_components`)
  and the return path through `Bd N'` (connected per component of `K`, from the Lemma 12 tools).
- Estimate: 2000+ lines; beyond the per-leaf budget. Compiles: 0.

## exists_isPolyhedralTubeNeighborhood (Lemma 2) — STUCK (not attempted in Lean; analysis only)

- File: none.
- Route: (A) a finite combinatorial 3-manifold `X₀` with `K' ⊆ Int X₀`, `X₀ ⊆ Int N' − ⋃ Ebd`
  (fine subdivision of a simplex + derived neighbourhood; routine); (B) for each edge a finite
  combinatorial 2-manifold with boundary `L_e ⊆ Eint e \ {P'_e}` whose relative interior contains
  `Ec e ∩ (ε-neighbourhood of Bd X₀)` — the same missing brick (a) as Lemma 8; (C)
  `exists_small_homeomorph_generalPosition_relative` (GeneralPosition.lean) moves `Bd X₀`
  transverse to `⋃ L_e` by a small PL homeomorphism supported away from `K'` and `⋃ Ebd`, and
  `HasPLCrossingAt.congr` passes from `|L_e|` to `Eint e` at relative-interior points; (D)
  triangulate the image and transport the manifold certificate. Only (B) lacks tree support.
- Compiles: 0.

## section33_not_isLoopTheoremDisk (Lemma 9) — not attempted

- Needs Lemma 8's machinery, brick (B) for general position of `Δ` against the pseudo-cells,
  and the component-count descent. Compiles: 0.

## Batch 2 summary

- CLOSED 2 (tube product, Lemma 12), STUCK 2 (Lemma 8, Lemma 2), not attempted 1 (Lemma 9).
- Side result: the two UNREVIEWED leaves of `Skeleton/DerivedNeighborhoodComplement`
  (FREE_INPUTS B1.m) are proved (general form, see the tube product section).
- Reusable bricks now in the tree: degree-one Hurewicz factorization over a field
  (`exists_linearMap_fieldHurewiczOne`, `finrank_fieldHomology_one_le_of_fundamentalGroup_map_bijective`
  — also the key step of Lemma 10's `b₁` bookkeeping), capping bound for surfaces with boundary
  (`IsCombinatorialManifoldWithBoundary.eulerChar_add_card_le_two`), topological Euler
  additivity over finite families of polyhedra, and the half-open product
  `N − K ≅ Fr N × [0,1)` for derived neighbourhoods.

# Batch 3 (brick B, Lemma 2)

Worker: Opus 5.5 fill worker on lease b, 2026-09-22 (checkout HEAD cabf8df87 at the time of
the first check; the lead's Lemma 12 commit landed during the batch, statements unchanged).

## Brick (B): vertex links of triangulations inside topological surfaces — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/LocalSurfaceLink.lean`
  (809 lines, SHA-256 `59cc80e7d59a73c02ca7751d89946a7da55b4d65c6fb43a58e0f9e77d310af65`).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink`
  (imports `ExistsCombinatorialTriangulation`, `Exhaustion`, `GeneralPosition`, `LocalManifold`).
- New public names (grepped tree-wide, all unused before): `exists_ball_chart_of_homeomorph_isOpen`,
  `image_mem_nhdsWithin_of_homeomorph`, `exists_ball_chart_of_inter_eq`,
  `image_mem_nhdsWithin_of_inter_eq`, `exists_mem_openSimplex_mem_of_mem`,
  `exists_segment_point_mem`, `subset_or_subset_of_hinge_of_inter_eq`,
  `false_of_maximal_face_of_inter_eq`, `exists_card_three_superset_of_inter_eq`,
  `exists_second_triangle_of_inter_eq`, `edgeGraph_geometricLink_connected_of_inter_eq`,
  **`isPLSphere_one_geometricLink_of_homeomorph`** (the brick), and
  **`exists_isSubdivision_neighborhood_of_forall_geometricLink`** (its consumer form).
- Statements.  `isPLSphere_one_geometricLink_of_homeomorph (K) [Finite K.faces] (hU : IsOpen U)
  (ψ : M ≃ₜ U) (hv : {v} ∈ K.faces) (hvM : ∀ᶠ y in 𝓝 v, y ∈ K.space ↔ y ∈ M) :
  IsPLSphere 1 (geometricLink K {v}).space` for `U ⊆ ℝ²` open and `E` finite dimensional: no PL
  structure on `M`, no global hypothesis on `K` (only agreement of `|K|` with `M` near `v`).
  `exists_isSubdivision_neighborhood_of_forall_geometricLink`: a finite `K`, compact `C ⊆ |K|`,
  open `O ⊇ C`, and sphere-or-ball links at the vertices in `O` of every finite subdivision give a
  subdivision `K'` and a combinatorial `(n+1)`-manifold with boundary `L ≤ K'` with `|L| ⊆ O` and
  `|L| ∈ 𝓝[|K|] x` for `x ∈ C` (the local form of
  `IsCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood`).
- Success line (2026-09-22T16:34-07:00):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LocalSurfaceLink.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditBatch31.lean`, `-Audit`, 16:36:18):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch31.lean with no diagnostics; shared outputs unchanged.`
  — every declaration within `propext`, `Classical.choice`, `Quot.sound`; the thirteen
  environment linters pass.
- Route: the torus template with its global chart `ψ : |K| ≃ₜ S¹ × S¹` replaced by two local chart
  lemmas for `M ≃ₜ U` (ball charts, and invariance of domain for images of open planar sets),
  transported to `|K|` on an open `W ∋ v` with `W ∩ |K| = W ∩ M`.  Every invariance-of-domain step
  is taken at a point of `W`: the hinge at `(1 - t) a + t b` for small `t` on an edge through `v`,
  maximal faces at a point of their open simplex near `v`, the second triangle at a point of the
  edge near `v`, connectedness at `v`.  The consumer runs the `Exhaustion` construction with
  `IsLocallyCombinatorialManifoldWithBoundary.derivedNeighborhood` instead of the global one.
- Hypotheses: none beyond the statement; `hU` is genuinely used (ball charts need an open target).
- Compiles: 5 module checks (≈40 s each) + 1 audit.

## exists_isPolyhedralTubeNeighborhood (Lemma 2) — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/PolyhedralTubeNeighborhoodExists.lean`
  (299 lines, SHA-256 `42ec56ee8d63d7b09d4981759e1aa6fb64e19fc757a644fe0f45c976e8ffa3f4`).
- Import line to register (after `LocalSurfaceLink`):
  `import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists`
  (imports `ExistsIsPLBallSupersetOfExteriorCompression`, `FreeFaceArc`, `LocalSurfaceLink`,
  `PLHomeomorphTopology`, `PolyhedralTubeNeighborhood`, `SeparatingSurface`; no `Skeleton/`).
- New public names (grepped tree-wide, all unused before):
  `exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff`, `IsPseudoCell.isClosed`,
  `IsTube.isCompact`, `IsTube.interior_eq_image_interior`, `IsTube.image_space_subset_interior`,
  `IsTube.isCompact_image_space`, `IsTube.disjoint_image_rim_interior`,
  `IsHandleDecompositionOfTube.disjoint_rim_interior`, and the leaf
  `exists_isPolyhedralTubeNeighborhood` (statement and the skeleton's `section Leaves` variable
  block byte-identical, checked by script; the skeleton leaf has no `open Classical in`).
- Success line (2026-09-22T16:42:00-07:00):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PolyhedralTubeNeighborhoodExists.lean with no diagnostics; shared outputs unchanged.`
- Axiom audit (`claude-moise-agent-b/AuditBatch32.lean`, `-Audit`, 16:43:09):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch32.lean with no diagnostics; shared outputs unchanged.`
  — every declaration within `propext`, `Classical.choice`, `Quot.sound`; the thirteen
  environment linters pass.
- Route (the log's (A)-(D), all real): (A) `exists_isCombinatorialManifoldWithBoundary_neighborhood`
  (SeparatingSurface) gives a finite combinatorial 3-manifold `X₀` with `K' ⊆ Int X₀`,
  `X₀ ⊆ Int N'`, and `Int N' = h(Int N)` (invariance of domain, `FreeFaceArc`) puts `K'` in
  `Int N'` and the rims `h(Dbd e) ⊆ h(Fr N)` (from `splitProper`) outside it; its frontier is a
  closed combinatorial surface `B` (`exists_isCombinatorialManifold_space_eq_frontier`).
  (B) `δ` with `cthickening δ (Fr X₀) ⊆ Int N' − K'`; `C_e = E_e ∩ cthickening δ (Fr X₀)` is a
  compact subset of `Int E_e − {P_e}`; the new general lemma
  `exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff` (finitely many disjoint open
  2-cells, each locally polyhedral off a point, compact sets there) builds polyhedral
  neighbourhoods `Q_e`, triangulates `⋃ Q_e`, applies brick (B) at every vertex near `⋃ C_e` and
  the local derived-neighbourhood lemma, and returns one combinatorial surface with boundary `L`
  with `|L| = Int E_e` near every point of `C_e`.  (C) `exists_small_homeomorph_generalPosition B L`
  with support `Int N' − K'` and displacement `< δ` gives a PL homeomorphism `f` of `ℝ³` and the
  crossing of `f(B)` with `|L|` at every common point.  (D) `X = f(X₀)` is triangulated
  (`IsPolyhedron.image_of_isPiecewiseAffineOn`), the manifold certificate transfers by
  `IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn`; `f` fixes `K'` and maps
  `Int N' − K'` into itself, so `K' ⊆ Int X` and `X ⊆ Int N'`; every point of `E_e ∩ Fr X =
  E_e ∩ f(Fr X₀)` is within `δ` of `Fr X₀`, hence in `C_e`, where `HasPLCrossingAt.congr` replaces
  `|L|` by `Int E_e`.  The union of the `L_e` is avoided by building one `L` for all edges.
- Hypotheses used: only `hd`, fields `tube` (`facesFinite`, `isNeighborhood`, `unionEq`,
  `dualBall`, `splitProper`, `isEmbedding` through `IsTube.injOn`/`continuousOn`, `imageEq`),
  `pseudoCell` (`carrierEq`, `closureEq`, `isOpenCell`, `regular`), `rimEq`,
  `pseudoCellDisjoint`.  Producer of `hd`: `Moise323` via `exists_section33HandleFrame`.
- Compiles: 2 module checks (≈45 s each; the first failed only on one long line) + 1 audit.

## section33_disk_meets_graph (Lemma 8) — STUCK (analysis only; lead decision needed)

- File: none (no Lean attempt; the analysis below found a hypothesis gap in the route first).
- Verdict on truth: no counterexample; the statement is true (the separation argument below
  closes once `ℝ³ − N'` has no bounded component, which holds for an embedded handlebody by
  Alexander duality).  The book's proof (p. 233, read from the PDF) is a separation argument:
  with `Δ ∩ K' = ∅`, a broken line `B` from `x₂ ∈ E₂` (a second pseudo-cell at `v₁`, from `hend`)
  follows the arm `P'₁ v'₁ P'₂ ⊆ K'` and crosses `D₁` once at a flat point `x₁`; Theorem 32.4
  (`Moise324`) replaces a small disk of `E₁` around `P'₁` by a PL disk missing `B`, giving a PL
  sphere `S = Δ ∪ D'₁`; the two ends of the crossing are in different components of `ℝ³ − S`, but
  are joined "close to `E₁`, then close to `C''_{v₁} ∩ Bd N'`, then close to `E₂`".
- The gap.  `IsHandleDecompositionOfTube` does not record `Ec e ∩ frontier N' = Ebd e`
  (equivalently `Eint e ⊆ interior N'`); every field allows `Eint e₁`, hence the disk `DJ` of
  `hcenter`, to touch `frontier N'` (a pseudo-cell kissing the wall of the tube from inside
  satisfies all fields).  Then `S` may meet `Bd N'`, and the return path "close to
  `C''_{v₁} ∩ Bd N'`" is not available.  When `e₁` is a bridge of `K` (allowed by `hend`, e.g. the
  bar of a dumbbell) every path from the `v₁`-arm side to the `u`-side of `E₁` avoiding `S` must
  pass through `Bd N'` or through `ℝ³ − N'`; the second needs "every component of `ℝ³ − h(N)` is
  unbounded", i.e. Alexander duality for a topologically embedded handlebody (`h` is only an
  embedding of `N`, so `Bd N'` may be wild and has no collar outside `N'`); the tree has Jordan–
  Brouwer only for smooth spheres (`SphereSeparation/`).
- Decision for the lead (one of): (i) add a field `∀ e ∈ K.faces, e.card = 2 → Ec e ∩ frontier N'
  = Ebd e` to `IsHandleDecompositionOfTube` (in the book the pseudo-cells lie in the `W` of 32.1/32.2,
  whose clause `W ∩ frontier (h '' C u ∪ h '' C v) = h '' Dbd` gives it, since
  `frontier N' ∩ (C'_u ∪ C'_v) ⊆ frontier (C'_u ∪ C'_v)`; so `Moise323`'s conclusion would carry it);
  or (ii) make "no bounded component of `ℝ³ − N'`" a named input of the leaf.
- Remaining bricks under (i), in order (brick B and Lemma 2 of this batch are now available):
  (a) PL replacement: `Moise324` for `E₁` with `δ < dist(P'₁, B ∪ Δ ∪ E₂)`; the annulus
  `DJ − Int DJ₁ ⊆ Eint₁ − {P'₁}` is a polyhedron (triangulate a polyhedral neighbourhood with
  `exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff`, curves as subcomplexes);
  PL-sphere recognition of `Δ ∪ (DJ − Int DJ₁) ∪ Δ₁`.
  (b) Jordan in the cell chart `Eint₁ ≃ₜ ball`: `DJ = J ∪ inside J ⊆ Eint₁` (the outside plus the
  rim is not an open 2-cell: an open disk minus a circle is disconnected), and `DJ₁ ⊆ Int DJ` for
  small `δ` (Moise324 as frozen bounds `Δ₁`, not `DJ₁`).
  (c) The broken line: the component `Q` of `ball(P'₁, ρ) − E₁` containing the `v₁`-arm germ has
  a frontier point in `E₁ − {P'₁}` (else `Q` is clopen in the punctured ball); take `x₁` in an open
  triangle there; `B = [y₁, z₁] ∪ (polygon in Q) ∪ (arm to P'₂)`.
  (d) Crossing parity at a flat point of a PL sphere (`IsPLSphere.exists_isPLBall_complement_components`
  plus the half-space model at an open triangle).
  (e) Return path: `E₂ ∋ P'₂` to a rim point, along `h(Fr C_{v₁} ∩ Fr N)` (a PL sphere minus disjoint
  open disks, connected; misses `S` under (i)) to a rim point `q₁` of `E₁`, a small ball around
  `q₁` to the `u`-side, and a push-off of a path in `E₁ − ball(P'₁, δ)` to the `u`-side (local
  flatness of the locally polyhedral `E₁ − {P'₁}`, brick B plus
  `exists_isPLHomeomorphOn_linearize_codimension_one`) back to `y₁`.
  Estimate: 2500–3500 lines.  Lemma 9 consumes Lemma 8 only through its universal hypothesis
  `h8`, so it is independent of this decision.
- Compiles: 0.

## Batch 3 summary

- CLOSED 2: brick (B) `isPLSphere_one_geometricLink_of_homeomorph` with its consumer
  `exists_isSubdivision_neighborhood_of_forall_geometricLink` (module `LocalSurfaceLink`), and
  Lemma 2 `exists_isPolyhedralTubeNeighborhood` (module `PolyhedralTubeNeighborhoodExists`, which
  also provides `exists_isCombinatorialManifoldWithBoundary_two_eventually_mem_iff`: one
  combinatorial surface with boundary agreeing with finitely many disjoint open 2-cells, locally
  polyhedral off a point, near prescribed compact sets).  STUCK 1: Lemma 8 (hypothesis gap above).
- Register, in this order: `LocalSurfaceLink`, `PolyhedralTubeNeighborhoodExists`.

# Batch 4 (Lemmas 3-7)

Worker: Opus 5.5 fill worker on lease b, 2026-09-22 (checkout HEAD f04911c47 at the start, with
the `rimFrontier` field; later lead commits up to 888521413 did not touch the statements used).

## exists_hasSinglePolygonTraces (Lemmas 3-4) — CLOSED

- Files (register in this order; each imports the previous ones it needs):
  1. `PolyhedralTubeTraces.lean` (689 lines, SHA-256
     `978fe9926a054080a5a8eda3745bd993cfff686f55d3da586e6e85db358b5cd6`);
  2. `NestedJordanCurves.lean` (338 lines,
     `2fee85307638cfc261811c3c86252f336b05fb124b423a2d728e95eca61b290e`);
  3. `PolyhedralTubeOuterTrace.lean` (423 lines,
     `60a3be272615de49a5386de567368cec97e1e9296febb27db0319f42b58eb9e2`);
  4. `DerivedNeighborhoodSurgery.lean` (473 lines,
     `be08a57b4bd1586c7b7587c15b8bc5e3b6981545d883f7bb7d0bc12ea91d2358`);
  5. `PolyhedralTubeSinglePolygonTraces.lean` (446 lines,
     `6f83103d868d7d186a1461342129d21afb9a5e339ee0f4b52822aaed96a09c26`), the leaf, statement and
     `section Leaves` variable block byte-identical to the skeleton.
  All under `DifferentialGeometry/Topology/PiecewiseLinear/`.
- Import lines: `import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces`,
  `...NestedJordanCurves`, `...PolyhedralTubeOuterTrace`, `...DerivedNeighborhoodSurgery`,
  `...PolyhedralTubeSinglePolygonTraces` (same prefix).
- New public names (all grepped tree-wide, unused before): `HasPLCrossingAt.exists_coordinateChart`,
  `false_of_ballChart_of_halfPlane`, `false_of_frontier_halfPlane`, `side_of_frontier_plane`,
  `HasPLCrossingAt.exists_sideChart`, `IsPolyhedralTubeNeighborhood.trace_subset`,
  `IsPolyhedralTubeNeighborhood.exists_sideChart`,
  `IsPolyhedralTubeNeighborhood.exists_traceCircles`;
  `subset_inside_or_subset_outside`, `closure_inside_eq_union`, `compl_closure_inside`,
  `closure_inside_subset_inside_of_subset_inside`, `disjoint_closure_inside_of_not_subset_inside`,
  `isPreconnected_compl_union_iUnion_closure_inside`, `closure_inside_subset_ball`,
  `exists_innermost_jordanCurve_of_sides`; `IsOpenTopologicalCell.exists_planarChart`,
  `isJordanCurve_image_of_isPLSphere_one`, `IsPolyhedralTubeNeighborhood.exists_outerTrace`;
  `exists_face_meets_of_mem_derivedNeighborhood_space`, `subset_of_isPreconnected_of_eq_inter`,
  `derivedNeighborhood_space_inter_subset_of_eq_inter`, `restrict_space_eq_of_eq_inter`,
  `exists_isSubdivision_restrict_space_diam_lt`, `derivedNeighborhood_space_subset_cthickening`,
  `IsCombinatorialManifoldWithBoundary.complement_derivedNeighborhood`,
  `IsCombinatorialManifoldWithBoundary.exists_remove_of_eq_inter`,
  `IsCombinatorialManifoldWithBoundary.exists_add_of_eq_inter`,
  `IsCombinatorialManifoldWithBoundary.exists_add_remove_of_eq_inter`;
  `frontier_sdiff_eq_of_sdiff_eq`,
  `IsHandleDecompositionOfTube.interior_pseudoCell_subset_interior`,
  `IsPolyhedralTubeNeighborhood.exists_singlePolygonTrace_edge`, `exists_hasSinglePolygonTraces`.
  Note for dedupe: `exists_face_meets_of_mem_derivedNeighborhood_space` overlaps
  `exists_convexHull_subset_face_of_mem_derivedNeighborhood` in another lane's untracked
  `CutOutPieceOfClosureSubset.lean` (not importable; different name, no clash).
- Success lines (2026-09-22, each module checked alone after a fresh prepare; `...` stands for
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\PolyhedralTubeTraces.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\NestedJordanCurves.lean with no diagnostics; shared outputs unchanged.` (13 s)
  `Verified ...\PolyhedralTubeOuterTrace.lean with no diagnostics; shared outputs unchanged.`
  (16 s)
  `Verified ...\DerivedNeighborhoodSurgery.lean with no diagnostics; shared outputs unchanged.`
  (14 s)
  `Verified ...\PolyhedralTubeSinglePolygonTraces.lean with no diagnostics; shared outputs
  unchanged.` (35 s)
- Axiom audit of all five modules (`claude-moise-agent-b/AuditBatch41.lean`, `-Audit`, 55 s):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch41.lean with no diagnostics; shared outputs unchanged.`
  — every declaration within `propext`, `Classical.choice`, `Quot.sound`; thirteen linters pass.
- Hypotheses: only `hd` and `h2` of the leaf; fields used: `tube`, `pseudoCell`, `rimFrontier`
  (for `Int E_e ⊆ Int N'` and closedness of the rims), `meetsGraph`, `pseudoCellDisjoint`.
  No producer is added; `hd` is consumed.
- Route (not the book's innermost-disk/annulus induction, which needs PL annulus prisms):
  (A) traces are finitely many disjoint PL circles and at each trace point `X` is one closed side
  of `Fr X` in a PL chart where `E_e` is a transverse plane (side charts);
  (B) in a planar chart of `E_e`, a curve `J` with `P'` inside and minimal inside is found by
  Theorem 30.2 applied to the maximal closed Jordan disks: near `J`, `E_e ∩ X` is the closed disk
  `F = Din ∪ J` (Schoenflies);
  (C) with `R = Din - Int X`, `R' = (E ∩ X) - F` (compact, relatively clopen in `G - Int X`,
  `G ∩ X` for a polyhedral `G ⊆ E - {P'}`), add a derived neighbourhood of `R` in the closed
  complement of `X` inside a large manifold ball and remove one of `R'` from `X`, via
  `IsCombinatorialManifoldWithBoundary.complement` and `.derivedNeighborhood`, with fine mesh so
  that everything happens inside an open `U` missing `J`, `P'`, the rims, `K'`, the other
  pseudo-cells and `Fr N'`;
  (D) induction over the finite set of edges; traces on other pseudo-cells are unchanged.
- Compiles: 15 module checks (first-run failures were API names: `domRestrict`,
  `sdiff_sdiff`, the `IsCombinatorialManifoldWithBoundary.derivedNeighborhood` namespace clash,
  universe-0 `subset_closure_interior_space`) + 1 audit.

## exists_hasConnectedHandlePieces (Lemmas 5-6) — CLOSED

- Files (register in this order, after the five Lemma 3-4 modules):
  1. `TubeFrontierConnected.lean` (179 lines, SHA-256
     `d3077e535853e489935a7b1c2c16b376d243600b1556d690dc15979baf80b5d9`);
  2. `PolyhedralTubeConnected.lean` (334 lines,
     `e778056983e2d540ce80608a6e7894ce5f0b7703b90c948474a5fe7c816310b6`);
  3. `HandlePieceChart.lean` (424 lines,
     `3cf7aad036e2071241f322bdf1579058c2d82cc0e5cac9b66713aacb3077ede8`);
  4. `PolyhedralTubeHandlePieces.lean` (571 lines,
     `279fab8393cee1632868bdb39a4e2d53484e9ef66ff8bfb0961d3fbbb7507ad3`), the leaf, statement and
     `section Leaves` variable block byte-identical to the skeleton.
- Import lines: `import DifferentialGeometry.Topology.PiecewiseLinear.TubeFrontierConnected`,
  `...PolyhedralTubeConnected`, `...HandlePieceChart`, `...PolyhedralTubeHandlePieces`.
- New public names (grepped, unused before): `isConnected_compl_interior_of_isConnected_frontier`,
  `IsTube.isConnected_frontier`, `IsTube.frontier_eq_image_frontier`,
  `IsHandleDecompositionOfTube.isConnected_compl_interior`;
  `IsOpenTopologicalCell.isPreconnected_sdiff`, `IsPolyhedralTubeNeighborhood.exists_isConnected`;
  `IsHandleDecompositionOfTube.subset_interior_handlePiece`,
  `IsHandleDecompositionOfTube.subset_handlePiece_of_isPreconnected`,
  `IsHandleDecompositionOfTube.pseudoCell_subset_handlePiece`,
  `IsHandleDecompositionOfTube.handlePiece_inter_eq_pseudoCell`,
  `IsHandleDecompositionOfTube.handlePiece_inter_pseudoCell_eq_empty`,
  `IsPolyhedralTubeNeighborhood.isPLBall_geometricLink_handlePiece`;
  `geometricLink_restrict_eq_of_forall_convexHull_subset`,
  `IsPolyhedralTubeNeighborhood.exists_handlePieceSurface`, `exists_hasConnectedHandlePieces`.
- Success lines (2026-09-22, each after a fresh prepare; `...` as above):
  `Verified ...\TubeFrontierConnected.lean with no diagnostics; shared outputs unchanged.` (13 s)
  `Verified ...\PolyhedralTubeConnected.lean with no diagnostics; shared outputs unchanged.`
  (15 s)
  `Verified ...\HandlePieceChart.lean with no diagnostics; shared outputs unchanged.` (15 s)
  `Verified ...\PolyhedralTubeHandlePieces.lean with no diagnostics; shared outputs unchanged.`
  (16 s)
- Axiom audit of the four modules (`claude-moise-agent-b/AuditBatch42.lean`, `-Audit`, 57 s):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch42.lean with no diagnostics; shared outputs unchanged.`
  — standard axioms only; thirteen linters pass (a first audit caught an unused `[T2Space X]`,
  removed, then all four modules re-checked).
- Hypotheses: `hd`, `hconn`, `h2`, `h34` of the leaf.  Fields used: `tube` (`freeFaceConnected`,
  `splitProper`, `splitCell`, `dualBall`, `unionEq`, `isEmbedding`, `hasEdge`), `pseudoCell`,
  `rimFrontier`, `meetsGraph`, `pseudoCellDisjoint`, `oneVertex`, `coversTube`,
  `componentClosure`, `handleEdge`, `handleNonEdge`.  `hd` is consumed, not constructed.
- Route.  (i) `Fr N` is connected: it is the union of the closures of the free faces, adjacent
  ones meeting in the rims `Dbd e`, along the connected edge graph; so `Fr N' = h(Fr N)` and
  `ℝ³ - Int N'` are connected (this is the book's tacit "`Bd N'` lies in the unbounded component").
  (ii) Lemma 5: by 30.2 (`exists_separating_component`) a component `B` of `Bd X` separates `K'`
  from `ℝ³ - Int N'`; `X'` is the solid bounded by `B`
  (`IsCombinatorialManifold.exists_isCombinatorialManifoldWithBoundary_boundaryComplex`);
  `E ∩ X' = E ∩ X` and `E ∩ Bd X' = E ∩ Bd X` since `E - (E ∩ X)` is connected (planar
  Schoenflies + Theorem 30.2 in the chart of `Int E`), so the single-polygon clause is unchanged.
  (iii) Lemma 6: a PL chart argument shows that at a trace point `C''_v ∩ Bd X` is a half-plane
  (the two half-balls of the side chart lie in the two handle pieces of the edge), giving arc
  links; off the traces the links are those of `Bd X`; the boundary is identified by the same
  links after subdividing.  Connectedness is the book's argument with `F = A'_v ∪ ⋃ (E ∩ X)`
  (no need for the component `X_v`): `F` separates `v'` from `ℝ³ - Int N'`, and a splitting of
  `A'_v` would give, by Janiszewski (`exists_separates_of_finite_iUnion`), a separating part
  missed by the arm of the graph, the cell `Cl E` and `ℝ³ - Int N'`.
- Compiles: 13 module checks + 2 audits.

## exists_hasNoHandleLoopTheoremDisk (Lemma 7) — BLOCKED (vocabulary; analysis only)

- File: none.  The conclusion `HasNoHandleLoopTheoremDisk K h N' Cpp XK'.space` and its
  `IsLoopTheoremDisk` are defined only in `Skeleton/Section33Approximation.lean` (section
  `Vocabulary`, lines 194-209); a real module cannot import the skeleton, and redefining the two
  names in a real module would clash with the skeleton's copies.  Lead decision: hoist the two
  definitions (verbatim) into a real module, e.g. `PolyhedralTubeNeighborhood.lean` beside
  `HasSinglePolygonTraces`/`HasConnectedHandlePieces`.  Lemma 9 is blocked by the same two names.
- Verdict on truth: no counterexample found; the book's route (p. 232) is sound once the step
  below is supplied.
- Route (for whoever takes it after the hoist): choose `XK` among those satisfying Lemmas 2-6
  with `bettiOne (frontier XK.space)` minimal (`Nat.find`).  Given an LTD `Δ ⊆ C''_v`,
  compress `Bd X` along `Δ` inside `U = Int N' - (K' ∪ ⋃ Ec e)`
  (`IsCombinatorialManifold.exists_compression_neighborhood_of_spanning_disk`,
  `IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_spanning_disk`), take the
  solid bounded by the separating component (as in Lemma 5,
  `exists_isCombinatorialManifoldWithBoundary_boundaryComplex`), keep the traces (Lemma 5's
  "`E - (E ∩ X)` connected" argument, `PolyhedralTubeConnected`), and re-choose the handle pieces
  (`exists_hasConnectedHandlePieces`, this batch); `b₁` drops, contradiction.
- Missing step (the real work): an LTD `Δ ⊆ C''_v` may meet the pseudo-cells `E_e` (only
  `Δ ⊆ Int N' - K'` and `Δ ∩ Bd X = Bd Δ` are required), so before compressing `Δ` must be pushed
  off `⋃ Ec e` keeping `Bd Δ ⊆ Bd X` and essentiality: a PL bicollar of `E_e - {P'_e}` in `C''_v`
  compatible with `Bd X` near the trace polygons (local flatness of the locally polyhedral
  `E_e - {P'_e}`, brick B + `exists_isPLHomeomorphOn_linearize_codimension_one`) and a
  cut-and-paste along `Δ ∩ E_e` (innermost curves in `Δ`, `NestedJordanCurves`).  Estimate
  1000-2000 lines for the push-off, 800-1200 for the minimisation/compression assembly.  A global
  shortcut ("take `Bd X` incompressible") fails: annulus surgeries can raise `b₁`.
- Compiles: 0.  Moving to Lemma 8 per the lead's plan.

## section33_disk_meets_graph (Lemma 8) — CLOSED

- Files (register in this order, after the Batch 3-4 modules they import:
  `PolyhedralTubeNeighborhoodExists`, `PolyhedralTubeOuterTrace`, `NestedJordanCurves`,
  `TubeFrontierConnected`, `HandlePieceChart`):
  1. `PseudoCellLocalSides.lean` (76 lines,
     `c4f967bc0238dff5fba5ad800d1da740acb9837827389389945eea0b7c0c39d6`);
  2. `PseudoCellSubdisk.lean` (423 lines,
     `2c30e77e32fb1f0eaa19b417238921e173f9a5d9d52f5d82fbf3e4537789cf27`);
  3. `CellGluingSphere.lean` (643 lines,
     `4c6798b25a8d6ae6ca48fa8185040e55f12de30e67f956103cc0916bb207e936`);
  4. `SurfaceSideChaining.lean` (179 lines,
     `24dcb687b49effd11254e199e262515dc34f308402ea8d6fa399d1673dd963e2`);
  5. `DiskMeetsGraph.lean` (1282 lines,
     `57f9cc620c6d3fa6b706b81c6876ca1d7c31b7368fa43713e9007e8ba3d9f716`), the leaf; statement and
     `section Leaves` variable block byte-identical to the skeleton (checked by script).
- Import lines: `import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellLocalSides`,
  `...PseudoCellSubdisk`, `...CellGluingSphere`, `...SurfaceSideChaining`, `...DiskMeetsGraph`.
- New public names (grepped tree-wide, unused before):
  `IsPseudoCell.exists_connected_neighborhood_pair_sdiff`;
  `IsTopologicalCellWithInterior.not_isPreconnected_sdiff`, `IsPseudoCell.subset_and_image_eq_inside`;
  `homeomorphClosedBall_mem_iff`, `exists_homeomorph_closedBall_eq_on_sphere`,
  `IsTopologicalCellWithInterior.isTopologicalSphere_union`,
  `IsTopologicalCellWithInterior.sdiff_union_of_subcell`,
  `IsPLHomeomorphOn.isTopologicalCellWithInterior`, `IsTopologicalSphere.isCombinatorialManifold`,
  `IsTopologicalSphere.isConnected`;
  `IsCombinatorialManifold.false_of_sdiff_subset_connectedComponentIn`,
  `IsPreconnected.subset_closure_of_forall_sides`, `isPreconnected_ball_sdiff_closedBall`,
  `exists_mem_closure_connectedComponentIn_ball_sdiff_closedBall`;
  `IsTopologicalCellWithInterior.subset`, `IsTopologicalCellWithInterior.isCompact`,
  `IsPseudoCell.isPreconnected`, `IsTube.rim_subset_frontier_inter_frontier`,
  `IsTube.isConnected_frontier_inter_frontier`, `exists_edge_ne_of_ncard_neighborSet_ne_one`,
  `IsHandleDecompositionOfTube.exists_arm`, `IsPseudoCell.exists_replacementDisk`,
  `IsPseudoCell.isPolyhedron_sdiff_of_subdisk`, `exists_isCombinatorialManifold_sdiff_union`,
  `false_of_sides_joined`, `section33_disk_meets_graph`.
- Success lines (2026-09-22, final pass, each after a fresh prepare; `...` =
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\PseudoCellLocalSides.lean with no diagnostics; shared outputs unchanged.` (21 s)
  `Verified ...\PseudoCellSubdisk.lean with no diagnostics; shared outputs unchanged.` (40 s)
  `Verified ...\CellGluingSphere.lean with no diagnostics; shared outputs unchanged.` (40 s)
  `Verified ...\SurfaceSideChaining.lean with no diagnostics; shared outputs unchanged.` (16 s)
  `Verified ...\DiskMeetsGraph.lean with no diagnostics; shared outputs unchanged.` (20 s)
- Axiom audit of the five modules (`claude-moise-agent-b/AuditBatch43.lean`, `-Audit`, 79 s):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch43.lean with no diagnostics; shared outputs unchanged.`
  — `propext`, `Classical.choice`, `Quot.sound` only; thirteen linters pass.
- Hypotheses: all binders of the leaf are used.  `h324` supplies the replacement disk; `hd`
  through `tube`, `pseudoCell`, `rimEq`, `rimFrontier` (so `Int E₁ ⊆ Int N'`, the sphere misses
  `Bd N'` and the rim `Bd E₁` lies in `h (Fr C_{v₁} ∩ Fr N) ⊆ Bd N'`), `meetsGraph`,
  `pseudoCellDisjoint`, `coversTube`, `componentClosure`, `handleEdge`, `handleNonEdge`; `hend`
  gives a second edge `e₂` at `v₁`; `hmiss` is used only for `e₂`.  `hd` is consumed, not
  constructed.  With `Moise324` and the owner's `rimFrontier` the leaf is unconditional.
- Route.  Suppose `Δ ∩ K' = ∅`.  (i) In a planar chart of `Int E₁` the given disk `DJ` is the
  closed inside of `Bd Δ`: the chart image of `Int DJ ∩ Int E₁` is open (invariance of domain)
  and closed in `ball - Ψ(Bd Δ)`; if it contained the outer part, `Int DJ` would contain the rim
  and either the inner part would be open-closed in `Int DJ`, or `Int DJ` minus the rim would be
  connected, impossible for a circle in an open disk (`PseudoCellSubdisk`).  (ii) An arm of `K'`
  from a point `a` near `P'₁` through `v'₁` to `P'₂` misses `Δ`; `Moise324` at a radius below the
  arm, `E₂` and a chart square gives `Δ'`, `D'`, and `S = Δ ∪ (DJ - Int D') ∪ Δ'` is a topological
  two-sphere (radial extension of the circle reparametrisation, two hemispheres) and a polyhedron
  (`DJ - Int D'` = closure of a component of `Q - (Bd Δ ∪ Bd Δ')` for a polyhedral neighbourhood
  `Q`, plus the curves), so every triangulation is a closed combinatorial surface (brick B on a
  punctured sphere via `stereographic'`).  (iii) The shell component `Q` of the arm point is
  adherent to `x₁ ∈ E₁` where `S = E₁`; the local sides of `E₁` at `x₁` lie in `V_{v₁}` and `V_u`;
  the first reaches `Γ`, `E₂` and `h (Fr C_{v₁} ∩ Fr N)`; the `V_u` sides chain along `Int E₁`
  outside the square to the rim (`IsPreconnected.subset_closure_of_forall_sides`), missing `S`
  because `V_u ∩ Δ = ∅` and `Δ'` is inside the square's radius.  Both sides at `x₁` in one
  component contradicts `exists_connectedComponentIn_pair_compl`.  The proof was split into the
  lemmas above after a first single-declaration version hit the heartbeat limit.
- Compiles: 21 module checks (16 while developing, 5 in the final pass) + 1 audit.

## section33_not_isLoopTheoremDisk (Lemma 9) — BLOCKED (same vocabulary as Lemma 7)

- Its hypothesis `h7 : HasNoHandleLoopTheoremDisk ...` and conclusion `¬ IsLoopTheoremDisk ...`
  use the two skeleton-only definitions (see the Lemma 7 entry); no byte-identical real module is
  possible until they are hoisted.  `h8` (the universal form of Lemma 8) is now a theorem:
  `fun v₁ hv₁ e₁ he₁ hc Δ r hr hΔ hbd hcenter hmiss => section33_disk_meets_graph h324 hd hend ...`.
- Route after the hoist (book p. 234): put an LTD in general position with the pseudo-cells,
  remove innermost polygons `J ⊆ E ∩ Δ` (by `h8` the disk `E_J` misses the centre, so a splitting
  removes `J`), then arcs by pushing across `B ∪ B₁`, until the LTD lies in one `C''_v`,
  contradicting `h7`.  Missing brick: general position of a PL disk against the pseudo-cells
  (locally polyhedral only off the centre) and cut-and-paste preserving non-contractibility of the
  boundary in `Bd X`.  Estimate 1500-2500 lines.  Compiles: 0.

## Batch 4 summary

- CLOSED 3: Lemmas 3-4 (`exists_hasSinglePolygonTraces`), Lemmas 5-6
  (`exists_hasConnectedHandlePieces`), Lemma 8 (`section33_disk_meets_graph`, unconditional given
  `Moise324` and `rimFrontier`).  BLOCKED 2: Lemma 7 and Lemma 9, both on the skeleton-only
  `IsLoopTheoremDisk`/`HasNoHandleLoopTheoremDisk` (lead decision: hoist them verbatim into a real
  module), each with a remaining mathematical brick recorded above.
- Register, in this order (14 new modules): `PolyhedralTubeTraces`, `NestedJordanCurves`,
  `PolyhedralTubeOuterTrace`, `DerivedNeighborhoodSurgery`, `PolyhedralTubeSinglePolygonTraces`,
  `TubeFrontierConnected`, `PolyhedralTubeConnected`, `HandlePieceChart`,
  `PolyhedralTubeHandlePieces`, `PseudoCellLocalSides`, `PseudoCellSubdisk`, `CellGluingSphere`,
  `SurfaceSideChaining`, `DiskMeetsGraph`.

# Batch 5 (Lemmas 7 and 9)

## exists_hasNoHandleLoopTheoremDisk (Lemma 7) — CLOSED

- Statement and `section Leaves` variable block byte-identical with the frozen leaf (checked by
  script); no hypothesis dropped.  Module `NoHandleLoopTheoremDisk` (239 lines, 61e24294), over
  four new bricks: `ChartPush` (330, b9f1d717), `PseudoCellFlatChart` (389, 205a2ec8),
  `TubeSurfaceTransfer` (257, 9cb60f27), `HandlePiecePushOff` (377, 97cfe27d).
- Route.  `Nat.find` on `b₁(Bd X)` over the tube neighbourhoods with single polygon traces and
  connected handle pieces.  Given an LTD `Δ ⊆ C''_v`:
  (i) push-off (`HandlePiecePushOff`): at every point of `Δ ∩ E_e` a chart where `E_e` is a
  coordinate plane (side chart of `X` on the trace, `IsPseudoCell.exists_flatChart` off `Bd X`);
  `C''_v` is a closed half-ball there (`exists_side_of_chart`: the two open half-balls are
  connected in `N' - ⋃ E`, one in each end's component); a cut-off vertical push
  (`exists_isPLHomeomorphOn_push_of_chart`) preserves `X`; finitely many compose
  (`exists_isPLHomeomorphOn_push_of_forall`); the pushed disk is again an LTD (the push is a
  homeomorphism of `ℝ³` fixing `X`, hence `Bd X`; nullhomotopies transported by composition);
  (ii) compression (`exists_bettiOne_lt_of_isLoopTheoremDisk`): triangulate `Bd X`, compress
  along `Δ` inside `Int N' - (K' ∪ ⋃ E)` with `exists_compression_neighborhood_of_spanning_disk`
  and `exists_separating_component_bettiOne_lt_of_spanning_disk`; the component agrees with
  `Bd X` off the compression ball, hence near the pseudo-cells (local connectedness of `Bd X`);
  `exists_of_separating_surface` (Lemma 5's construction for a given separating surface) gives
  the new `X'` with single traces; Lemma 6 gives its handle pieces; `b₁` dropped, contradiction.
  `IsConnected K.space` comes from `IsTube.isConnected_space_of_isConnected` and `IsConnected X`.
- Verification: `NoHandleLoopTheoremDisk` and each brick "Verified ... with no diagnostics";
  audit `AuditBatch51.lean` (5 modules, axioms ⊆ {propext, Classical.choice, Quot.sound}, the 13
  linters) "Verified ... with no diagnostics".  Compiles: about 28 module checks + 1 audit.
- Register after `DiskMeetsGraph`, in order: `ChartPush`, `PseudoCellFlatChart`,
  `TubeSurfaceTransfer`, `HandlePiecePushOff`, `NoHandleLoopTheoremDisk`.

## section33_not_isLoopTheoremDisk (Lemma 9) — STUCK (general position at the boundary)

- Proved brick, module `LoopTheoremDiskMeetsPseudoCells` (84 lines, 1baa46f4): a nonempty
  preconnected `Z ⊆ Int N'` missing `⋃ E_e` lies in one `C''_v`
  (`IsHandleDecompositionOfTube.exists_subset_handlePiece`), so under `h7` every LTD meets a
  pseudo-cell (`HasNoHandleLoopTheoremDisk.inter_pseudoCells_nonempty`).  Register after
  `NoHandleLoopTheoremDisk`.  Audit `AuditBatch52.lean`.
- Exact remaining goal (with `hd h2 h34 h7 h8` in context):
  `∀ Δ, IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ → ∃ Δ',
   IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Disjoint Δ' (⋃ e ∈ {e | e ∈
   K.faces ∧ e.card = 2}, Ec e)`; the brick then closes the leaf.
- Route checked for the descent once `Δ` is in general position (`Δ ∩ ⋃ E` finitely many
  components, each a PL circle in `Int Δ` or an arc meeting `Bd Δ` in its ends, crossing at every
  point).  Polygons: an innermost one in `Δ` bounds `Δ₀ ⊆ C''_{v₁}` (brick above); `h8` then says
  its disk in `E₁` misses `P'`; an innermost polygon `J` of `Δ ∩ E₁` inside that disk bounds
  `D_J` with `D_J ∩ Δ = J`; `(Δ - Int Δ_J) ∪ D_J` touches `E₁` from one side only, and the push of
  `HandlePiecePushOff` (with `C := C''_v` of that side, support in a small neighbourhood of `D_J`)
  removes `J` without new intersections.  Arcs: an outermost arc `B` cuts `D_B` from `E ∩ X` or
  from the annulus `E - Int X`; the two halves `Δᵢ ∪ D_B`, pushed the same way, are disks with
  boundaries `αᵢ ∪ B₁`; if both were nullhomotopic in `Bd X` so would `α₁ ∪ α₂` be (glue the two
  disk extensions over a theta-curve model, `JordanDiskPasting`).  End: the brick above.
- Obstruction (why STUCK): putting an LTD in general position without moving `Bd Δ` off `Bd X`.
  The tree's relative move (`exists_small_homeomorph_generalPosition_relative`,
  `..._off_polyhedron_with_lipschitz_displacement`) needs the fixed faces of `Bd Δ` face-wise
  transverse to a triangulation of `E`; `E` may fold along the trace `J = E ∩ Bd X` (only
  `HasPLCrossingAt` holds there), so no triangulation makes a crossing of `Bd Δ` with `J`
  face-wise transverse.  The half-space version (`HalfSpaceGeneralPosition`) needs a flat `Bd X`.
  Side-chart moves fix each point of `Bd Δ ∩ J` in chart coordinates only, and the interior move
  in `ℝ³` then cannot be made relative to them.  Easy sub-case: if `Bd Δ ∩ ⋃ J = ∅`, fix a collar
  of `Bd Δ` missing `⋃ E` and move the rest by less than its distance to `Bd X`; then only
  polygons occur.  Unblock by either (a) an X-compatible bicollar of a compact part of each
  `E_e - {P'}` (one generic collar level then does all of general position at once, the shift
  preserving `X`), or (b) a relative general position move whose fixed part is only required to
  cross (`HasPLCrossingAt`) rather than be face-wise transverse.  Estimate with (a) or (b)
  available: 2500-3500 further lines; without: add 1500-2500 for (a).  Compiles: 2 + 1 audit.

## Batch 5 summary

- CLOSED 1: Lemma 7 (`exists_hasNoHandleLoopTheoremDisk`), statement byte-identical, no
  hypothesis dropped.  STUCK 1: Lemma 9, reduced to the goal above; obstruction and unblocking
  options recorded.
- Register, in order (6 new modules): `ChartPush`, `PseudoCellFlatChart`, `TubeSurfaceTransfer`,
  `HandlePiecePushOff`, `NoHandleLoopTheoremDisk`, `LoopTheoremDiskMeetsPseudoCells`.

# Batch 6 (Lemma 9)

## Route decision for the general position step (logged before building)

- (b) as specified is not provable with the tree's relative general position: every relative
  mover (`exists_small_homeomorph_generalPosition_relative`, `..._transverse_relative`,
  `..._curveCrossing_relative`) needs the fixed faces face-wise transverse to the faces of `L`,
  and at a point of `Bd Δ ∩ J` the boundary edge of `Δ` and the trace `J` are both segments in
  `Bd X`, so `vectorSpan ⊔ vectorSpan` has rank 2 < 3 whatever triangulations are chosen.  The
  exemption-free variant (`..._off_polyhedron_in_halfSpace`) needs a flat `Bd X`.  Chart moves
  (side charts) certify transversality only in chart coordinates, and the junction with an ambient
  move is again a face-wise condition.  A "crossing only" hypothesis would need a new general
  position theory, not a variant of the existing proof.
- (a) needs an `X`-compatible bicollar of a compact annulus of `E - {P'}` (collar lines through
  `J` inside `Bd X`), i.e. collars of a face of a manifold with corners; the tree has bicollars
  of closed two-sided surfaces only.
- (c), adopted: use the disk's own prism.  `IsCombinatorialManifold.exists_centered_prism_
  neighborhood_of_spanning_disk` (tree) applied to the component `S` of `Bd X` containing `Bd Δ`
  gives `f : σ × [-1,1] → N` with `f(x,0) = r x` and wall `S ∩ N = f(∂σ × [-1,1])`.  Every level
  `Δ_s = f(σ × {s})` is again a loop theorem disk (the wall lies in `Bd X`, the boundary curves
  are homotopic along the wall), and for `s` off the finitely many vertex heights of a
  triangulation of `f⁻¹(⋃ E ∩ N)` the level `Δ_s ∩ ⋃ E` is a compact PL 1-manifold whose
  boundary is `Bd Δ_s ∩ ⋃ E`.  No bicollar of `E` and no side chart is needed; the wall edges are
  handled in prism coordinates, where the wall is a union of flat faces.

## Brick GP (general position of a loop theorem disk) — CLOSED

- `IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_levelSet` (module
  `LoopTheoremDiskLevelSet`): every loop theorem disk can be replaced by one, `Δ'`, with
  `Δ' ∩ ⋃ E = ⋃₀ Cs`, `Cs` finite and pairwise disjoint, each member a PL circle missing `Bd X`
  or a PL arc `q(σ¹)` with `q(∂σ¹) = S ∩ Bd X`.  Route (c): a generic level of the disk's own
  prism.  Local disks of `f⁻¹ E` in prism coordinates come from flat charts off the wall
  (invariance of domain puts the point in `Int N`) and from half-square side disks on the wall
  (the prism lies on one side of `Bd X`); a finite cover, one triangulation with the disks as
  subcomplexes, and a level off the vertex heights give a graph with degrees 1 on the wall and 2
  off it.
- Modules, in order (lines, sha256 prefix): `LevelSetOneManifold` (245, 2bc1c15e),
  `LevelSetComponents` (157, 0d29a746), `LoopTheoremDiskPrism` (239, e26634e8),
  `PseudoCellLocalDisks` (463, 3e735184), `LoopTheoremDiskLevelSet` (523, 3f3039e2); each
  verified with no diagnostics.
- Next: the descent (circles, then arcs) consuming exactly this output.

## Brick circle step (removing a circle of intersection) — CLOSED

- `IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_circleStep` (module
  `LoopTheoremDiskCircleStep`): a loop theorem disk meeting `⋃ E` in circles and arcs as in the
  GP brick, with at least one circle, is replaced by one meeting `⋃ E` in a proper subfamily.
  Innermost circle in `Δ` (planar model) + `h8` give a circle whose disk in `E` misses the
  centre; the minimal such circle in the chart bounds a PL disk `D ⊆ E` with `D ∩ Δ = c`
  (`PseudoCellCircleDisk`, via `PseudoCellChartDisks` and the new general
  `PolyhedralDiskRecognition`: a polyhedral topological 2-cell with PL boundary circle is a PL
  disk, proved by capping with a cone in `E × ℝ`); swap by `exists_isPLHomeomorphOn_replace_ball`,
  side from an outer collar of `c`, push off by `LoopTheoremDiskPushOff`.
- Modules (all verified, no diagnostics): `PolyhedralDiskRecognition`, `LoopTheoremDiskPushOff`,
  `PseudoCellChartDisks`, `PseudoCellCircleDisk`, `LoopTheoremDiskCircleStep`.
- Next: the arc step (outermost arc in the chart, via inversion when `Δ` lies outside `X`), then
  the induction and the leaf.

## Brick arc step (removing an arc of intersection) — CLOSED

- `IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_arcStep` (module
  `LoopTheoremDiskArcStep`): a loop theorem disk meeting `⋃ E` only in arcs `q(σ¹)` with ends on
  `Bd X`, at least one, is replaced by one meeting `⋃ E` in a proper subfamily.
- `Δ - Bd X` is connected, so it lies on one side of `Bd X`.  Chart of `Int E_e - P'`: `Ψ` with
  hole `{a}` if `Δ` is inside `X`, `invert a ∘ Ψ` with hole `insert a (invert a '' (B(0,1))ᶜ)`
  if outside (`Schoenflies.inversion_sides`).  Outermost crosscut (`PlanarOutermostCrosscut`)
  gives `B`, a sub-arc `B₁` of the trace and a PL disk `D ⊆ E_e`, `∂D = B ∪ B₁`,
  `D ∩ Bd X = B₁`, `D ∩ Δ = B` (`PseudoCellArcDisk`, `PseudoCellArcDiskSides`).
- Theta curve (`LoopTheoremDiskTheta`, `nullhomotopic_of_crosscut_halves`): `B` splits the
  planar model of `Δ` into `U`, `V`; if both `α₁ ∪ B₁` and `α₂ ∪ B₁` were null-homotopic in
  `Bd X`, extensions over `U` and `V` glue and `∂Δ` would be null-homotopic.  Replace `V` by `D`
  (`exists_isPLHomeomorphOn_union` + boundary-simplex extension), then push `D` off `A` inside
  the handle piece containing `U` near `B` (`LoopTheoremDiskArcSide`,
  `exists_handlePiece_near`; `LoopTheoremDiskPushOff`).
- Modules (all verified, no diagnostics): `PlanarOutermostCrosscut`, `PseudoCellArcDisk`,
  `PseudoCellArcDiskSides`, `LoopTheoremDiskTheta`, `LoopTheoremDiskArcSide`,
  `LoopTheoremDiskArcStep`.  Deduplication after the uniqueness grep: the local
  `stdSimplexBoundary_one_eq` was replaced by the tree's `stdSimplexBoundary_one_eq_pair`
  (`GeneralPosition`), the local `mem_inside_or_mem_outside` by
  `Schoenflies.inside_union_outside`; both modules re-verified.

## section33_not_isLoopTheoremDisk (Lemma 9) — CLOSED

- Module `NotLoopTheoremDisk`.  Statement and `section Leaves` variable block byte-identical to
  `Skeleton/Section33Approximation.lean` (checked by script); no hypothesis dropped (`hd`, `h2`,
  `h34`, `h7`, `h8` all used; `h7` only at the end).
- Proof: GP brick gives `Δ₁` and the family `Cs`; strong induction on `Cs.ncard`
  (`IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_disjoint_of_decomposition`: circle
  step while a circle remains, else arc step) gives a loop theorem disk missing `⋃ E`, which
  contradicts `HasNoHandleLoopTheoremDisk.inter_pseudoCells_nonempty` (Lemma 7).
- Verification: all 17 modules `Verified ... with no diagnostics; shared outputs unchanged`
  (last re-checks after the dedup: `LoopTheoremDiskArcSide`, `PseudoCellArcDiskSides`,
  `LoopTheoremDiskArcStep`, `NotLoopTheoremDisk`).  Audit `AuditBatch61.lean` (all 17 modules:
  axioms within `propext`, `Classical.choice`, `Quot.sound`; the 13 linters): `Verified ... with
  no diagnostics`.  No `sorry`/`admit`/`native_decide`/`axiom`/`nolint`/`set_option`, no
  declaration docstrings or `--` comments, no line over 100 characters, public names unique
  tree-wide, no `Skeleton/` import; all external imports are tracked and clean.

## Batch 6 summary

- CLOSED: Lemma 9 (`section33_not_isLoopTheoremDisk`), statement byte-identical.  Route (c)
  (the disk's own prism) replaced (b)/(a) for general position; reasons in the route decision
  above.  New general bricks usable elsewhere: `PolyhedralDiskRecognition` (polyhedral
  topological 2-cell with PL boundary circle is a PL disk), `PlanarOutermostCrosscut`,
  `LoopTheoremDiskTheta`, `LevelSetOneManifold`/`LevelSetComponents` (generic levels of a
  triangulated prism are PL 1-manifolds, split into circles and arcs).
- Register, in order (17 new modules, after `LoopTheoremDiskMeetsPseudoCells`):
  `LevelSetOneManifold`, `LevelSetComponents`, `LoopTheoremDiskPrism`, `PseudoCellLocalDisks`,
  `LoopTheoremDiskLevelSet`, `PolyhedralDiskRecognition`, `LoopTheoremDiskPushOff`,
  `PseudoCellChartDisks`, `PseudoCellCircleDisk`, `LoopTheoremDiskCircleStep`,
  `PlanarOutermostCrosscut`, `PseudoCellArcDisk`, `PseudoCellArcDiskSides`,
  `LoopTheoremDiskTheta`, `LoopTheoremDiskArcSide`, `LoopTheoremDiskArcStep`,
  `NotLoopTheoremDisk` (4660 lines).

# Batch 7 (Section 33 endgame: Lemmas 13, extension, 10)

Worker: Opus 5.5 fill worker on lease b, 2026-09-23 (checkout HEAD 35a89dbb5 while writing this
entry; statements read from `Skeleton/Section33Approximation.lean`, section `Leaves`).

## exists_section33BoundaryMatch (Lemma 13) — CLOSED

- Files (all under `DifferentialGeometry/Topology/PiecewiseLinear/`; register in this order):
  1. `HoledSphereExtension.lean` (388 lines,
     `ea8f04d298cd020434ec22eedd4ec777fdfdebd0644b13d015d3fc690d7914d7`);
  2. `HoledSphereStrip.lean` (554,
     `df20b9de0074b43b26c4a008d72bfe681dd59b4de787544ae2b828ce586485d1`);
  3. `SurfaceCapSphere.lean` (229,
     `f1fb65aaf47b615fe1b88f4aafaf82f9e5ff2e0d630f20b66b8f85ee154f6978`);
  4. `SquareConcat.lean` (146,
     `3c65987b591671bb8fd6ea4e2153171a2774c12f5664ce26c9b0727ff19db0ee`);
  5. `TubeFreeFaceStrips.lean` (397,
     `ac4224d423d94fb3c4fb621509fbe67d7f2291ffd0146de772a4cefdd4244a3a`);
  6. `BoundaryMatchMobius.lean` (442,
     `97ea624295ba5f40284596875bdb57b0dfca02ecbee0d3dc6a51a317fc150305`);
  7. `Section33BoundaryMatch.lean` (611,
     `6e67de4f0107da69cf129050aa19227508059ad68d83b669ba9a940b82a19587`), the leaf.
- Import lines: `import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension`,
  `...HoledSphereStrip`, `...SurfaceCapSphere`, `...SquareConcat`, `...TubeFreeFaceStrips`,
  `...BoundaryMatchMobius`, `...Section33BoundaryMatch` (same prefix; no `Skeleton/` import).
- Statement identity: the theorem text from `theorem exists_section33BoundaryMatch` to `:= by`
  and the `section Leaves` variable block are byte-identical with the skeleton (checked by script).
  All six hypotheses are used (`hconn` for the edge graph and for the orientability of `Bd N`).
- Success lines (2026-09-23, each after a fresh prepare; `...` =
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\HoledSphereExtension.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\HoledSphereStrip.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SurfaceCapSphere.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SquareConcat.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\TubeFreeFaceStrips.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\BoundaryMatchMobius.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33BoundaryMatch.lean with no diagnostics; shared outputs unchanged.`
- Audit (`claude-moise-agent-b/AuditBatch71.lean`, `-Audit`, all seven modules, axioms within
  `propext`, `Classical.choice`, `Quot.sound`, the thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch71.lean with no diagnostics; shared outputs unchanged.`
- Route.  Model: `A_v = Fr C_v ∩ Fr N` is the PL two-sphere `Fr C_v` minus the open splitting disks
  of the edges at `v` (`IsTube.freeFace_eq_sdiff`).  Target: `A'_v` capped at its `deg v` trace
  circles in `ℝ³ × (edges → ℝ)` is a closed surface of Euler characteristic 2, hence a PL
  two-sphere (`exists_isPLSphere_cap`, from the batch-2 capping).  Holed spheres with the same
  index set: `exists_isPLHomeomorphOn_holed` transfers `exists_isPLHomeomorphOn_holed_disk_with_
  boundary_extension` through planar charts (sphere minus one disk).  Vertices are added along the
  connected edge graph (processed set kept path-connected); the new vertex's prescribed rim maps
  must be orientation compatible with the reference: otherwise a chain of strips of free faces along
  a path (planar strip model `[-1/2,1/2] × [-2,-1]` carried by the holed-disk classification,
  `exists_freeFace_chain`) closes to a cylindrical diagram in `Bd N`, which orientability of `Bd N`
  forces to be untwisted, and whose image in `Bd X` is twisted by the reflection
  (`false_of_reversed_rim`, via `IsCylindricalDiagram.endMap_endpoints_of_isOrientable`, the book's
  Möbius band of page 238).  Both orientabilities come from `isOrientable_euclidean_three`.
- New public names (grepped tree-wide, unique): `IsPLCirclePositive.of_eqOn`,
  `IsPLCirclePositive.conj`, `IsPLSphere.exists_holed_chart`, `image_sdiff_iUnion_sdiff_eq`,
  `IsPLSphere.exists_isPLHomeomorphOn_holed`; `isHPolytope_rectTwo`, `isPLBall_rectTwo`,
  `mem_frontier_rectTwo_of_apply_one_eq`, `exists_planar_strip`, `IsPLSphere.exists_holed_strip`;
  `IsCombinatorialManifoldWithBoundary.exists_isPLSphere_cap`; `isPLHomeomorphOn_squareLowerHalf`,
  `isPLHomeomorphOn_squareUpperHalf`, `exists_isPLHomeomorphOn_square_concat`;
  `IsTube.rim_subset_splitDisk`, `IsTube.disjoint_rim_rim`, `IsTube.freeFace_eq_sdiff`,
  `IsTube.frontier_eq_iUnion_freeFace`, `IsTube.exists_rim_of_mem_freeFace_inter`,
  `IsTube.rim_subset_freeFace`, `IsTube.disjoint_rim_freeFace`, `IsTube.exists_freeFace_strip`,
  `IsTube.exists_freeFace_chain`; `mem_or_mem_of_card_eq_two`,
  `IsHandleDecompositionOfTube.exists_trace_of_mem_inter`,
  `IsHandleDecompositionOfTube.pseudoCell_subset_piece`,
  `IsHandleDecompositionOfTube.isPLHomeomorphOn_iUnion_freeFace`,
  `IsTube.exists_isOrientable_frontier`,
  `exists_isOrientable_frontier_of_isCombinatorialManifoldWithBoundary`, `image_prod_singleton_eq`,
  `image_one_sub_eq`, `IsHandleDecompositionOfTube.false_of_reversed_rim`;
  `isPLHomeomorphOn_fst_inl`, `IsHandleDecompositionOfTube.exists_piece_map`,
  `IsHandleDecompositionOfTube.exists_boundaryMatch_step`, `exists_section33BoundaryMatch`.
- Compiles: about 25 module checks + 1 audit.

## exists_section33Extension (page-238 endgame) — CLOSED

- Files (new, `DifferentialGeometry/Topology/PiecewiseLinear/`; lines, SHA-256):
  `PseudoCellDiskReplacement.lean` 75
  `6f041b1e6928198859409d9007b1aa0e34f5afcd365073f634b352264c016d09`;
  `Section33ExtensionRegions.lean` 185
  `102e3dcfaeab3adb9faa6d9bac3e7e14cd6bdcb07a6ffecc1c378910b53b7d4f`;
  `Section33ExtensionSides.lean` 176
  `2dce38ae1bc01b03cf82a3e90fc7a28493a03f4efc212fde23cd8e5e23bc5312`;
  `Section33ExtensionBalls.lean` 399
  `fb17e176dafc4faaf22d5dd1fc0ac19d8d3056fc2082749ef73e4364492a8861`;
  `Section33ExtensionLabels.lean` 589
  `afb534b2799e192585937defccb5b15ca5d7b6006c6a5eaa53b001d66d4a932a`;
  `Section33ExtensionSphereMaps.lean` 324
  `e2f13b2eddc5fca270b932ccdbcb29d99a694fb9e4a89747e0fa53880cbf4974`;
  `Section33Extension.lean` 350
  `d2d97ccd317174601c2ccee5ed9dbefab6aee10dcc55cb7fb8892c19207b08ac`.
- Aggregate import lines (not added; the aggregate is the lead's):
  `import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskReplacement`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionRegions`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionSides`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionBalls`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionLabels`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionSphereMaps`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33Extension`
- Statement identity: `exists_section33Extension` in `Section33Extension.lean`, inside
  `section Leaves` with the skeleton's `variable` block, is byte-identical to the frozen leaf of
  `Skeleton/Section33Approximation.lean` (statement text and variable block compared by script:
  both identical).  All hypotheses are used (`h324` for the disks `F_e`, `h56` for the connected
  boundary and the polyhedral pieces `C''_v ∩ Bd X`, `hsmall` for the diameters).
- Success lines (2026-09-23, each after a fresh prepare; `...` as above):
  `Verified ...\PseudoCellDiskReplacement.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33ExtensionRegions.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33ExtensionSides.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33ExtensionBalls.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33ExtensionLabels.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33ExtensionSphereMaps.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33Extension.lean with no diagnostics; shared outputs unchanged.`
- Audit (`claude-moise-agent-b/AuditBatch72.lean`, `-Audit`, all seven modules, axioms within
  `propext`, `Classical.choice`, `Quot.sound`, the thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch72.lean with no diagnostics; shared outputs unchanged.`
- Route.  One radius `δ₀` (`exists_small_radius`): balls `B(P'_e, 2δ₀) ⊆ Int X`, centres `3δ₀`
  apart, `B(P'_e, δ₀)` off the other pseudo-cells and the vertices, `3δ₀` inside the diameter
  slack of every `C''_v`.  `F_e = (E_e ∩ X − Int D₁) ∪ Δ₁` from `Moise324` via
  `IsPseudoCell.exists_replacementDisk`, recognised as a PL disk with rim `J_e` and agreeing with
  `E_e ∩ X` off `B(P'_e, δ₀)` (`exists_plDisk_agreeing_off_ball`).  `g` plus disk extensions
  `D_e → F_e` give `ψ : Fr C_v → S'_v` (`exists_sphere_maps`); 3D PL Schoenflies gives `B'_v`
  with `Fr B'_v = S'_v`; Alexander extension `C_v → B'_v`.  Jordan-Brouwer for `Bd X`: `Int X`,
  `ℝ³ − X` connected (`isConnected_interior_space_and_compl`), so `B'_v ⊆ X`, interiors miss
  `Bd X` and all `F_e`, are pairwise disjoint, balls meet only in `F_e`, and cover `X` (local
  sides of `S'_a` at interior points of `F_e`).  `h v ∈ Int B'_v`: good/bad labelling (ball
  interior vs handle piece) on the connected `Int X − ⋃ B̄(P'_e, δ₀)`, constant across `E_e`
  there by the pseudo-cell local sides, good near `A'_v` off the pseudo-cells by the local sides
  of `Bd X`.  Diameter: `diam B'_v = diam S'_v` and `S'_v` lies within `δ₀` of `C''_v`.
- New public names (grepped tree-wide, unique): `IsPseudoCell.exists_plDisk_agreeing_off_ball`;
  `isConnected_interior_space_and_compl`, `closure_subset_of_frontier_subset_of_isConnected_compl`,
  `IsCompact.exists_mem_frontier_dist_le_dist`, `IsCompact.exists_mem_frontier_pair_dist_le`;
  `IsPLSphere.exists_connected_neighborhood_pair_sdiff_of_two`,
  `exists_connected_neighborhood_pair_sdiff_frontier_space`,
  `isConnected_sdiff_closedBall_of_ball_subset`, `isConnected_sdiff_biUnion_closedBall`;
  `Finset.eq_of_card_eq_two_of_mem_of_mem`,
  `IsHandleDecompositionOfTube.ball_subset_and_disjoint_interior`,
  `IsHandleDecompositionOfTube.disjoint_interior_balls`,
  `IsHandleDecompositionOfTube.exists_edge_of_mem_ball_inter_ball`,
  `IsHandleDecompositionOfTube.mem_interior_iUnion_balls_of_mem_disk`,
  `IsHandleDecompositionOfTube.iUnion_balls_eq`; `eq_empty_of_isPreconnected_of_closure_cover`,
  `IsHandleDecompositionOfTube.mem_handlePiece_of_mem_interior_ball`,
  `IsHandleDecompositionOfTube.mem_interior_ball_of_vertex`;
  `IsHandleDecompositionOfTube.vertex_image_notMem_pseudoCell`,
  `IsHandleDecompositionOfTube.exists_freeFace_image_notMem_pseudoCell`,
  `IsHandleDecompositionOfTube.exists_sphere_maps`, `IsTube.exists_isPLHomeomorphOn_glue`;
  `IsHandleDecompositionOfTube.exists_small_radius`, `IsHandleDecompositionOfTube.exists_plDisks`,
  `exists_section33Extension`.  (All in namespace `DifferentialGeometry.Topology.PiecewiseLinear`;
  `Finset.eq_of_card_eq_two_of_mem_of_mem` and `IsCompact.*` are namespaced there too.)
- Compiles: 14 module checks + 1 audit.

## section33_fundamentalGroup_map_bijective (Lemma 10) — CLOSED in a strengthened form (lead decision)

- Files (new, `DifferentialGeometry/Topology/PiecewiseLinear/`; lines, SHA-256):
  `Section33TubeRayChart.lean` 217
  `37039b40fc104b50cc726c352a529aa4be9e3c1e535e995c80660cc6081bb0a5`;
  `Section33CollarPush.lean` 137
  `db0b460e18cd6afada145959811e294441d0a8f5b1cc3d5a58d31963831c1ef4`;
  `Section33LoopTheoremInjective.lean` 58
  `8811a1c91ec322a4113c4757fbc222f430395d625569979e706d80e08763ecf2`;
  `SquareCrossingChain.lean` 468
  `824ee3819a07458ce5925479a3f3f8ee41ae4c5197074c4c253743f0698c9bf6`;
  `SquareHomotopyToSurface.lean` 264
  `5b2679c2adfb1f758ec3e7a5dd443f6a70633d7de108f5d9339cf05626145c9e`;
  `SurfaceLoopDecomposition.lean` 225
  `8b274cf177f4f36c5974a52ae6ed43d79ab817e207e619123eb4592a62fc957f`;
  `SurfaceSideLoops.lean` 119
  `fddbc59e31cd0962ec670f733f9c5acaa53c5a954dfb964ff38286b596839e7f`;
  `Section33FundamentalGroupBijective.lean` 274
  `5428f1cf52ffe063156161171fca84a0ab9d2454f04d0d77ae06c5d6c0e1b11f`.
- Aggregate import lines (not added; the aggregate is the lead's):
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeRayChart`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33CollarPush`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33LoopTheoremInjective`
  `import DifferentialGeometry.Topology.PiecewiseLinear.SquareCrossingChain`
  `import DifferentialGeometry.Topology.PiecewiseLinear.SquareHomotopyToSurface`
  `import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceLoopDecomposition`
  `import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSideLoops`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33FundamentalGroupBijective`
- Statement.  `section33_fundamentalGroup_map_bijective_of_isTube (h264 : Moise264)
  (ht : IsTube K N C D Dbd h N') (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
  (hXc : IsConnected (frontier XK.space)) (hnoLTD : ...)` with the frozen conclusion verbatim
  (`∀ hsub, ∀ x, Function.Bijective (FundamentalGroup.map ⟨Set.inclusion hsub, _⟩ x)`), same
  `hnoLTD` text.  NOT byte-identical: the frozen leaf's `h34`, `h7`, `hprod` are not needed, and
  `hd`, `h56` enter only through `hd.tube` and `h56.2.1`.  Probe
  `claude-moise-agent-b/ProbeLeaf10.lean` (frozen `variable` block and frozen statement copied by
  script, proof `exact section33_fundamentalGroup_map_bijective_of_isTube h264 hd.tube h2 h56.2.1
  hnoLTD`) elaborates with no error and exactly three diagnostics: ``Variable name `h34` is not
  explicitly referenced`` (25:5), same for `h7` (27:5) and `hprod` (30:5).  So the frozen leaf holds,
  but no zero-warning byte-identical restatement exists.  Lead decision: drop `h34`, `h7`, `hprod`
  from the leaf (a strengthening) or call the new theorem in the assembly:
  `have h10 := section33_fundamentalGroup_map_bijective_of_isTube h264 hd.tube h2 h56.2.1 h9`
  (the assembly's `have hprod := section33_tube_product ht` then has no consumer).
- Hypotheses and producers: `h264` is the open `Moise264` input (as in the frozen leaf); `ht` from
  `hd.tube` (`exists_section33HandleFrame`); `h2` from `exists_isPolyhedralTubeNeighborhood`;
  `hXc` from `h56.2.1` (`exists_hasConnectedHandlePieces`); `hnoLTD` from
  `section33_not_isLoopTheoremDisk` (Lemma 9).  All five are used; the module compiles clean.
- Success lines (2026-09-23; `...` =
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\Section33TubeRayChart.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33CollarPush.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33LoopTheoremInjective.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SquareCrossingChain.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SquareHomotopyToSurface.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SurfaceLoopDecomposition.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SurfaceSideLoops.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section33FundamentalGroupBijective.lean with no diagnostics; shared outputs unchanged.`
- Audit (`claude-moise-agent-b/AuditBatch73.lean`, SHA-256
  `a8443977bf84a1fd8373ed3769685bed0b0474656dc234de3915dde59deb1e34`, `-Audit`, all eight modules,
  axioms within `propext`, `Classical.choice`, `Quot.sound`, the thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch73.lean with no diagnostics; shared outputs unchanged.`
- Route.  (1) Ray chart of the tube (`IsTube.exists_rayChart`): compact `Y`, `Φ : Y × [0,1] → N'`
  from the derived-neighbourhood rays transported by `h`, `Φ(b,1) ∈ K'`, `Φ(b,0) ∈ Bd N'`,
  injective on `Y × [0,1)`, with continuous inverse coordinates `(β, τ)` on `N' - K'`.
  (2) Collar: `max(τ, s/2)` makes `Int N' - K' → N' - K'` a homotopy equivalence
  (`IsTube.bijective_fundamentalGroup_map_interior_sdiff`; this answers AA question 5 without
  `hprod`).  (3) Injectivity `π₁(Bd X) → π₁(Int N' - K')`: `Moise264` with the boundary complex of
  `X` (`injective_fundamentalGroup_map_of_moise264`, now stated for a set `S = |L|`), `hnoLTD`
  supplying nullhomotopy of every disk boundary.  (4) Surjectivity: lowest ray level `e₀` meeting
  `X` (its level set misses `Int X`, touches `Bd X` at `P₀`), highest level `e₂` meeting the
  closure of the complement (its level set lies in `X`, touches `Bd X` at `P₂`); loops at `P₀` in
  `X` are pushed along rays to level `e₀`, loops at `P₂` in `cl(X^c)` to `e₂`; the square lemma
  (`exists_surface_path_homotopic_of_square`, via grid ε-chains in `SquareCrossingChain` and short
  convex-ball homotopies) turns the pushed square into a loop of `Bd X`; conjugation by paths of
  `Bd X` (`exists_path_homotopic_map_of_loops`, `Bd X` path connected) gives arbitrary endpoints;
  a general path is cut at its returns to `Bd X` by real induction on the supremum of good
  parameters (`exists_surface_path_homotopic_of_sides`).  (5) Composition of the three maps.
- New public names (grepped tree-wide, unique; namespace `DifferentialGeometry.Topology.
  PiecewiseLinear`): `exists_continuousOn_rayCoordinates`, `IsTube.exists_rayChart`,
  `IsTube.bijective_fundamentalGroup_map_interior_sdiff`,
  `injective_fundamentalGroup_map_of_moise264`, `exists_dist_lt_chain_of_isPreconnected`,
  `finite_connectedComponents_of_iUnion`, `exists_nat_lt_div_le_le_succ_div`,
  `exists_chain_left_right_of_no_crossing`, `exists_pos_forall_exists_path_dist_lt`,
  `path_homotopic_of_forall_mem_convex`, `exists_surface_path_homotopic_of_square`,
  `exists_surface_path_homotopic_of_sides`, `exists_path_homotopic_map_of_loops`,
  `exists_surface_loop_homotopic_of_level`, `section33_fundamentalGroup_map_bijective_of_isTube`.
- Compiles: about 30 module checks + 1 audit + 1 probe.

## Batch 7 summary

- Lemma 13 (`exists_section33BoundaryMatch`) and the page-238 endgame (`exists_section33Extension`)
  CLOSED byte-identically; Lemma 10 CLOSED as `section33_fundamentalGroup_map_bijective_of_isTube`
  (frozen leaf minus the unused `h34`, `h7`, `hprod`; lead decision above).
- Final audit over all 22 Batch 7 modules (`claude-moise-agent-b/AuditBatch7.lean`, SHA-256
  `fa0b3c469e54388ef733340873f3e22e37a10054034c2b3e2756bd5f86870651`, axioms within `propext`,
  `Classical.choice`, `Quot.sound`, the thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch7.lean with no diagnostics; shared outputs unchanged.`

# Batch 8 (compact cut and graph frames, leaf 1)

Worker: Opus 5.5 fill worker on lease b, 2026-09-23 (checkout HEAD 712480db4 while writing this
entry).  Target: `exists_compactCutAndGraph` of `Skeleton/Section34Compact.lean`.  Not restated:
the leaf is not closed (INTERFACE below); six bricks CLOSED.

## exists_compactCutAndGraph — INTERFACE (the hypothesis `h331 : Moise331`)

- The graph frame needs `f₁` on the cut neighbourhood `N = ⋃ src (.vertexBall w)`, and the cut
  frame pins `N` to the simplices of `K` (face disks `closure (conv s \ N)`, residual balls,
  patches, arcs; clauses 18--23).  `Moise331` returns `f` only on its own
  `(derivedNeighborhood T L').space`, with `T` arbitrary (no mesh, no compatibility with `K`) and
  only the global estimate `dist (f x) (h x) < ε`.  So neither `N :=` the 33.1 neighbourhood (its
  cut by the simplices of `K` is uncontrolled) nor a nice `N` inside it with `f₁ := f` works
  (`f₁ '' N ∈ 𝓝ˢ (h '' Γ)` fails in general: `f` may translate a thin tube by `0.3 ε` and stretch
  it to radius `0.6 ε`, so the image of a thinner tube misses `h '' Γ`); a recomposition `f ∘ ψ`
  needs a displacement-controlled homeomorphism between regular neighbourhoods, which the tree
  does not have.  Clauses (5)--(8) of the graph frame moreover need `f₁ '' C_w` inside
  prescribed neighbourhoods of `h '' C_w` (book, page 240: "by (8) of Theorem 32.3 the sets C''_v
  can be chosen so as to lie in arbitrarily small neighborhoods of the sets C'_v"); an
  `ε`-estimate cannot give them, since the handle frame forces `ε > 4 diam h(C_w)` while
  `dist(C_w, conv s)` for a non-incident `s` is of the same order.  The book chooses `N` first
  (page 239) and applies 33.1 to that `N`.
- Proposed replacement (lead/owner decision): the leaf, `moise341OnNeighborhood` and
  `moise341_of_onNeighborhood` take `h331 : Moise331OnTube` instead of `h331 : Moise331`, where
  `Moise331OnTube := ∀ K N N' C D Dbd h, IsTube K N C D Dbd h N' → IsConnected K.space →
  (∀ v : K.vertices, ((edgeGraph K).neighborSet v).ncard ≠ 1) → ∀ W, (∀ v ∈ K.vertices,
  W v ∈ 𝓝ˢ (h '' C v)) → ∃ f, IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ 𝓝ˢ (h '' K.space) ∧
  ∀ v ∈ K.vertices, f '' C v ⊆ W v` (module `Section33TubeApproximation`).  Its producer
  `moise331OnTube : Moise323 → Moise324 → Moise264 → Moise331OnTube` is PROVED (the Section 33
  assembly after the tube frame, `Moise323`'s prescribed neighbourhoods taken inside the `W v`,
  and the sharpened extension below), and `Moise331OnTube.moise331 : Moise331OnTube → Moise331`
  is PROVED; the chain `32.3, 32.4, 26.4 → 33.1 on a tube → 34.1` stays one-way and no named
  input is added.  The assembly would call `moise341_of_onNeighborhood (moise331OnTube h323 h324
  h264) h305`.  I found no clause of the frozen conclusion that is false.

## Design (the leaf under `Moise331OnTube`)

- `M` = fine triangulation of a PL ball `C⁺ ⊆ V` with `C ⊆ Int C⁺` and `C` the space of a
  subcomplex; `K := restrict M C`, `K' := K`, `L := restrict K Γ` (`Γ = |K¹|`),
  `N := ⋃ graphDualCell M L v` (the second derived neighbourhood of `L` in `M`, leaving `C` at the
  boundary vertices through the collar of `M`).  Vertex balls = graph dual cells; splitting disk
  of `e` = meet of the two end cells (clause 27 by definition); face disks, residual balls,
  patches, arcs, marked points, outer faces and arcs by the frame's formulas (clauses 12--19 by
  definition); `srcBd` = the intrinsic boundaries.  `f₁` from `Moise331OnTube` with
  `W v := thickening η (h '' C v)`, `η` below the finitely many positive distances
  `dist (h '' C_u) (h '' conv s)` (`u ∉ s`) and `dist (h w) (h '' C_u)` (`w ≠ u`).  Carriers:
  boxes around `h '' S_t ∪ ⋃_{w ∈ t} W w` (fine `M` by uniform continuity of `h` on `C⁺`).

## CLOSED bricks (new files under `DifferentialGeometry/Topology/PiecewiseLinear/`)

- `Section33TubeApproximation.lean`, 417 lines,
  `07aabb84771574e407b48511d953fa826cdd5054e805af44a1edcf96ea4855d5`: `Moise331OnTube`,
  `exists_section33Extension_image_dualCell_subset` (the page-238 extension with
  `f '' C v ⊆ C''_v ∪ ⋃_{e ∋ v} ball(P'_e, δ)` for any `δ > 0`), `moise331OnTube`,
  `Moise331OnTube.moise331`.
- `Section34CompactLinkCondition.lean`, 141,
  `bee6fed69fbeffce4c94187c20a99b7d88888ee756a8e41f0d5f36d38290b201`:
  `IsCombinatorialManifoldWithBoundary.mem_connectedComponentIn_sdiff_openEdge` and
  `IsCombinatorialManifoldWithBoundary.section34CompactLinkCondition` (clause 6 from
  `IsCombinatorialManifoldWithBoundary 3 K`, `K` finite).
- `Section34CompactGraphApproximation.lean`, 261,
  `77df9fe2314ba588eb7c6e8dd329a4613b2ea6ccc1c757bfa40e351b978c7241`:
  `IsPLBall.exists_collarTriangulation`,
  `exists_subset_of_convexHull_subset_section34CompactGraphSkeleton`,
  `card_le_two_of_mem_restrict_section34CompactGraphSkeleton`,
  `convexHull_subset_section34CompactGraphSkeleton`,
  `restrict_section34CompactGraphSkeleton_space`, `isConnected_section34CompactGraphSkeleton`,
  `IsCombinatorialManifoldWithBoundary.exists_two_neighbors`,
  `ncard_neighborSet_restrict_section34CompactGraphSkeleton_ne_one`,
  `exists_compactGraphApproximation` (from `h331 : Moise331OnTube`: `M` as above, then for every
  `W` with `W v ∈ 𝓝ˢ (h '' C v)` an `f₁`, PL on `N`, with `f₁ '' N ∈ 𝓝ˢ (h '' Γ)` and
  `f₁ '' C v ⊆ W v`).
- `Section34CompactResidualCells.lean`, 274,
  `e544410405b2e35b05e5cfeb45f5aa9ad61bfb49f2d6070f37dd0811f9e9a3eb`:
  `closure_space_sdiff_derivedNeighborhood_space` (the closure of `|A| − N(L)` is the union of
  the derived cells of the simplices outside `L`), `closure_convexHull_sdiff_derivedNeighborhood_space`,
  `vertices_eq_setOf_restrict_section34CompactGraphSkeleton`,
  `mem_restrict_section34CompactGraphSkeleton_iff`,
  `closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_three` (face disk = derived cell of
  `s` in its face complex), `closure_convexHull_sdiff_iUnion_graphDualCell_of_card_eq_four`
  (residual ball = derived cells of `t` and of its four facets),
  `isPLBall_derivedNeighborhoodCell_restrict_of_card_eq_three`,
  `isPLBall_residualCell_of_card_eq_four`.
- `Section34CompactCarriers.lean`, 105,
  `5bf1023bf1c762c0817d6d5d1bb8d25d5575e7125a214b7a6fb5f85b487deb49`:
  `dist_le_two_mul_of_forall_mem_Icc`, `exists_isPLCellOn_frontier_subset_interior_of_diam_lt`,
  `exists_section34CompactCarrierControl` (`Section34CompactCarrierControl` plus `X t ⊆ Int H t`).
- `Section34CompactCellSeparation.lean`, 111,
  `b10fb18d8babeb930035a607ab60647f456fda0614efc0333c237037fa897239`:
  `closedStar_barycentricSubdivision_inter_convexHull_eq_empty`,
  `graphDualCell_space_inter_convexHull_eq_empty`, `notMem_graphDualCell_space_of_ne` (clauses
  20--23 and the separations behind graph-frame clauses 5--8).
- Import lines, in this order (aggregate not touched):
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphApproximation`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualCells`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarriers`
  `import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation`
- Success lines (each after a fresh prepare; `...` =
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\Section33TubeApproximation.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section34CompactLinkCondition.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section34CompactGraphApproximation.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section34CompactResidualCells.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section34CompactCarriers.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\Section34CompactCellSeparation.lean with no diagnostics; shared outputs unchanged.`
- Audit `claude-moise-agent-b/AuditBatch8.lean` (SHA-256
  `24a4e8b2a401236492f97b1265c4634583c35f6671d96d7aeafc2533d8fd49a9`, `-Audit`, the six modules,
  axioms within `propext`, `Classical.choice`, `Quot.sound`, the thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch8.lean with no diagnostics; shared outputs unchanged.`
- All new public names grepped tree-wide: unique.  `Moise331OnTube` is a named proposition like
  `Moise331`; its producer is `moise331OnTube`, its hypotheses are inhabited (`exists_isTube`,
  any `W`), and it implies `Moise331`, so it is not degenerate.

## STUCK (what the leaf still needs under `Moise331OnTube`)

- Cut frame: clause 7 for patches, face arcs, edge arcs, marked points, outer faces and outer
  arcs (PL cells with their intrinsic boundaries), clause 8 (boundary = union of the proper
  faces), 9 (pairwise meets), 10 (incomparability), 11 (`⋃ src = C ∪ N`), 26 (a vertex ball
  meets only the splitting disks at its vertex), 28 (face disk ⊆ residual ball; follows from the
  two derived-cell descriptions above).  Missing bricks: the flag description of `C_w ∩ conv s`
  and `D_e ∩ conv t` in the face complexes (the arcs and points as meets of derived cells), and
  the collar part of `M` near `∂C` for the outer kinds (`closure (|M| − C)` a combinatorial
  manifold in which the cells of the boundary vertices are half-balls).  Clauses 1--6, 12--25,
  27 and 29 are covered by the bricks, by definition, or by `codimension_one_cofaces` purity.
- Graph frame: clauses 1--8 and 10 follow from `exists_compactGraphApproximation`, the
  separation brick and the carriers brick (assembly not written).  Clause 9 (nested solid tori
  with `IsSpine S₁ (h '' rim s)` and a toroidal shell around the face torus, which carries the
  arms of the vertex balls along the edges leaving `s`) needs a PL product structure `D² × S¹`
  around `∂s ∪ arms` with core `∂s`, i.e. regular-neighbourhood uniqueness or annulus theory for
  a PL circle; absent from the tree.  Clause 11 (the thin exterior 5(7)) needs `ℝ³ − h(t)`
  connected for the topological cell `h(t)` (Jordan-Brouwer of `SphereSeparation/` plus
  invariance of domain; `TopologicalCellComplementConnected` of `MoiseChain` is an unproved named
  proposition).
- Compiles: 10 module checks and 1 audit.

# Batch 9 (Section 32 canonical tower)

Worker: Opus 5.5 fill worker on lease b, 2026-09-23.  Target: `exists_canonicalTower` of
`Skeleton/Section32PseudoCell.lean` (Moise §32, p. 224).  Result: CLOSED, restated byte-identically
in a real module; no skeleton imported; no existing file edited except this log.

## exists_canonicalTower — CLOSED

- Statement identity: the text from `open Classical in` / `theorem exists_canonicalTower` to
  `:= by` (788 characters) and the `section Leaves` variable block are byte-identical to the
  skeleton (checked by script); same namespace `DifferentialGeometry.Topology.PiecewiseLinear`,
  same `open Set Topology`, same `local notation "E3"`.  To wire it: import `CanonicalTowerExists`
  into `Section32PseudoCell.lean` and delete the skeleton's `exists_canonicalTower`.
- Hypotheses used: `ht hu hv huv he hP' hWint hWfr h307 hZ hZD`.  Not needed for the tower and
  bound by `let _ :=` (AGENTS `unusedArguments` pattern): `hW`, `hWsub`, `hWK`.  `hWfr` is used
  only to put `h '' Dbd {u, v}` in the frontier of `h '' C u ∪ h '' C v` (local finiteness).
- `Moise307`: needed, once per integer index, for the fitted polyhedral tori
  (`isPolyhedralSolidTorus`); it is a hypothesis of the frozen leaf, so no interface change.  It is
  NOT available unconditionally in the tree: the only producers are
  `moise307_of_moise252 (h252 : Moise252)` and `moise307_of_moise306_of_moise252`
  (`Section30Torus.lean`), and `Moise252` has only conditional producers (loop theorem lemma two).
- Route (BP answer §1, all sub-leaves proved, no new `sorry`):
  1. `exists_continuous_injective_image_closedBall_eq_stdSimplex`: gauge rescaling between the
     round unit disk and the coordinate triangle, conjugated by translations so that the centre goes
     to the barycentre (`exists_homeomorph_image_eq_of_mem_interior`, Mathlib's proof plus the point
     equation), then the chart `w ↦ (1 - w₀ - w₁, w₀, w₁)`.
  2. `IsTube.exists_unitSolidCylinder_coordinates`: `φ = h ∘ ρ ∘ (x ↦ (κ(x₀,x₂), x₁))` with `ρ` from
     `IsTube.exists_centered_prism_coordinates`; continuous and injective on `unitSolidCylinder`,
     image `h '' C u ∪ h '' C v`, middle disk ↦ `h '' D {u,v}`, rim ↦ `h '' Dbd {u,v}`, `0 ↦ P'`.
  3. `exists_isRevolvedTorusChain_tower` (model, in ℝ³): radii `rᵢ = 2ⁱ/(1+2ⁱ)`, squares
     `[rᵢ-wᵢ, rᵢ₊₁+wᵢ] × [-wᵢ, wᵢ]`, `wᵢ ≤ min(εᵢ/4, gaps/3)` with `εᵢ` a thickening of the compact
     revolved segment inside the given open set (all angles at once); every triple is an
     `IsRevolvedTorusChain` (solid tori via `isSpine_revolutionOf_of_mem_cellInterior`), squares at
     index distance ≥ 2 disjoint, segments fill the punctured open disk exactly, exact lower tail
     closure `∪ {0}`, exact upper tail closure `∪ unitMeridianCircle`, local finiteness off the
     centre and rim.
  4. Transport through `φ` (closed embedding of the compact cylinder; invariance of domain for
     `interior`), open set `interior cylinder ∩ φ⁻¹(interior W ∩ Zᶜ)`.
  5. Fitting and general position: `exists_fits_image_annulus_of_isRevolvedTorusChain` (inner shell,
     `Moise307`, cylindrical diagram bridge) and `exists_fits_family_pairGP_succ` (even seeds kept,
     odd ones relative GP), both adapted from the Codex probe `CanonicalTowerReduction`; one family
     restricted to all triples.
- New files (under `DifferentialGeometry/Topology/PiecewiseLinear/`), lines, SHA-256:
  - `CenteredDiskSimplexMap.lean`, 149,
    `9fb53b3098ac32d7f16d81e8c490f21d08cf6c6ccb80fa5e1ce0cc5757c6c7a3`
  - `RevolvedTorusTower.lean`, 741,
    `b2e3e87c83052afc3852fc612d6061b4bbac5a27084d0a66b2c9cf7f76e3cc04`
  - `SplitDiskCylinderCoordinates.lean`, 192,
    `358ebd7e737a8dba41781b4ba670e565c92a26bdd2d6a1f5a55e1e8452ec4aa6`
  - `CanonicalTowerExists.lean`, 277,
    `c90b927c2be807585cc8a8881947bcf67db0174c005f484b2e64c9d16085cc98`
- New public names (all grepped tree-wide, unique except the frozen leaf itself):
  `exists_homeomorph_image_eq_of_mem_interior`,
  `exists_continuous_injective_image_closedBall_eq_stdSimplex`, `unitSolidCylinder`,
  `unitMeridianDisk`, `unitMeridianCircle` (Set-valued defs, no structure or Prop-valued def),
  `isCompact_unitSolidCylinder`, `unitMeridianDisk_subset_unitSolidCylinder`,
  `unitMeridianCircle_subset_unitMeridianDisk`, `zero_mem_interior_unitSolidCylinder`,
  `unitMeridianDisk_sdiff_subset_interior`, `exists_isRevolvedTorusChain_tower`,
  `IsTube.exists_unitSolidCylinder_coordinates`,
  `exists_fits_image_annulus_of_isRevolvedTorusChain`, `exists_fits_family_pairGP_succ`,
  `exists_canonicalTower`.
- Import lines, in this order (aggregate not touched):
  `import DifferentialGeometry.Topology.PiecewiseLinear.CenteredDiskSimplexMap`
  `import DifferentialGeometry.Topology.PiecewiseLinear.RevolvedTorusTower`
  `import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskCylinderCoordinates`
  `import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerExists`
- Success lines (each after a fresh prepare; `...` =
  `D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear`):
  `Verified ...\CenteredDiskSimplexMap.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\RevolvedTorusTower.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\SplitDiskCylinderCoordinates.lean with no diagnostics; shared outputs unchanged.`
  `Verified ...\CanonicalTowerExists.lean with no diagnostics; shared outputs unchanged.`
- Audit `claude-moise-agent-b/AuditBatch9.lean` (SHA-256
  `5ac78ba0f94bd8270cf9761276db511e25eea5353620381d8073533104ee0ab4`; every declaration of the four
  modules, transitive axioms within `propext`, `Classical.choice`, `Quot.sound`, the thirteen
  linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b\AuditBatch9.lean with no diagnostics; shared outputs unchanged.`
- Untested on an instance only in the sense that no joint Lean fixture was built; `IsTube` is
  inhabited (`exists_isTube`), and every hypothesis of the new public theorems is satisfiable (the
  model tower takes any open set containing the punctured disk, e.g. `univ`).
- Compiles: 8 module checks and 1 audit.
