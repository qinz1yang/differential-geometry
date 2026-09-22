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
