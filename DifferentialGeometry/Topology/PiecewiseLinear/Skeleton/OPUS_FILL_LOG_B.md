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
