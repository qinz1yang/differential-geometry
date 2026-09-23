# Opus fill log — lease e (`claude-agent-e-20260919`), 2026-09-22

Output root `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e`. No existing file edited; no
git write. Lead instruction received mid-task: no separate refutation phase, look for a
counterexample only when a proof hits a case the hypotheses allow.

## exists_locallyFinitePLPieceIn_of_isOpen — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/ExistsLocallyFinitePLPieceInOfIsOpen.lean`
  (711 lines).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.ExistsLocallyFinitePLPieceInOfIsOpen`
- Leaf block (`section Leaves` … statement) byte-identical to `Skeleton/Section34Control.lean`
  (checked by `diff`); same namespace, `universe u`, both `variable` lines.
- New public names (namespace `DifferentialGeometry.Topology.PiecewiseLinear`):
  `momentPoint`, `momentPoint_injective`, `affineIndependent_momentPoint`, `momentComplex`,
  `exists_eqOn_of_eqOn_succ`, `IsPiecewiseAffineWithinAt.of_subset_of_mem_nhdsWithin`,
  `simplicialMap_comp_eqOn`; in `LocallyFinitePieceTower`: `exists_injOn_nat_vertices`,
  `vertexCode`, `injOn_vertexCode`, `vertexParam`, `vertexParam_zero`, `vertexParam_succ`,
  `unpair_vertexParam_fst_le`, `injOn_vertexParam`, `vertexParam_embed`, `vertexPos`,
  `injOn_vertexPos`, `vertexPos_embed`, `limitComplex`, `mem_limitComplex_faces_of_mem`,
  `injOn_simplicialMap_vertexPos`, `affineIndependent_image_vertexPos`, `levelComplex`,
  `mem_levelComplex_faces_iff`, `mem_limitComplex_faces_iff`,
  `levelComplex_faces_subset_limitComplex`, `levelComplex_space`, `levelComplex_faces_finite`,
  `levelComplex_faces_subset_succ`, `levelComplex_mono`, `levelComplex_space_mono`,
  `mem_limitComplex_space`, `levelComplex_space_subset`, `levelPiece`, `levelPiece_complex`,
  `levelPiece_map`, `levelPiece_map_simplicialMap`, `levelPiece_map_eqOn_succ`,
  `exists_limitMap`, `limitMap`, `limitMap_eqOn`, `continuousOn_limitMap_levelComplex`,
  `injOn_limitMap_levelComplex`, `image_limitMap_levelComplex`, `limitMap_mem_coreSpace`,
  `mem_levelComplex_faces_of_mem_space`, `finite_setOf_mem_limitComplex_faces`,
  `locallyFinite_convexHull_limitComplex`, `levelComplex_space_mem_nhdsWithin`,
  `continuousOn_limitMap`, `injOn_limitMap`, `bijOn_limitMap`, `invFunOn_limitMap_eq`,
  `continuousOn_invFunOn_limitMap`, `isEmbedding_limitMap`,
  `isPiecewiseAffineOn_chart_limitMap`, `isPiecewiseAffineOn_chart_symm_limitMap`,
  `toLocallyFinitePLPieceIn`. All grepped tree-wide: no clash (`limitMap` exists only in
  other namespaces).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ExistsLocallyFinitePLPieceInOfIsOpen.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T20:52:32Z, receipt SHA256 `E94A5D9D…12B3E0`).
- Audit: `AuditLeafA1.lean` in the output root (all declarations of the module; allowed axioms
  `propext`, `Classical.choice`, `Quot.sound`; the thirteen environment linters): `Verified …
  AuditLeafA1.lean with no diagnostics; shared outputs unchanged.`
- Route: the proved tower `exists_locallyFinitePieceTower_of_isOpen` is a direct system of finite
  cores glued by `IsGlueIso`; every vertex gets a natural parameter (inherited through
  `embedInv`, fresh `Nat.pair (i+1) code` when born) and is placed on the moment curve of
  `ℝ^(2n+1)` (any `2n+2` moment points are affinely independent, faces have `≤ n+1` vertices by
  `IsCombinatorialManifoldWithBoundary.card_le`), so all cores become nested subcomplexes of one
  complex; the first coordinate bounds the parameter, and the tower's
  `core_space_mem_nhdsWithin` forces every face through a level-`i` vertex into level `i+2`
  (open-simplex argument), which gives topological local finiteness in `ℝ^7`, local
  stabilisation of `|K|` to one finite level, and hence continuity, embedding and both chart
  clauses from the finite `PLPieceIn.precomp` pieces. Reviewer's warning addressed: local
  finiteness is proved in the ambient `ℝ^7`, not only injectivity.
- Hypotheses of the endpoint and their producers: `[Nonempty M₁] [T2Space M₁]
  [SecondCountableTopology M₁] [HasGroupoid M₁ (plGroupoid 3)]`, `IsOpen U` — all consumed by
  `exists_locallyFinitePieceTower_of_isOpen (m := 2)`; the brick
  `LocallyFinitePieceTower.toLocallyFinitePLPieceIn` needs only `[T2Space X]` and
  `hcard : ∀ i, ∀ s ∈ (T.core i).faces, s.card ≤ n + 1`, produced by `card_le`.
- Compiles: 3 module compiles (~15–19 s each) + 1 audit (49 s).

## exists_isSubdivision_section34CarrierSupport_subset — CLOSED (two redundant instance binders reported)

- File: `DifferentialGeometry/Topology/PiecewiseLinear/SubdivisionSubordinateToCover.lean`
  (550 lines).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover`
- Leaf statement and both `variable` lines byte-identical to `Skeleton/Section34Control.lean`
  (checked by `diff`).
- New public names (namespace `DifferentialGeometry.Topology.PiecewiseLinear`): `depthKeep`,
  `finite_setOf_faces_inter_nonempty`, `exists_mem_nhds_finite_setOf_faces_inter_nonempty`,
  `diam_convexHull_image_centroid_le`, `depthSubdivision`, `depthSubdivision_zero`,
  `mem_depthSubdivision_succ_faces_iff`, `depthSubdivision_succ_isSubdivision`,
  `depthSubdivision_isSubdivision`, `mem_depthSubdivision_succ_of_mem_depthKeep`,
  `mem_depthKeep_of_mem_subcomplexGeneratedBy`,
  `convexHull_subset_of_mem_depthSubdivision_succ_faces`,
  `finite_setOf_depthSubdivision_faces_subset`, `mem_depthKeep_of_convexHull_subset`,
  `setOf_depthSubdivision_succ_faces_subset_eq`, `setOf_depthSubdivision_faces_subset_eq`,
  `diam_le_of_mem_depthSubdivision_faces`, `depthLimit`, `exists_depth_bound`,
  `mem_depthLimit_faces_iff_of_bound`, `depthLimit_isSubdivision`, `locallyFinite_depthLimit`,
  `diam_le_of_mem_depthLimit_faces`, `LocallyFinitePLPieceIn.subdivide`,
  `LocallyFinitePLPieceIn.exists_isSubdivision_forall_image_subset`. Grepped: no clash.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SubdivisionSubordinateToCover.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T21:11Z).
- Audit (`AuditLeafB.lean`, all module declarations): axiom closure clean for every declaration
  (only `propext`, `Classical.choice`, `Quot.sound`); the thirteen linters pass on every
  declaration except the frozen leaf, where `unusedArguments` reports exactly
  `argument 10: [SecondCountableTopology M₁]` and
  `argument 11: [HasGroupoid M₁ (plGroupoid 3)]`. These two binders are part of the frozen
  statement and are genuinely unnecessary (the subdivision needs only local finiteness and the
  cover; the combinatorial-manifold conclusion comes from
  `isCombinatorialManifold_of_locallyFinitePLPieceIn`, which needs only `[T2Space M₁]` and
  `hU`). Not removed, per the "never a changed statement" rule; the lead decides (same situation
  as the redundant `HasGroupoid` of leaf a2). `h𝒦` is used, for the face-size bound `≤ 4`
  (vertex link is a finite PL 2-sphere); a finrank bound would also do, so `h𝒦` is not essential.
- Route: iterated relative derived subdivisions `relDerived` with depths `m σ`: at stage `j` all
  simplices meeting some `σ` with `j < m σ` are starred at barycentres, the others kept; inside
  `σ` the mesh is `≤ (3/4)^(m σ) · diam σ` (barycentric step reused from
  `exists_diam_le_of_mem_barycentricSubdivision_faces` on the closure of the top simplex); local
  finiteness makes each simplex stabilise after `max m` over its finitely many neighbours, and the
  eventually-present faces form a locally finite subdivision `depthLimit`. Depths come from local
  Lebesgue numbers (`lebesgue_number_lemma_of_metric` for each compact simplex, minimised over the
  finitely many neighbours), so every simplex through a vertex of `t` lies in one ball
  `B(w₀, δ)` mapping into one `O i`. Same realisation map; `IsCombinatorialManifold` from the
  proved a2 producer.
- Hypotheses of the endpoint and their producers: `hU` → a2 producer; `𝒦` (any) — the
  `locallyFinite`, `continuousOn`, `bijOn` fields are used; `h𝒦` → face bound; `O, hO, hcover`
  → Lebesgue numbers; `[T2Space M₁]` → a2 producer; `[SecondCountableTopology M₁]`,
  `[HasGroupoid …]` unused (above).
- Compiles: 3 module compiles (~15 s each) + 2 audits.
- Receipt SHA256 `01317E7F…4D345545`.

## handlePiece_subset_of_edgeCollars — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/HandlePieceSubsetOfEdgeCollars.lean`
  (442 lines).
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceSubsetOfEdgeCollars`
- Statement (`open Classical in` + theorem) and the `section Leaves` variable lines byte-identical
  to `Skeleton/Section32PseudoCell.lean` (checked by `diff`); same `local notation "E3"`.
- New public names (namespace `DifferentialGeometry.Topology.PiecewiseLinear`):
  `mem_of_mem_closure_of_forall_subset_or_subset`,
  `exists_mem_nhds_forall_mem_iff_of_forall_subset_or_subset`,
  `exists_mem_nhds_forall_mem_of_mem`, `eq_or_eq_of_mem_of_card_eq_two`,
  `IsTube.inter_eq_of_mem_faces`, `IsTube.inter_eq_empty_of_forall_notMem_faces`. Grepped: no
  clash. (The two `IsTube` helpers are stated without pair literals: `IsTube.interEdge` uses the
  default `DecidableEq` pair while the leaf's `open Classical` context elaborates `{u, v}` with the
  classical instance.)
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\HandlePieceSubsetOfEdgeCollars.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T21:27:35Z, receipt SHA256 `73CB26B3…6C6D0D83`).
- Audit (`AuditLeafC.lean`, all module declarations, standard three axioms, thirteen linters):
  `Verified … AuditLeafC.lean with no diagnostics; shared outputs unchanged.`
- Route: for each edge `e = {v, w}` the pinned `SplitsDualCellsAlong` gives sides `A_e ∋ h v`,
  `B_e ∋ h w` of `S_e = (C'_v ∪ C'_w) \ E_e`; the "every preconnected subset lies on one side"
  clause makes both sides closed (hence open) in `S_e`; `C'_w \ W_e` (connected, contains `h w`,
  avoids `E_e ⊆ W_e`) lies in `B_e`, so `A_e ∩ C'_w ⊆ W_e`; `C'_a ∩ C'_b = h(D_{ab}) ⊆ W_{ab}` and
  collars of distinct edges are disjoint. The set `R` = points of `X = N' \ ⋃ E` in `C'_v` or an
  adjacent `C'_w`, on the `A_e` side of every `S_e` they meet, contains `h v`, lies in
  `C'_v ∪ ⋃_{e∋v} W_e`, and membership in `R` is locally constant on `X` (only the cells through a
  point occur near it); `IsPreconnected.constant` on the component with the Bool indicator, then
  closure of a closed target. No clause of the frozen statement is unused (`hE` supplies sides and
  `E_e ⊆ W_e`; `hW` closedness, disk-in-collar, vertex avoidance, connectivity, disjointness;
  `ht` injectivity, cells, finiteness, cell intersections). As the skeleton notes, `IsTube` still
  has no inhabitant in the tree, so this leaf is proved but untested on an instance.
- Compiles: 2 module compiles (~15 s) + 1 audit.

# Batch 2

Four frozen leaves of `Skeleton/Section32PseudoCell.lean`. Same lease and output root; no existing
file edited (except this log); no git write.

## exists_compact_connected_to_freeFace — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/FreeFaceArc.lean` (302 lines).
- Import line: `import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc`
- Statement and `section Leaves` variable lines byte-identical to the skeleton (checked by script).
- New public names (namespace `DifferentialGeometry.Topology.PiecewiseLinear`):
  `interior_image_eq_image_interior_of_isCompact`, `frontier_image_eq_image_frontier_of_isCompact`,
  `exists_isOpen_inter_image_eq_of_isCompact`, `stdSimplex_subset_closure_openSimplex`,
  `IsTube.injOn`, `IsTube.continuousOn`, `IsTube.finite_vertices`, `IsTube.dualCell_subset`,
  `IsTube.isClosed`, `IsTube.mem_dualCell`, `IsTube.card_eq_two_of_mem`,
  `IsTube.splitDisk_subset_frontier`, `IsTube.dualCell_inter_subset_frontier`,
  `IsTube.splitDisk_sdiff_subset_interior`, `IsTube.exists_dualCell_model`. Grepped: no clash.
  The module doubles as the shared tube-topology layer of the other Batch 2 modules.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\FreeFaceArc.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T22:05:52Z, receipt SHA256 `9F429A10…2ACA4E8A`).
- Audit (`AuditBatch2A.lean` in the output root, all declarations of this module and of the
  leaf-4 module, standard three axioms, thirteen linters): `Verified … AuditBatch2A.lean with no
  diagnostics; shared outputs unchanged.` (22:19:51Z).
- Route: invariance of domain (`interior_range_eq_image_preimage_interior`) transports interiors and
  frontiers through `h` on compact subsets of `N`; with the PL model `f` of `C v`
  (`image_stdSimplexBoundary_eq_frontier`, `image_openSimplex_stdVertices`) the map `g = h ∘ f` sends
  the open 3-simplex onto `interior (h '' C v)` and its boundary onto `frontier (h '' C v)`.
  `D e ⊆ frontier (C v)` by `IsPLBall.inter_subset_frontier_of_isPLBall` (a 2-ball meeting two
  3-balls). `Bv = g '' [q, s]` with `g q = h v` (`q` in the open simplex since `v ∈ interior (C v)`)
  and `g s = h p` for `p` in the free face (non-empty: `freeFaceConnected`); points of the segment
  other than `s` have all barycentric coordinates positive, so land in the interior, off the
  frontier; `p ∉ D e` since `D e ∩ Bd N = Dbd e`.
- Compiles: 1 module compile (~30 s) + shared audit.

## isHandleDecomposition_of_edgeCollars — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/HandleDecompositionOfEdgeCollars.lean`
  (803 lines).
- Import line:
  `import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars`
- Statement (`open Classical in` + theorem) and variable lines byte-identical to the skeleton.
- New public names: `isPreconnected_compl_iUnion_of_isPreconnected_compl`,
  `isPreconnected_union_of_subset_union_of_disjoint_closed`, `vertex_ne_centroid_of_card_eq_two`,
  `IsEdgeCollarFamily.eq_of_mem_of_mem`, `IsEdgeCollarFamily.image_vertex_notMem`,
  `IsEdgeCollarFamily.image_splitDisk_subset`, `IsEdgeCollarFamily.exists_mem_of_mem_image_inter`,
  `IsEdgeCollarFamily.disjoint_image_dualCell`,
  `IsEdgeCollarFamily.isPreconnected_image_dualCell_sdiff`. Grepped: no clash.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\HandleDecompositionOfEdgeCollars.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T22:18:47Z, receipt SHA256 `F52AE765…6538A63`).
- Audit: covered by `AuditBatch2A.lean` above (clean).
- Route: the frozen predicate is NOT changed. The unicoherence step the stopped worker asked for is
  `isPreconnected_compl_iUnion_of_isPreconnected_compl` (Theorem 30.2,
  `exists_separates_of_finite_iUnion`, in a simply connected locally path connected space), applied
  in the subspace `C w` (`IsPLBall.simplyConnectedSpace`, `.locallyPathConnectedSpace`) to the
  pulled-back collars: `Q_w = h '' C w \ ⋃_{e ∋ w} W e` is connected. Per edge the pinned sides
  are chosen once (`choose`), `sd w e` is the side of `w`. `P_w` = points of `X = N' \ ⋃ E` in
  `C'_w` or a collar at `w`, on the `w`-side of every such collar. The `P_w` are disjoint, cover `X`,
  are open in `X` (near a collar point only the two cells of that edge occur; near a core point
  only `C'_w`), and connected: `Q_w ∪ (W_e ∩ sd w e)` is connected because `sd w e` is, and the rest
  of `sd w e` lies in the other collars at `w`, closed and disjoint from `W_e`
  (`isPreconnected_union_of_subset_union_of_disjoint_closed`). Hence `P_w` is the component of
  `h w`, the handle piece is `closure P_w`; near a point of `W_e` a handle piece agrees with the side
  (`hcleq`), `E_e ⊆ closure` of both sides gives (9) and (10a ⊇), relative closedness of the sides
  gives (10a ⊆); (7) and (10b) come from clause (8) (`handlePiece_subset_of_edgeCollars`).
- Hypotheses used: `hW` (all six clauses), `hE` (sides, `Ec ⊆ W`, `Ec ⊆ frontier` of both sides),
  `ht` (cells, injectivity, finiteness, cell intersections, dual balls).
- Compiles: 2 module compiles (~40 s; the first failed only on the `push_neg` deprecation).

## exists_twoComponents_of_pseudoCell — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/TwoComponentsOfPseudoCell.lean` (810 lines).
- Import line: `import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell`
- Statement (`open Classical in` + theorem) and variable lines byte-identical to the skeleton.
- New public names: `IsOpenTopologicalCell.isConnected_sdiff_singleton`,
  `isConnected_sdiff_of_isPLBall_inter`, `image_stdSimplex_subset_closure_image_openSimplex`,
  `exists_preconnected_local_interior`, `IsTube.mem_frontier_of_mem_frontier_dualCell`,
  `IsTube.frontier_inter_frontier_subset_closure_freeFace`. Grepped: no clash.
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TwoComponentsOfPseudoCell.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T22:32:50Z, receipt SHA256 `B8D9C140…18D71364`).
- Audit (`AuditBatch2B.lean`, all module declarations, standard three axioms, thirteen linters):
  `Verified … AuditBatch2B.lean with no diagnostics; shared outputs unchanged.` (22:33:46Z).
- Route: `U_i = (Y \ E) ∩ closure Γ_i`, `Γ_1, Γ_2` the components of `h u`, `h v` in the open set
  `I \ E` (`I = interior Y`, `Y = C'_u ∪ C'_v`). Both gaps of the stopped worker are closed from
  the tube, without new hypotheses:
  (a) separation up to frontier points: a point of `Bd Y \ E` lies in one cell only, and the
  dual-cell model (`exists_preconnected_local_interior`, via
  `exists_isOpen_inter_image_eq_of_isCompact`) gives it arbitrarily small neighbourhoods `O'`
  with `O' ∩ I` inside the image of a convex subset of the open simplex, adherent to the point,
  so it is adherent to exactly one component;
  (b) rim circles: `Bd C_u` is a PL 2-sphere (`IsPLBall.isPLSphere_frontier`), `D f ⊆ Bd C_u`, and
  `IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary` puts `Dbd f` in the closure of
  `Bd C_u \ D f`; near `Dbd f` the other disks are absent, and a point of `Bd C_u` off all disks
  is in `Bd N` (`IsTube.mem_frontier_of_mem_frontier_dualCell`), hence in the free face.
  "All or none": the pairs `Q_i \ DQ` (connected: between `Int Q_i` and `Q_i`) make adherence to
  `Int E \ {P'}` open and closed in that connected punctured 2-cell; every component is adherent
  (else it is clopen in `I \ {P'}`, which is connected: it lies between
  `Int C'_u ∪ Int C'_v ∪ {z₀}` and its closure, `z₀ ∈ h (D e \ Dbd e)`, `z₀ ≠ P'`); three
  components adherent at one point share a `Q_i \ DQ`, so there are exactly two, distinct by
  `hsep`. The arcs put `h F_u` in `U₁` (`freeFaceConnected`); `h (Bd C_u ∩ Bd N)` misses `I` by
  invariance of domain. `Ec = closure (Int E \ {P'})` gives `Ec ⊆ frontier U_i`.
- Every hypothesis is used (`hBu.1`, compactness of the arc, is not needed but is part of the
  frozen conjunction). `hP'` gives `P' ∈ h (D e)` (so `P' ∉ Int C'_u`); `hWsub`/`hWfr`/`hEW` give
  `E ∩ Bd Y ⊆ Ebd`; `freeFaceConnected`, `splitProper`, `splitCell`, `splitDisjoint`, `dualBall`
  are the tube fields used.
- Compiles: 3 module compiles (~60 s; `Σ` is a reserved token; two rewrite orders; one
  `norm_num` on `Fin 3`) + 1 audit.

## exists_edgeCollarFamily — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/EdgeCollarFamily.lean` (811 lines).
- Import line: `import DifferentialGeometry.Topology.PiecewiseLinear.EdgeCollarFamily`
- Statement and variable lines byte-identical to the skeleton (checked by script).
- New public names: defs `tetraDepth`, `tetraRadialPoint`, `tetraRadialProjection`,
  `tetraRadialCollar` (set-valued, no underscore); theorems `stdCenter_two_apply`,
  `tetraRadialPoint_apply`, `tetraRadialProjection_apply`, `tetraRadialPoint_one`, `tetraDepth_le`,
  `exists_eq_tetraDepth`, `le_tetraDepth`, `continuous_tetraDepth`, `tetraDepth_stdCenter`,
  `tetraDepth_eq_zero`, `tetraDepth_tetraRadialPoint`, `tetraRadialPoint_mem_stdSimplex`,
  `tetraRadialPoint_mem_openSimplex`, `eq_of_tetraRadialPoint_eq`, `dist_tetraRadialPoint_le`,
  `tetraRadialProjection_mem`, `tetraRadialPoint_tetraRadialProjection`,
  `tetraRadialProjection_eq_self`, `continuousAt_tetraRadialProjection`,
  `tetraRadialCollar_subset_stdSimplex`, `subset_tetraRadialCollar`,
  `tetraDepth_le_of_mem_tetraRadialCollar`, `stdCenter_notMem_tetraRadialCollar`,
  `mem_of_mem_tetraRadialCollar_of_notMem_openSimplex`, `exists_dist_le_of_mem_tetraRadialCollar`,
  `mem_of_mem_tetraRadialCollar_of_mem`, `isCompact_tetraRadialCollar`,
  `disjoint_tetraRadialCollar`, `starConvex_sdiff_tetraRadialCollar`,
  `exists_ball_inter_subset_tetraRadialCollar`. Grepped: no clash (`radialRetraction` exists in
  `DifferentialGeometry.Simplex`, hence the `tetra` prefix).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\EdgeCollarFamily.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T22:48:04Z, receipt SHA256 `AA077BD5…7FE2A175`).
- Audit: `AuditBatch2All.lean` in the output root, all declarations of the four Batch 2 modules,
  standard three axioms only, thirteen linters: `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch2All.lean with no diagnostics; shared outputs unchanged.`
  (22:49:09Z).
- Route: radial collars in the dual-cell models, as the stopped worker proposed. In `Δ ⊆ ℝ⁴`
  with barycentre `c`, `z = c + t (b - c)` with `t = 1 - 4·(least coordinate)` and `b` on the
  boundary, unique and continuous away from `c`. Collar over `B_a = g_a⁻¹ (h D e)` (a subset of
  `∂Δ` because `h D e ⊆ frontier (h C a)` and `g_a` is injective) with taper
  `τ_a = min (1/2) (δ_a/2) (dist(·, g_a⁻¹ h|K|)/2)`; `W e` = union over the two ends of the images.
  Closed (compact image); `W e ∩ h|K| = {h mid}` (collar meets the closed set only in `B_a`, and
  `h D e ∩ h|K| = {h mid}`); interior: at `y ∈ h (D e \ Dbd e)`, `y ≠ h mid`, the preimage `β` has
  `τ > 0`, and `B_a` is a boundary-neighbourhood of `β` since `Bd (h C a) ∩ Int (h C u ∪ h C v)
  ⊆ h D e`, so the collar contains a `Δ`-ball, whose image is relatively open
  (`exists_isOpen_inter_image_eq_of_isCompact`); collar points off the image disk are in the open
  simplex, hence interior, so the collar meets `Bd (h C u ∪ h C v)` exactly in `h Dbd e`;
  `h C a \ W e = g_a (Δ \ collar)` is the image of a set star-shaped about `c`; `W e ⊆ V a` by a
  common `ε` (finitely many vertices, `eventually_all_finite`) and uniform continuity of `g_a`;
  disjointness: same vertex — disjoint base sets (`splitDisjoint`); different vertices — the
  point lies on both cell frontiers, hence in both image disks.
- Compiles: 2 module compiles (~60 s) + the combined audit.

## Batch 2 summary

- Four CLOSED, 0 FALSE, 0 STUCK. Modules (all verified, receipts match current sources):
  `FreeFaceArc`, `HandleDecompositionOfEdgeCollars`, `TwoComponentsOfPseudoCell`,
  `EdgeCollarFamily`. The last three import `FreeFaceArc`, which imports the lead-accepted
  `HandlePieceSubsetOfEdgeCollars`. Register in this order:
  `import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc`
  `import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars`
  `import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell`
  `import DifferentialGeometry.Topology.PiecewiseLinear.EdgeCollarFamily`
- No frozen statement or predicate changed; no hypothesis added. `IsTube` still has no inhabitant
  in the tree, so all four are proved but untested on an instance (as the skeleton notes).
- Total: 8 module compiles, 3 audits, about 50 minutes wall clock.

# Batch 3 (lane F take-over)

Lease e, token `claude-agent-e-20260919`, output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e`. No existing file edited except this log;
no git write; no skeleton imported.

## exists_isTopologicalCellWithInterior_union_consecutive — CLOSED

- Files (all new, under `DifferentialGeometry/Topology/PiecewiseLinear/`), in dependency order:
  - `IntervalOrderExtension.lean` (256 lines), SHA-256
    `FE6F97AFBEBA29A87DF725C583C6F098A2EB4CBBFB814F6946DC5D532D84F2CB`;
  - `JordanRelativeMatching.lean` (451 lines), SHA-256
    `65C190C81FAFDEE68D9843A5EB9D742EFC287050D93A39256B9FB3E9556A3477`;
  - `ConsecutiveCellUnion.lean` (253 lines), SHA-256
    `DD659C1474DFC0A59486A8631C9C835C792078A7F7533E0F8B397DC5B583E1DF`.
- Import lines to register (this order):
  `import DifferentialGeometry.Topology.PiecewiseLinear.IntervalOrderExtension`
  `import DifferentialGeometry.Topology.PiecewiseLinear.JordanRelativeMatching`
  `import DifferentialGeometry.Topology.PiecewiseLinear.ConsecutiveCellUnion`
- Frozen block: `theorem exists_isTopologicalCellWithInterior_union_consecutive … := by`
  byte-identical to `Skeleton/Section31CanonicalConfiguration.lean` (checked by `diff`); namespace
  `DifferentialGeometry.Topology.PiecewiseLinear`, `section Leaves`, only `open Set Topology` in
  scope (the planar part's extra `open`s are confined to its own section).
- New public names (all grepped tree-wide, no clash). `DifferentialGeometry.Topology`:
  `exists_strictMonoOn_Icc_extension`, `strictMonoOn_or_strictAntiOn_of_between`.
  `DifferentialGeometry.Topology.PlanarJordan`: `exists_isArcBetween_sdiff_subset_inside`,
  `isCutPair_of_isLoop`, `false_of_isCutPair_of_inside_subset`,
  `not_lt_lt_of_isLoop_of_inside_subset`, `invFunOn_isLoop`, `invFunOn_isLoop_apply`,
  `continuousOn_image_of_continuousOn_comp`, `isLoop_comp_one_sub`, `image_comp_one_sub`,
  `exists_isLoop_image_eq_zero`, `continuousOn_injOn_image_of_isLoop_of_strictMonoOn`,
  `exists_matching_of_isLoop_of_strictMono`, `exists_matching_of_inside_subset`,
  `nonempty_homeomorph_closure_inside`, `isTopologicalCell_union_of_isTopologicalCell_inter`
  (the general planar producer Gemini's round 2 left open, exact proposed signature).
  `DifferentialGeometry.Topology.PiecewiseLinear`: the frozen leaf.
- Checker (final sources):
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\IntervalOrderExtension.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:22:27Z);
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\JordanRelativeMatching.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:38:34Z);
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ConsecutiveCellUnion.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:38:48Z).
- Audit: `AuditBatch3A.lean` (all declarations of the three modules, allowed axioms `propext`,
  `Classical.choice`, `Quot.sound`, thirteen linters without docBlame/docBlameThm):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch3A.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:39:38Z).
- Route. General planar theorem first: for closed disks `A, B` with `A ∩ B` a closed disk, `A ∪ B`
  is a closed disk. (1) Relative matching: Jordan curves `S, J` with `inside S ⊆ inside J` admit a
  homeomorphism `S → J` fixing `S ∩ J` pointwise. Base both curves at a common point; four common
  points interleaved on `J` but not on `S` would give disjoint crosscuts of `J` (one through
  `inside S`, one through the side it cuts off, both from the existing crosscut API plus a new
  crosscut-existence lemma via PL straightening) with interleaved ends — impossible by
  `crosscut_regions`/`arc_diff_subset_crosscut_side`; so the parameter correspondence preserves
  betweenness, is monotone after possibly reversing the loop, and extends (linear interpolation on
  the gaps, closedness of both parameter sets, order-iso ⇒ continuous) to a homeomorphism of
  `[0,1]`. (2) Crossed pasting: with `f : Bd C → Bd A`, `g : Bd C → Bd B` from (1), `g` on
  `Bd C ∩ Bd A`, `f` elsewhere is a continuous injection of `Bd C` onto
  `(A ∪ B) \ (Int A ∪ Int B) = Fr (Int A ∪ Int B)`; recognition of the open set as the inside of
  that Jordan curve and Schoenflies (`exists_image_closed_region_eqOn_compl`) give the disk. No
  finiteness of boundary intersections, no PL hypothesis, containment and equal disks covered.
  The frozen leaf is then the existing conditional consumer
  `exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion` (PlanarCellUnion) fed with
  this producer.
- Hypotheses used: `hc.halfPlane` (first coordinate plane), `hc.cell` (both cells and interiors),
  `hc.overlap j` (the intersection disk); `interior_mono` gives both `Dint` inclusions.
  `segmentSubset`, `consecutiveNe`, `interiorSubset`, `apart` are not needed.
- Compiles: 7 module checks, 3 audits (the last module/audit pair repeated after renaming one
  lemma and making the leaf's `:= by` byte-identical).

## separates_initialSurface — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/InitialSurfaceSeparates.lean` (313 lines),
  SHA-256 `ADA5E93563EC0583998897A61E5A67F81E0E0B95EE25ED89D5DEEF46E86C86F9`.
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.InitialSurfaceSeparates`
  (imports `PseudoCell` and the batch-2 `HandleDecompositionOfEdgeCollars`, hence `FreeFaceArc`).
- Frozen block: `open Classical in` + `theorem separates_initialSurface … := by` and the section's
  `variable` lines (including the unused `H B Jlo Jhi`, which Lean does not include) are
  byte-identical to `Skeleton/Section32PseudoCell.lean` (checked by `diff`); `local notation "E3"`
  and `open Set Topology` as in the skeleton.
- New public names (grepped, no clash): `DifferentialGeometry.Topology.Separates.image_homeomorph`;
  in `DifferentialGeometry.Topology.PiecewiseLinear`: `separates_image_interior_of_isEmbedding`,
  `isClosed_preimage_val_of_forall_mem_closure`, `mem_of_mem_closure_of_inter_subset_isClosed`,
  and the frozen leaf.
- Checker:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\InitialSurfaceSeparates.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:48:33Z).
- Audit `AuditBatch3B.lean` (all declarations of the module, standard three axioms, thirteen
  linters): `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch3B.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-22T23:49:52Z).
- Route. No limit argument is needed. Let `Σ = (⋃ i, S'' i) ∪ {P'}`. (1) Closedness in
  `I = Int (h C u ∪ h C v)` of the initial surface and of `Σ`: off `P'` the tower is locally finite
  (`locallyFinite`), and `T'' i ⊆ S'' i ⊆ φ '' S i`, so near each point both sets are finite unions
  of closed sets (odd tori minus the open union of even interiors is closed); `P'` lies in both.
  (2) `splitSeparates` is transported to `I` through `h`, which maps `Int (C u ∪ C v)`
  homeomorphically onto `I` (invariance of domain, `interior_image_eq_image_interior_of_isCompact`),
  giving that `h '' (D - Dbd)` separates `h u` from `h v` in `I`. (3) The general
  `Separates.of_frontier_subset_replacement` with `N := Σ`: both separators lie in `Σ`
  (`annuliEq` + `annulusImageSubset`: the open disk image is the tower annuli plus `P'`), the
  frontier of `Σ` in `I` lies on the initial surface (a frontier point off `P'` is on some `T'' j`
  and in no `Int S'' i`, split by parity), and `h u, h v ∉ Σ` (`havoid`, and `P' = h(midpoint)`
  with `vertex_ne_centroid_of_card_eq_two` and injectivity of `h`).
- Hypotheses used: `ht` (`splitSeparates`, `isEmbedding`, `dualBall`, `splitProper`,
  `isNeighborhood`, dual-cell/splitting-disk identities), `hu`, `hv`, `huv`, `he`, `hP'`, `havoid`,
  and from `htw` the fields `config` (`innerSubset`, `isPolyhedralSolidTorus`, `boundaryEq`,
  `annulusImageSubset` at index 0 of each triple), `annuliEq`, `locallyFinite`. Not needed:
  `apart`, `subsetW`, `subsetInterior`, `centerMemInterior`, `closureLower`, `closureUpper`, `W`.
  `IsTube`/`IsCanonicalTower` still have no inhabitant (untested, as the skeleton records).
- Compiles: 3 module checks, 1 audit.

## hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock — CLOSED (redundant `hℓ` reported)

- File: `DifferentialGeometry/Topology/PiecewiseLinear/StableCrossingDoubleCrossing.lean`
  (479 lines), SHA-256 `018C28E59B530075E2845BBE483094FA231C60E5C9AD05467EE0B5481743BF8D`.
- Import line to register:
  `import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingDoubleCrossing`
  (imports `StableCrossingBlock`, `StableCrossingNormalizer`, `NormalCrossingTransport`,
  `LocallyPolyhedral`; none modified).
- Frozen block: `theorem hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock [T2Space M] … := by`
  byte-identical to `Skeleton/GeneralPositionInDouble.lean` (repaired statement of ca345c4c8,
  checked by `diff`), in `section Ambient` with both `variable` lines of the skeleton, `universe u`,
  `open Set Topology`.
- New public names (grepped; one clash found and renamed): `isPLHomeomorphOn_univ_of_affineEquiv`,
  `isPLHomeomorphOn_image_of_eqOn_comp`, `eventually_inter_preimage_singleton_subset_of_isCompact`,
  `eventually_mem_image_iff_of_graph`, `exists_normalForm_of_two_graphs`,
  `hasPLNormalDoubleCrossingAt_chart_of_isStableCrossingBlock` (the general chart version, without
  `hec` and `hℓ`), and the frozen leaf.
- Checker:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\StableCrossingDoubleCrossing.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-23T00:10:01Z).
- Audit `AuditBatch3C.lean` (all declarations, standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch3C.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-23T00:10:46Z).
- Route (the fourth-pass plan of FILL_QUEUE). Preimages `xa ∈ SA`, `xb ∈ SB` of `y` from
  `sheets_nonempty_of_isStableCrossingBlock`; polyhedral relative neighbourhoods `A' ⊆ SA`,
  `B' ⊆ SB` of them in `D.domain` (`IsLocallyPolyhedral.exists_isPolyhedron_subset_mem_nhdsWithin`).
  On `A'`, `ec ∘ D = G_a ∘ projA` with `G_a (v,t) = A⁻¹ (a (v,t), v, t)` PL on `univ`, so it is a PL
  homeomorphism onto its image (`isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn` on the
  polyhedron). Near `ec y` the image of `A'` is exactly `{z | A z on graph a, projection in the
  block half-plane}` (the projection image of `A'` is a relative neighbourhood, through the
  continuous PL inverse of `projA`), same for `B'`. The accepted normalizer `H` (keeps `t`, graphs
  to `u = 0`, `v = 0`) composed with `A`, a translation and `A.linear⁻¹` is the PL chart `k` with
  planes `ker(u∘L)`, `ker(v∘L)` (finranks from `Module.Dual.finrank_ker_add_one_of_ne_zero`).
  Cases: `tlo = -r` (box disjoint from `BdM`) and `tlo = 0, t(y) > 0` give `HasPLDoubleCrossingAt`
  with `α = β = 0`; `tlo = 0, ℓ (ec y) = 0` gives `HasPLBoundaryDoubleCrossingAt` with
  `M := {z | 0 ≤ t(k z)}`, the `t = 0` half-space, via `(A z).2.2 = ℓ z`. Fibre coverage uses
  `T2Space M`: the domain minus the relative interiors of `A' ∪ B'` is compact, its image is closed
  and misses `y`. The chart is replaced by `exists_crossing_chart_mem_atlas` (no `HasGroupoid`).
- Hypotheses used: `[T2Space M]` (fibre coverage), `hec` (atlas transport), `hBdchart` (boundary
  case split), `h` (all twenty block fields except the compactness/closure fields of the outer
  box), `hy`, `hyB`. **Not used: `hℓ : ℓ ≠ 0`** (with `ℓ = 0` the block is already
  inconsistent: `tlo = -r` puts the inner block inside `ec.source ⊆ BdM`, `tlo = 0` forces the
  third coordinate of the affine equivalence `A` to vanish). Because the frozen signature keeps it,
  the leaf binds it with `let _ := hℓ` (the AGENTS pattern for a binder that cannot be removed);
  without that the unused-variable linter warns. Lead decision: drop `hℓ` from the frozen
  statement and its caller, or accept the binding.
- Compiles: 3 module checks, 2 audits, 3 small external probes (linter behaviour of unused
  hypotheses, `clear`).

## Batch 3 summary

- Three CLOSED, 0 STUCK, 0 FALSE. Five new modules, register in this order:
  `IntervalOrderExtension`, `JordanRelativeMatching`, `ConsecutiveCellUnion`,
  `InitialSurfaceSeparates`, `StableCrossingDoubleCrossing` (all under
  `DifferentialGeometry.Topology.PiecewiseLinear`). No existing file edited except this log; no
  statement changed; the three `.lean.wip` files of lane F are untouched.
- Re-check after the lead's `PseudoCell.lean` change (`rimFrontier`, 2026-09-23): prepare refreshed
  the stale cone; `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\InitialSurfaceSeparates.lean with no diagnostics; shared outputs unchanged.`
  (00:13:02Z, source unchanged, SHA-256 `ADA5E935…`) and `AuditBatch3B.lean` again `Verified … no
  diagnostics` (00:14:00Z). The other four modules do not import `PseudoCell` (0 stale objects).

# Batch 4 (A1 remaining leaves)

## `SingularTwoCell.exists_cutOutPiece_of_closure_subset` — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/CutOutPieceOfClosureSubset.lean` (193 lines).
  Import line (79 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.CutOutPieceOfClosureSubset`
- Statement byte-identical with `Skeleton/GeneralPositionInDouble.lean` (string comparison after
  CRLF normalization), same `variable {M : Type u} …` line and `universe u`.
- New public names (grepped tree-wide, unused before): the leaf, and
  `exists_convexHull_subset_face_of_mem_derivedNeighborhood` (every face of
  `derivedNeighborhood K L` lies in the hull of a face `σ` of `K` whose hull contains the centroid
  of a face of `L`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CutOutPieceOfClosureSubset.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-23 ~00:31Z).
- Audit `AuditBatch4A.lean` (standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch4A.lean with no diagnostics; shared outputs unchanged.`
- Route: `K₀ = D.domain ∩ D ⁻¹' closure V₀` and `D.domain ∩ D ⁻¹' Vᶜ` are disjoint compacta, so
  a `δ`-thickening of `K₀` misses the second. Triangulate the domain (`exists_simplicialComplex`),
  subdivide to mesh `< δ / 2` (`exists_isSubdivision_diam_lt`); the result `T` is a combinatorial
  two manifold with boundary (`IsPLBall.isCombinatorialManifoldWithBoundary`) and
  `frontier D.domain` is its boundary complex (`frontier_space_eq_boundaryComplex_space`).
  `L` = subcomplex generated by the simplices meeting `K₀`; `Rc = derivedNeighborhood T L`
  (manifold with boundary by `IsCombinatorialManifoldWithBoundary.derivedNeighborhood`);
  `Lc` = faces of `Rc` inside the frontier (their union is `Rc.space ∩ frontier` because an open
  simplex of the second derived meeting the boundary complex lies in its second derived);
  `Ω = interior (Rc.space ∪ D.domainᶜ)` (contains `L.space` by `derivedNeighborhood_mem_nhdsWithin`);
  `Ac` = faces of `Rc` meeting `Rc.space \ Ω`, `Nb` = complement of the union of the others. A face
  of `Ac` lies in a simplex `σ` of `T`; if `σ` met `K₀`, the face would lie in `L.space ⊆ Ω`.
- **Not used: `[T2Space M]`** (the conclusion lives in the domain only). The environment linter
  `unusedArguments` rejects the instance, so the leaf binds it with `let _ := ‹T2Space M›`, as for
  `hℓ` in batch 3. Lead decision: drop it from the frozen statement or accept the binding.
- Compiles: 4 module checks, 2 audits.

## `wallProductBlock_transport` — TARGET FALSE (counterexample; no file created)

The leaf lets `y` be *any* point of the inner block, and the old block's two neighbourhood
clauses only hold over the inner block. When `y` lies on the boundary of the inner box, sheet
points just outside the inner box enter every new inner block around `y`, and nothing controls
them there.

- Data (checked clause by clause against the Lean text). Take any data satisfying `hsys` (the
  skeleton's fixture) with an open three cell `c ∈ Cf` whose `wallSystemCellInt ρ c` contains,
  inside `Eb i` and away from `BdM`, the closed chart box `ec i ⁻¹' (A ⁻¹' blockBox r (-r))`
  for an affine equivalence `A` and some `r > 0` whose closure is compact in `(ec i).source`.
  Put `i' = i`, `N = univ`, `tlo = -r`, `a = 0`, `b = r / 4`, `La = Lb = 0`, `η = 1`. Source
  sets in `ℝ²` (coordinates `(p, q)`):
  `SA = {(v, t) ∈ [-r, r]² | t < r / 2 ∨ (r / 2 < t ∧ v ≤ 0)}`, `f (v, t) = ec⁻¹ (A⁻¹ (0, v, t))`;
  `SB = (10, 0) + [-r, r]²`, `f ((10, 0) + (u, t)) = ec⁻¹ (A⁻¹ (u, r / 4, t))`; `S = SA ∪ SB`.
  `y = ec⁻¹ (A⁻¹ (0, 0, r / 2))`.
- Old block valid: `hmapC` (images in the cell `c ⊆ C`); `S ∩ f ⁻¹' chartBlock = SA ∪ SB`;
  both graph equations; `blockSheetProjA = id` on `SA`, `blockSheetProjB = (· - (10, 0))` on
  `SB`, and both are PL homeomorphisms onto their images (every point of `SA` has a small
  rectangle, or rectangle ∩ `{v ≤ 0}`, inside `SA` as polyhedral neighbourhood); a sheet point
  over the inner block has `t < r / 2` (the row `t = r / 2` is not in `SA`), so `SA` and its
  projection are neighbourhoods there; `La * Lb = 0 ≤ 1 - η`; type (i) wall data from
  `chartBlock ⊆ wallSystemCellInt ρ c`; `hblkE`, `hy` (`t = r / 2` is on the top face of the
  inner box), `hy'`, `hN`, `hyN`.
- No new block exists. A new block centred at `y` has `tlo' = -r'` (`tlo' = 0` would force
  `ℓ i (ec i y) = 0`, i.e. `y ∈ BdM`), so its inner block contains an open neighbourhood of `y`,
  hence `f x_t` for `x_t = (0, t) ∈ SA`, `t ↓ r / 2`. Near `f x_t` the image of `S` is the half
  plane piece `{(0, v, t') | v ≤ 0}` with `f x_t` on its edge. If `x_t ∈ SA'`, every point of
  `SA'` projecting near `blockSheetProjA … x_t` lies (continuity of `a'`) near `f x_t`, so the
  projection of `SA'` near that point is an affine image of a half disc with the point on its
  edge (or a segment): not a neighbourhood, contradicting the inner neighbourhood clause. The
  same with `b'` for `x_t ∈ SB'`. But `x_t ∈ S ∩ f ⁻¹' chartBlock' = SA' ∪ SB'`.
- Where it matters: the only consumer is the plan of `hasStableCrossingBlocks_of_wallProductBlocks`,
  which transports at double points. Suggested repair (not proved): add
  `(hyd : y ∈ doublePointSet f S)`. Then both sheet points over `y` are inner points, the
  neighbourhood sets are relatively open, and a new block small enough around `y` sees only
  sheet points of the old inner block, where both clauses hold.

## `exists_normalizationPreparation_on_prescribedRegion` — CLOSED

- File: `DifferentialGeometry/Topology/PiecewiseLinear/NormalizationPreparation.lean` (242 lines,
  SHA-256 `5f18842b…`). Import line (77 characters):
  `import DifferentialGeometry.Topology.PiecewiseLinear.NormalizationPreparation`
- Statement byte-identical with the skeleton (string comparison), section variables
  `{M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]`, `universe u`.
- New public names (grepped, unused before): the leaf and
  `exists_uniformInjectivityScale_and_fiber_encard_le_two_of_close` (metric-target version of
  `exists_fiber_encard_le_two_of_close_of_injOn_starComplex`, whose target must be a normed group;
  same proof, and it also returns the scale `κ` of `exists_pos_eq_of_dist_lt_of_injOn_starComplex`).
- Checker: `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\NormalizationPreparation.lean with no diagnostics; shared outputs unchanged.`
  (2026-09-23 ~00:45Z). Audit `AuditBatch4B.lean`:
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch4B.lean with no diagnostics; shared outputs unchanged.`
- Route: `T` from `exists_isSubdivision_injOn_starComplex` (local injectivity through
  `Covering.isLocallyInjective_domRestrict_iff`); `κ`, `δ` from the helper; `ε = min ε₁ ε₂` with
  `cthickening ε₁ (ec '' (D '' Rc.space)) ⊆ ec '' V` and `ε₂` the uniform-continuity modulus of
  `ec.symm` on that compact set for `min δ (min d₀ d₁)`, where `thickening d₀ (D '' Ac.space)`
  misses `closure W` and `thickening d₁ (D '' (Rc.space ∩ frontier D.domain))` lies in the open
  set of points at which `B` is a relative neighbourhood in `BdM` (`hbuffer`).
- **Not used: `[CompactSpace M]` and `hWV : closure W ⊆ V`**; bound with `let _ := …` as in
  batch 3. Lead decision: drop them from the frozen statement or accept the bindings.
- Compiles: 1 module check, 1 audit.

## `hasStableCrossingBlocks_of_wallProductBlocks` — CLOSED (with the transport at double points)

- Files (six new modules, register in this order; import lines ≤ 100 characters):
  `WallSystemBlocks` (135 lines, SHA-256 `5f840f57…`), `StableCrossingBlockTransfer` (395,
  `1d601c7a…`), `KinkedBlockCoordinates` (277, `762c6af6…`), `StableCrossingBlockRecentre` (385,
  `7f2c4dd4…`), `WallChartTransition` (176, `03fc5327…`), `StableCrossingBlocksOfWallProductBlocks`
  (621, `ff8cfb09…`), all `import DifferentialGeometry.Topology.PiecewiseLinear.<Name>`.
- **Vocabulary hoisted (lead decision needed).** `WallSystemBlocks` contains byte-identical copies
  of the skeleton's definitions `HasStableCrossingBlocks`, `wallSystemCells`, `wallSystemWalls`,
  `wallSystemCell`, `wallSystemCellInt`, `wallSystemSkeleton`, `IsCommonWallSystem`,
  `WallProductBlock`, `HasWallProductBlocks` (a real module cannot import the skeleton).  When wiring,
  delete these nine definitions from the skeleton and import `WallSystemBlocks`; nothing else in the
  skeleton needs to change.  Their inhabitants are the skeleton's proved theorems.
- Leaf statement byte-identical (string comparison).  Checker:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\StableCrossingBlocksOfWallProductBlocks.lean with no diagnostics; shared outputs unchanged.`
  (~01:40Z); each of the other five modules verified the same way before it.  Audit
  `AuditBatch4C.lean` over all six modules (standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch4C.lean with no diagnostics; shared outputs unchanged.`
- New public names (all grepped, unused before): `IsPLHomeomorphOn.inter_preimage_of_isPolyhedron`,
  `IsPLHomeomorphOn.comp_of_univ`, `IsPLHomeomorphOn.image_mem_nhds_of_univ`, `blockSwap`,
  `blockSwap_apply`, `blockSwap_mem_blockBox_iff`, `chartBlock_trans_blockSwap`,
  `innerChartBlock_trans_blockSwap`, `blockSheetProjA_trans_blockSwap`, `blockSheetProjA_transfer`,
  `IsStableCrossingBlock.transfer`, `kinkOffset`, `kinkHeight`, `kinkHeightInv`, `kinkBound`,
  `max_kinkHeight`, `max_kinkHeightInv_sub`, `kinkHeight_kinkHeightInv`, `kinkHeightInv_kinkHeight`,
  `kinkHeight_surjective`, `kinkHeight_nonneg_iff`, `kinkHeight_eq_zero_iff`, `kinkHeight_self`,
  `kinkOffset_self`, `isPiecewiseAffineOn_add_mul_max`, `isPLHomeomorphOn_kinkShear`,
  `isPiecewiseAffineOn_add_kinkOffset`, `exists_kinkGraph`, `dist_le_kinkBound_mul`,
  `isCompact_blockBox`, `blockHalfPlane_eq_univ`,
  `exists_pos_forall_mem_nhdsWithin_of_isPLHomeomorphOn`,
  `IsStableCrossingBlock.exists_kink_recentre`, `AffineIndependent.comp_affineMap_of_injOn`,
  `exists_affineEquiv_eqOn_convexHull`, `IsCommonWallSystem.exists_transition`,
  `AffineMap.eq_add_smul_of_eqOn_plane`, `AffineMap.eq_mul_of_eq_zero_on_plane`,
  `neg_add_eq_kink_zero`, `neg_add_eq_kink_of_nonpos`, `neg_add_add_smul_eq_kink`,
  `neg_add_scale_eq_kink`, `WallProductBlock.exists_isStableCrossingBlock_at`, and the leaf.
- Route.  (1) `IsStableCrossingBlock.transfer`: all twenty fields of a block survive a change of
  block coordinates `(u, v, t) ↦ (u + α t, v + β t, γ t)` (planar maps PL homeomorphisms of the
  plane), with the sheets cut by the new box (a polyhedron in the projection plane) and graphs
  `a' (v + β t, γ t) = a (v, t) + α t`, so `La`, `Lb`, `η` are unchanged.  (2) Kinked family
  (translation, height scaling, shear switched on across `t = 0`).  (3)
  `IsStableCrossingBlock.exists_kink_recentre`: at a *double point* `y` of the inner block the two
  sheet points over `y` are old inner points; the neighbourhood clauses persist near them, so a small
  new box centred at `y` works.  (4) `IsCommonWallSystem.exists_transition`: on a three cell in both
  layers the transition is an affine equivalence (images of the four vertices are affine bases,
  because `chartAffine`'s maps are injective on the cell).  (5)
  `WallProductBlock.exists_isStableCrossingBlock_at`: type (i), type (ii) off the wall, type (iii)
  inside `C` use one cell; type (ii) on the wall uses the two transitions, which differ by a shear
  fixing `t = 0` with positive height factor (injectivity of `ec i₀`); type (iii) on `BdM` uses
  `ℓ i₀ ∘ T = μ ℓ j` with `μ > 0`.  (6) Leaf: finite subcover of the compact
  `doublePointSet f S ∩ Z'` (uniform injectivity gives local injectivity) by the open centred boxes
  of half size; a double point in such a box is in the inner block (for a boundary half block
  because `f` maps `S` into `C`).
- Hypotheses used: all (`[T2Space M]` for the compact closure of the new boxes and the closed `Z'`).
- About leaf `wallProductBlock_transport` (FALSE as stated, see above): the repaired version with
  `hyd : y ∈ doublePointSet f S` is proved here with conclusion `IsStableCrossingBlock` in chart
  `i₀` (not `WallProductBlock`: the new block's wall type is not produced), `A' (ec i₀ y) = 0` and
  `chartBlock ⊆ N`; it does not assert `chartBlock ⊆ old chartBlock` (true by construction, not
  exported).  That is all the leaf above needs.
- Compiles: 14 module checks (all six modules), 1 audit.

## `exists_commonWallComplex` — CLOSED

- File: `CommonWallComplex.lean` (424 lines, SHA-256 `c1628bbb…`), import line
  `import DifferentialGeometry.Topology.PiecewiseLinear.CommonWallComplex` (after
  `WallSystemBlocks`; it imports `WallSystemBlocks` for `IsCommonWallSystem`).
- Leaf statement byte-identical to the skeleton (string comparison, including `open Classical in`).
  Checker:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CommonWallComplex.lean with no diagnostics; shared outputs unchanged.`
  Audit `AuditBatch4D.lean` (standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch4D.lean with no diagnostics; shared outputs unchanged.`
- New public names (grepped, unused before): `isPiecewiseAffineOn_val_of_mem_maximalAtlas`
  (a maximal-atlas chart of a combinatorial manifold is piecewise affine, in ambient coordinates,
  on the realisation of its source: near a point it is a vertex-chart transition),
  `exists_wallSides_of_isCombinatorialManifold` (in a closed combinatorial three manifold a
  triangle has exactly two three-simplex cofaces), and the leaf.
- Route.  `A i := val '' closure (V i)` compact inside an ambient open `O i` with
  `val ⁻¹' O i = (ec i).source`; widths `d i` with `thickening (d i) (A i) ⊆ O i`, `μ := min d / 4`.
  A subdivision of mesh `< μ`; `L i` the subcomplex generated by the simplices meeting the
  `3 μ`-thickening; `exists_isSubdivision_affineOn_subcomplexes_finite` makes every `ec i`
  (extended by `0` off the realisation) affine on each simplex of a subdivision of `L i`; a final
  subdivision `Q` of mesh `< μ`.  `Eb i := val ⁻¹' cthickening μ (A i)`,
  `Eb' i := val ⁻¹' cthickening (2 μ) (A i)`.  `Cf`/`Bf` are the three simplices and triangles of
  `Q` inside `ι '' K.space` resp. `ι '' ∂K.space`; `Q` restricted to the image of `K` is a
  combinatorial three manifold with boundary (`isGlueIso_glued₂_id`,
  `IsCombinatorialManifoldWithBoundary.of_isSubdivision`) whose boundary is `ι '' ∂K`
  (`boundaryComplex_space_of_isPLHomeomorphOn`, `boundaryComplex_space_of_isSubdivision`), which
  gives `eqC`, `eqBd` (purity) and `boundarySides` (`mem_boundaryComplex_iff_unique_coface`).
- Hypotheses used: all.
- Compiles: 5 module checks, 1 audit.

## `exists_protectedSubdivision_in_adaptedChart` — STUCK (not attempted in Lean; analysis only)

- No counterexample found; I believe it TRUE.  Remaining goal = the whole conclusion.  Split:
  (a) elementary, for a fixed `R` with `ec ∘ D` affine on its faces (from `D.isPLOn` and `hec`)
  and `τ` small against the finitely many vertices: `IsPiecewiseAffineOn`, `dist < ε`, `EqOn` on
  `Ac`, `0 ≤ ℓ`, `ℓ = 0 ↔ Lc` (an `R`-simplex with all vertices on `Lc` lies in `Lc`: `ℓ ∘ ec ∘ D`
  is affine on it and `hproper`), the `Ac`-separation (compactness, `hAfree`), `MapsTo`, `⊆ K`;
  (b) `StarInj T g`: openness of injectivity on the closed stars of `T` under small vertex moves
  of the fixed `R` (disjoint simplices at positive distance; simplices sharing a face: the two
  image cones meet only in the common face, an open condition), plus the seam `g = D` on `Ac`;
  (c) `hprot` (persistence of PL normal crossings at double points touching frozen simplices)
  and (d) `hpersist` (margin-`η/2` blocks for `g`), both a perturbation-stability theorem as in
  the next leaf.  The docstring says (c), (d) are not on the assembly path: **lead decision** —
  dropping those two clauses would leave (a)+(b), a much smaller leaf.

## `wallProductBlocks_stable_on_fixedSubdivision` — STUCK (not attempted in Lean; analysis only)

- No counterexample found; I believe it TRUE as stated.  Route: (1) away from `Kt`, `g = D`
  (`g '' Rc.space ⊆ Kt`, `D '' Rc.space ⊆ interior Kt`), so the double point sets agree there and
  the old blocks, re-centred (type (ii) only along the wall, `t`-offset zero) so as to miss `Kt`,
  are retained by `isStableCrossingBlock_of_eqOn_compl`; (2) near `Kt ⊆ interior (Eb i₀)` all new
  blocks live in chart `i₀`: transport old blocks to `i₀` (the kinked transport of
  `WallProductBlock.exists_isStableCrossingBlock_at` keeps `t = 0` on the wall, so it can be
  upgraded to output the wall type), then perturb: in chart `i₀` the change `p_φ - p₀` is affine
  on each face of the fixed `R` with slope `O(τ / mesh R)` (in other charts it is not small in
  Lipschitz norm across a wall: `max (t, 0) - max (t - τ, 0)` has slope one — that is why the new
  blocks must be in `i₀`).  Needed and absent from the tree: bi-Lipschitz bounds for PL sheet
  projections, a graph-perturbation lemma (`La' ≤ La + O(τ)`), full-preimage stability from
  `hcert` (uniform injectivity, fibres ≤ 2).  The "same wall" question: the new type (ii) blocks
  in `i₀` keep the transported wall, so no correspondence clause is needed for existence.

## `wallProductBlocks_of_wallGenericity` — CLOSED (13 new modules; margin `η' = 1`)

- Files, in dependency (register) order, all `import DifferentialGeometry.Topology.PiecewiseLinear.<Name>`:
  `WallSystemCellTopology` (279 lines, `d32f6dfa…`), `FreeGermVocabulary` (72, `1fe76bfd…`),
  `WallChartLocalPicture` (312, `58635795…`), `BlockCoordinateAlgebra` (245, `6a50dab5…`),
  `SheetBlockAssembly` (312, `77db6143…`), `GluedDoublePointFaces` (357, `d977e9ad…`),
  `GluedEdgeSides` (165, `3eb48b1a…`), `GenericDoublePointSheets` (136, `8e8cf3a6…`),
  `TriangleCrossingBlock` (425, `c01f8586…`), `EdgeSideCoordinates` (148, `0509de62…`),
  `EdgeCrossingBlock` (524, `d0da4e51…`), `BoundaryCrossingBlock` (651, `56614a5f…`),
  `WallProductBlocksOfWallGenericity` (305, `e15d21e7…`).
- Leaf statement byte-identical (string comparison, including `open Classical in`).  Each module
  checker-verified (`Verified … with no diagnostics; shared outputs unchanged.`), the last:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\WallProductBlocksOfWallGenericity.lean with no diagnostics; shared outputs unchanged.`
  Audit `AuditBatch4E.lean` over all 13 modules (standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch4E.lean with no diagnostics; shared outputs unchanged.`
- **Hoisted (lead decision, as for `WallSystemBlocks`)**: `WallSystemCellTopology` is a verbatim
  copy of the skeleton's `wallSystemStar` and of its proved lemmas `wallSystemCellInt_subset_…`
  through `subset_iUnion_wallSystemCell_of_eq_boundary` (skeleton lines 785–787, 818–1056);
  `FreeGermVocabulary` is a verbatim copy of `FreeSourceGerm`, `IsFreeDoubleGerm`,
  `IsFreeBoundaryDoubleGerm`, `IsFreeInteriorDoubleGerm`, `regionGluedMap`.  Delete those from the
  skeleton when wiring and import the two modules.
- New public names (grepped, one definition each): `IsCommonWallSystem.injOn_chartAffine`,
  `IsCommonWallSystem.exists_wallChart_sides`, `IsCommonWallSystem.isClosed_physicalBoundary`,
  `exists_affineEquiv_prod_of_independent`, `exists_affineEquiv_flatSheets`,
  `exists_affineEquiv_bentSheet`, `isHPolytope_blockBox`,
  `exists_isOpen_inter_preimage_subset_ball_union`, `exists_pos_chartBlock_subset_of_isOpen`,
  `isStableCrossingBlock_of_sheets`, `eq_on_of_sum_smul_eq_of_affineIndependent`,
  `not_affineIndependent_insert_of_eq_sum`, `eq_of_simplicialMap_eq_of_affineIndependent`,
  `affineIndependent_of_wallGuard`, `convexHull_subset_of_subset_boundaryVertices`,
  `not_subset_boundaryVertices_of_card_eq_three`, `faces_cases_of_simplicialMap_eq`,
  `exists_linearEquiv_prod_of_independent_pair`, `exists_apply_sub_eq_mul_of_mem_convexHull_insert`,
  `exists_pos_forall_mem_ball_mem_convexHull_insert`,
  `exists_insert_mem_faces_of_mem_closure_interior`, `eq_or_eq_of_encard_le_two`,
  `exists_sum_eq_one_apply_eq_sum_smul`, `not_affineIndependent_insert_of_mem_range`,
  `not_affineIndependent_insert_of_eq_lineMap`, `exists_homeomorph_apply_eq_sub`,
  `exists_homeomorph_kinkShear`, `regionGluedMap_of_mem`, `exists_apply_eq_apply_ne_zero`,
  `exists_eq_add_smul_of_mem_openSimplex_pair`, `pair_independent_of_affineIndependent_insert`,
  `exists_eq_insert_of_ssubset_of_card_eq_two`, `exists_edgeSideCoordinates`,
  `exists_boundaryEdgeSheet`, `exists_wallProductBlock_of_triangle_crossing`,
  `exists_wallProductBlock_of_edge_crossing`, `exists_wallProductBlock_of_boundary_crossing`,
  and the leaf.
- Route.  Fibre `{x₁, x₂}` (`hgfiber`), both free (`hfree`), carried by faces of `R`;
  `faces_cases_of_simplicialMap_eq`: the guard (independence on `≤ 4` vertices, `≤ 3` on the
  boundary; a triangle never has three boundary vertices) and uniform injectivity leave exactly
  two disjoint triangles, an edge and a disjoint triangle, or two disjoint boundary edges.
  Triangles: flat sheets `u = 0`, `v = 0`; type (i) off the walls, type (ii) on a wall `w` with
  `t` the side functional of `exists_wallChart_sides` (the double line is transverse to the wall
  because `hgencross` puts double points in both open cells).  Edge/triangle: the edge is interior,
  has coface triangles on both sides, `p = A⁻ + max (f (· - x₁)) 0 • w` near it, block
  coordinates with the bent sheet `u = max t 0` over a kinked shear (`La = 0`), type (i) by
  `hgenfold`.  Boundary edges: one coface triangle each (the source is a PL disc:
  `IsPLBall.closure_interior`; triangles on both sides would make the point interior), half block
  with `t = ℓ` exactly, type (iii) for the boundary wall through `y`.  All blocks have
  `La * Lb = 0`, margin `1`.  Finite subcover of the compact double point set over `closure W`
  by half-size cubes.
- Unused hypotheses of the frozen leaf (kept by `let` bindings): `hfiber`, `hproper`, `hVopen`,
  `hWV`, `hRfin`, `hRV`, `hε`, `hsmall`, `hfrozen`, `hD'K`, `hKV`.
- Lesson: `EuclideanSpace ℝ (Fin 2)` has a real `DecidableEq` instance (`WithLp.instDecidableEq`);
  generic lemmas stated under `open Classical` build `insert` with `propDecidable` and do not
  unify with the concrete statements, so generic lemmas take `[DecidableEq E]` binders.

## `exists_wallGenericVertexMap` — STUCK (analysis only; no counterexample; believed TRUE)

- Remaining goal: the whole conclusion.  Reduction, checked against the leaf's hypotheses: take
  `φ = ec ∘ D` on frozen vertices, Bv vertices moved inside `ker ℓ`, the others inside `ℓ > 0`,
  close enough that `simplicialMap R φ` maps `Rc.space` into `ec.target` and the glued image
  stays in `interior (Eb i₀)` (compactness; `hlinear` gives `simplicialMap R (ec ∘ D) = ec ∘ D`
  on `Rc.space`).  Then a free double point is a pair `x₁ ≠ x₂` in free simplices with
  `p x₁ = p x₂`, and in the layer walls and one-skeleton are affine in the chart (`starLayer`,
  `chartAffine`).  The conclusion follows from finitely many general-position conditions on the
  free vertex images: (G1) the guard; (G2) for free faces `σ ≠ σ'` sharing at most one vertex and
  a skeleton edge or vertex `e` in the layer, `hull (φ σ) ∩ hull (φ σ') ∩ chart e = ∅`;
  (G3) for a free edge or vertex `σ`, a free face `σ'` and a wall `w`,
  `hull (φ σ) ∩ hull (φ σ') ∩ chart w ⊆ ker ℓ`; (G4) for free triangles `σ, σ'` sharing at most
  one vertex and a wall `w`, the line `aff (φ σ) ∩ aff (φ σ')` is not in the wall plane.
  (G1)+(G2) give `hgenskel`; (G1)+(G3) give `hgenfold`; (G1)+(G2)+(G4) give `hgencross` (the
  double set near an interior germ is that line; its two sides are the two open cells, as in
  `IsCommonWallSystem.exists_wallChart_sides`, proved for leaf 9).
- What is missing.  `ArrangementGeneralPosition.lean` already places free vertices one at a
  time inside their arrangement layer (`exists_mem_openCell_notMem_affineSubspaces`,
  `exists_small_affineIndependent_constraints_in_arrangement`,
  `exists_small_vertexMap_transverse_in_arrangement`), which covers (G1) and all four-point
  incidences (including fixed chart points of `Q`).  (G2)–(G4) are *triple* incidences (two free
  faces and a fixed wall or skeleton face): for the last placed vertex of a pair of faces without
  common vertex the bad positions lie in one plane (e.g. `aff (b, c, x₀)` with
  `x₀ = aff σ' ∩ line e`), given the four-point conditions; but when the last placed vertex is
  the vertex *shared* by two triangles, the bad positions form a ruled quadric
  (`⋃ x ∈ line e, aff (x, b, c) ∩ aff (x, d, e)`), not a union of affine subspaces, so the
  framework's "avoid finitely many proper affine subspaces" step does not apply.  The surface
  is the range of a polynomial map `ℝ² → ℝ³`, so Mathlib's `ContDiff.dimH_range_le`, `dimH_union`
  and `Real.dimH_of_nonempty_interior` give the missing avoidance step (a new per-vertex lemma
  "avoid finitely many affine subspaces and finitely many `C¹` ranges of `ℝ²`" next to
  `exists_mem_openCell_notMem_affineSubspaces`).  These sector-overlap double points are
  robust (the leaf has no local injectivity hypothesis), so they cannot be perturbed away.
  Estimated size: several thousand lines.

# Batch 5 (A1 vertex map)

## `exists_wallGenericVertexMap` — CLOSED (7 new modules)

- Files in dependency (register) order, all `import DifferentialGeometry.Topology.PiecewiseLinear.<Name>`:
  `ArrangementGeneralPositionDimension` (173 lines, `9a065025…`), `RuledSurfaceOfPlanePencils`
  (290, `0dd8a7a4…`), `GenericPlacementSteps` (443, `bbe7e378…`), `GenericPlacementClauses`
  (687, `0a2d49a3…`), `GenericVertexMapLinesPlanes` (410, `b6319c63…`),
  `AdmissibleVertexMapVocabulary` (110, `5eeb53f8…`), `WallGenericVertexMap` (951, `4bfcf955…`).
- Leaf statement byte-identical (string comparison, including `open Classical in`).  Each module
  checker-verified, the last:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\WallGenericVertexMap.lean with no diagnostics; shared outputs unchanged.`
  Audit `AuditBatch5A.lean` over the seven modules (standard three axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch5A.lean with no diagnostics; shared outputs unchanged.`
- **Hoisted (lead decision, as before)**: `AdmissibleVertexMapVocabulary` is a verbatim copy of the
  skeleton's `AdmissibleVertexMap`, `AdmissibleVertexMap.mono` and
  `exists_admissibleVertexMap_of_adaptedChart` (the inhabitant).  Delete them from the skeleton and
  import the module.
- The funded per-vertex lemma (lead's request): `exists_mem_openCell_notMem_affineSubspaces_notMem_ranges`
  in `ArrangementGeneralPositionDimension`, next to `exists_mem_openCell_notMem_affineSubspaces`:
  a point of the open cell, `ε`-close, off finitely many affine subspaces not containing the layer
  and off finitely many ranges of `C¹` maps from a space of dimension less than the layer's
  (`Real.Convex.dimH_eq_finrank_vectorSpan`, `ContDiff.dimH_range_le`, `dimH_iUnion`).  The
  induction itself uses the underlying `exists_mem_inter_notMem_of_dimH_inter_lt` (any set `B` with
  `dimH (B ∩ L) < finrank L.direction`), which lets bad sets of different kinds be united.
- Route.  (1) Generic core `exists_small_vertexMap_generic_lines_planes_in_halfSpace` (abstract
  vertex type, frozen set, boundary set, finitely many lines `S j` and planes `P j`): free boundary
  vertices placed first inside `ker ℓ` (bad sets: affine subspaces not containing `ker ℓ`; for the
  guard a plane of three placed vertices equal to `ker ℓ` would put four guarded vertices on the
  boundary), then the other free vertices inside `0 < ℓ` (bad sets of `dimH < 3`).  Clauses: guard;
  vertices off planes; positive combinations of two triangles sharing ≤ 1 vertex / triangle and
  disjoint edge / two disjoint boundary edges never agree on a line; triangle ∩ disjoint
  non-boundary edge off planes; double line of disjoint triangles not in a plane (internally also:
  vertices off lines, lines not in triangle planes).  Every case with the new vertex in one face
  only is affine (`mem_affineSpan_insert_image_erase_of_sum_smul`); the vertex shared by two
  triangles gives the ruled surface `(t, s) ↦ z(t) + s • (n₁ × n₂)` (`RuledSurfaceOfPlanePencils`,
  cross products), the only non-affine bad set.  (2) Leaf: lines through `A_c q₀, A_c q₁` for two
  vertices of each cell `c` (`A_c` from `chartAffine`), planes `affineSpan (A_c '' w)`; the
  perturbation is below the distance from `ec ∘ D (Rc.space)` (compact) to the complement of
  `ec '' (interior (Eb i₀) ∩ source)`, so `g = ec.symm ∘ p` on `Rc.space` with values in `Eb i₀`;
  `hlinear` gives `simplicialMap R (ec ∘ D) = ec ∘ D` and no boundary triangle; classification
  `faces_cases_of_simplicialMap_eq_of_guard` (no injectivity scale, so TT sharing a vertex is
  allowed); at an interior crossing on a wall the double line is transverse to the wall plane and
  the curves `xᵢ + t • eᵢ` inside the triangles give double points on both sides of `ν`.
- Unused hypotheses of the frozen leaf (kept by `let` bindings): `hLR`, `hAR`.
- Lesson: a 600-line single proof hit the per-declaration heartbeat limit (no `maxHeartbeats`
  allowed); split into `notMem_wallSystemSkeleton_of_generic`, `notMem_wallSystemCell_of_generic_edge`,
  `exists_wallSystemCells_of_generic_crossing` and the leaf.  `Π` is a reserved token (not a valid
  identifier character in `hΠ`).

## `exists_protectedSubdivision_in_adaptedChart` — CLOSED, all four clauses (7 new modules)

- Files in dependency (register) order, all `import DifferentialGeometry.Topology.PiecewiseLinear.<Name>`:
  `PlaneBoxGraphPerturbation` (199 lines, `5675c646…`), `StableCrossingBlockPerturbation`
  (860, `4004a78f…`), `ProtectedSubdivisionTools` (260, `cc43ae4a…`),
  `ProtectedSubdivisionClauses` (308, `56eac239…`), `ProtectedSubdivisionStarInj` (165,
  `702847e5…`), `ProtectedSubdivisionBlocks` (438, `6ca3381b…`),
  `ProtectedSubdivisionInAdaptedChart` (514, `86029022…`).
- Leaf statement byte-identical (string comparison, including `open Classical in`); no clause
  dropped.  Last module:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ProtectedSubdivisionInAdaptedChart.lean with no diagnostics; shared outputs unchanged.`
  Audit `AuditBatch5B.lean` over the seven modules (three standard axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch5B.lean with no diagnostics; shared outputs unchanged.`
- (c) `hprot` and (d) `hpersist` are provable from the hypotheses; nothing weakened.  Route.
  (1) Perturbation of one block (`IsStableCrossingBlock.exists_perturbation`): a block centred at a
  double point stays a block with the same coordinates on a smaller cube and margin `η / 2` for
  every `g` with `ec ∘ g = ec ∘ f + δ` on the sheets, `δ` piecewise affine and `λ`-Lipschitz on
  the plane, `λ` small: on a square `B₀` inside both sheet images, `σ = (sheet projection)⁻¹` and
  the graph function are Lipschitz (PL on a polyhedron: `exists_lipschitz_extension`); the new
  sheet is the graph of `(a + e₁, id + e₂)` with `e = A.linear ∘ δ ∘ σ`; `id + e₂ ∘ clamp` is a
  PL homeomorphism of the plane (`isPLHomeomorphOn_id_add_of_lipschitz`), the new graph function
  is `(a + e₁) ∘ clamp ∘ ψ⁻¹` with `v`-Lipschitz constant `La + 2 (La + Lt + 1) μ`
  (`PlaneBoxGraphPerturbation`); for half blocks `ψ` keeps the lower half plane because `δ` does
  not move the frontier off `ℓ = 0`.  (2) Regional form: recentring (`exists_kink_recentre` with a
  translation) puts each sheet in `Ω` or off `closure (Rc \ Ac) ⊆ Ω`; on `Ω` the glued map is
  `ec ∘ D + Σ_v b_v • (φ v - ec (D v))` (Lipschitz vertex functions from `GeneralPosition`), off
  it the glued map is `D`.  (3) Finitely many recentred blocks cover the compact
  `DP(D) ∩ Z ∩ closure (V \ closure W)`; the injectivity scale of `hcert` (via clause (b)) and a
  positive minimum on pairs at distance `≥ κ` put every double point of the glued map over that
  set into one of them.  (4) `hprot`: a double point with a preimage in a face touching `Ac` is
  off `closure W` (separation clause), so over `closure (V \ closure W)`, so in a block of the
  glued map, which is a `SingularTwoCell` (`isPLOn_regionGluedMap`), and
  `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` applies.  (a): `R` from
  `exists_isSubdivision_affineOn_faces`, then a Lebesgue-number subdivision (closed stars inside
  injectivity neighbourhoods and small balls; mesh below half the chart distance between `D (Ac)`
  and `closure W`); `K` is the chart preimage of a closed thickening of `ec (D (Rc))`.  (b):
  `starInj_of_forall_injOn_nhds` (Lebesgue number for close pairs, positive minimum of
  `dist (D x) (D x')` on pairs in one star at distance `≥ β`).
- Unused hypotheses of the frozen leaf (kept by `let` bindings): `hfiber`, `hnormal`, `hOopen`,
  `hZO`, `hRman`, `hLR`.
- Lessons: `ContinuousOn.dist` does not exist (use `continuous_dist.comp_continuousOn (f.prodMk g)`);
  `IsPiecewiseAffineWithinAt.comp` needs `(f := …)`, otherwise higher-order unification picks a
  wrong `f`; `DecidableEq (EuclideanSpace ℝ (Fin 2))` resolves to the `WithLp` instance even under
  `open Classical`, so star statements are kept generic (`closedStar`; no `starComplex` at `ℝ²`);
  the block perturbation hit the per-declaration heartbeat limit until split into four lemmas.

## `wallProductBlocks_stable_on_fixedSubdivision` — CLOSED (3 new modules; statement as frozen)

- Files in dependency (register) order, all `import DifferentialGeometry.Topology.PiecewiseLinear.<Name>`,
  after the seven leaf-6 modules: `WallProductBlockTypedTransport` (594 lines, `d6e7be97…`),
  `WallProductBlockPerturbation` (611, `06f7ff8a…`), `WallProductBlocksStableOnFixedSubdivision`
  (511, `63fb1aa2…`).
- Leaf statement byte-identical with skeleton lines 1317–1366 (string comparison, including
  `open Classical in`).  Last module:
  `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\WallProductBlocksStableOnFixedSubdivision.lean with no diagnostics; shared outputs unchanged.`
  Audit `AuditBatch5C.lean` over the three modules (three standard axioms, thirteen linters):
  `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e\AuditBatch5C.lean with no diagnostics; shared outputs unchanged.`
- Route.  (1) Typed transport (`WallProductBlock.exists_wallProductBlock_at`): at a double point
  `y` of an old inner block of chart `j`, with `y ∈ Eb i`, a wall product block of chart `i`
  centred at `y` inside any open `N ∋ y`; type read off the position of `y` (open cell: type (i);
  on the wall of a type (ii) block: kinked coordinates keep `t = 0` exactly on the wall; on
  `BdM`: half block with height `ℓ i`); open cells meet every neighbourhood of a point of the
  closed cell (`exists_mem_wallSystemCellInt_of_mem_nhds`, `ρ` a closed embedding of compact `M`).
  (2) Per double point `y` of `D` in `closure N'` (`closure N' ⊆` old neighbourhood):
  if `y ∈ Kt`, transport into chart `i₀` inside `interior (Eb i₀)` and perturb regionally
  inside the coordinate ball of the transported block
  (`IsStableCrossingBlock.exists_regional_perturbation_subset`, same coordinates since the block
  is centred); a centred sub-block inside that ball keeps the side and the type
  (`WallProductBlock.of_subset_ball`; the type (iii) cell lies in `C` because its open cell meets
  the block on the closed side of `ℓ`).  If `y ∉ Kt`, transport within chart `j` inside
  `Ktᶜ` and inside the old block (`IsStableCrossingBlock.exists_isOpen_mem_chartBlock`, the `BdM`
  case forcing a half block); since `D (Rc) ⊆ Kt` and the glued map sends `Rc` into `Kt`, the
  glued map equals `D` at every source point either map sends into the block
  (`IsStableCrossingBlock.congr_of_eq`), margin `η → η / 2`.  (3) The ℓ-clauses in chart `i₀`
  (`AdmissibleVertexMap.normal_simplicialMap_clauses`) need no mesh: affineness of `ecf i₀ ∘ D`
  on the faces of `R`, `hproper`, signs of `ℓf i₀ ∘ φ`.  (4) Finite subcover of
  `DP(D) ∩ closure N'`, Φ-argument with `Q := closure N'` and the injectivity scale of `hcert`,
  `τ` below the minimum of `τ₀`, the closeness scales, the Lipschitz scales over the vertex
  displacement constant and the chart-inverse modulus; the new neighbourhood is `N'`.
- No correspondence with the old block family is promised or used (the conclusion quantifies the
  new family afresh); a type (ii) new block exists only at points on an old type (ii) wall, and
  keeps that wall.
- Unused hypotheses of the frozen leaf (kept by `let` bindings): `hfiber`, `hVopen`, `hWV`,
  `hRfin`, `hΩcover`, `hε`, `hactive`; the premises `IsPiecewiseAffineOn` and the separation
  clause of the conclusion's `∀` are not used either.
- Lessons: the checkout's prepare script needs the full module name
  (`DifferentialGeometry.Topology.PiecewiseLinear.<Name>`), with a short name it reports an empty
  import closure; `rw [hA'eq] at …` after `AffineEquiv.ext` is safer than `subst` when both sides
  are obtained variables.
