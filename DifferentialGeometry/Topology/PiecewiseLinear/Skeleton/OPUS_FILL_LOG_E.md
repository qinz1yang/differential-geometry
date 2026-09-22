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
