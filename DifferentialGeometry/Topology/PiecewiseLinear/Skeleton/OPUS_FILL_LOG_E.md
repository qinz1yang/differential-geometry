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
