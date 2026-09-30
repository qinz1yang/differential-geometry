# Local modifications

Upstream: <https://github.com/alonamaloh/schoenflies-lean>, commit
`05a43d29cde026618777db3d4e4316204ccca237`, licensed under Apache-2.0.

The complete 128-module transitive dependency closure of
`Schoenflies.jordan_schoenflies_of_homeomorph` is included together with the
upstream `Compose.lean` and `InitialReverseTransfer.lean` modules. Internal
imports were relocated from `Schoenflies.*` to
`DifferentialGeometry.External.Schoenflies.*`. Upstream mathematical
namespaces and declaration names are otherwise retained.

Every modified Lean source carries a local-modification notice while preserving
the original copyright and author lines. The original `LICENSE`, README content
(`UPSTREAM_README.md`), and `formalization.yaml` are retained. The sources use
this project's Lean and Mathlib 4.33.1 configuration.

## 2026-09-11: Lean 4.33.1 reconciliation

The compatibility work from Ayush Khaitan's commits `ed97bb87e`, `392dcfd56`,
and `54009db02` was reconciled with the existing vendor tree.

- Removed `set_option autoImplicit true` from the 128-module theorem closure
  and explicitly bound the parameters it formerly inferred. `Compose.lean` and
  `InitialReverseTransfer.lean` remain outside that closure and retain the
  upstream option.
- Replaced deprecated set and graph APIs with their Lean 4.33.1 names:
  `Set.mem_ofPred_eq`, `Graph.edgeSet_eq_setOfPred_exists_isLink`,
  `Set.ofPred_and`, `Set.domRestrict`, `Set.domRestrict_apply`,
  `Set.range_domRestrict`, and `continuousOn_iff_continuous_domRestrict`.
- Replaced proposition-valued proof-local `letI` and `haveI` declarations by
  ordinary `let` or `have` declarations where the current source linters
  require them.
- Removed the redundant simp attributes from `det_perp_perp`, `poly_pair`,
  `Graph.mem_vertexSet_induce_component`, and
  `Graph.IsCycleThrough.cycleGraph_vertexSet`; the declarations themselves are
  retained.
- Removed unnecessary graph-finiteness assumptions from
  `Graph.IsAcyclic.longest_path_source_is_leaf`,
  `Graph.IsAcyclic.longest_path_target_is_leaf`,
  `Graph.IsDrawing.edge_radial_unique`, and
  `Graph.IsDrawing.not_three_localDirs_on_edge`.
- Removed unused infinity assumptions from the finite-transfer ear-step
  predicates and from the assembly theorems that consume already constructed
  ear steps. Infinity assumptions remain on constructions that select fresh
  cell names.
- Explicitly bound the refined domain in `RefinementStars.lean`, the real
  coordinates in `Strip.lean`, the arbitrary parameter set in
  `Polygonal.lean`, the graph variables in `Graph/Relabel.lean`, the input type
  of `exists_injective_pinned_avoiding`, and the cell-name type in
  `FreshDenseSelection.lean`.
- Made the affine reparametrization and unit interval explicit in
  `Subarc.lean` before transporting the segment-image equality.
- Qualified the Schoenflies graph namespace openings in
  `SourceAttachment.lean`, `SourceJoining.lean`, and `OverlayExtension.lean`.
- Applied whitespace-only repairs required by `git diff --check`.

## Mac strict copyright-header parsing, 2026-09-23

The provenance text following each Authors line is preserved in a separate adjacent
comment so that the standard header linter reads only author names in that field.
Copyright, licensing, attribution and provenance wording are unchanged. No declarations,
proofs or imports change; no linter is disabled. Affected source files:

- `Accessible.lean`
- `AccessibleJoin.lean`
- `AlternatingCrosscuts.lean`
- `ArcCollars.lean`
- `ArcComplement.lean`
- `ArcComplementPrep.lean`
- `ArcMonotone.lean`
- `BoundaryAnchors.lean`
- `BoundaryContinuity.lean`
- `BoundaryContinuity2.lean`
- `BoundaryCycles.lean`
- `BoundaryCyclesGenerated.lean`
- `Bounded.lean`
- `CellulationInvariants.lean`
- `CombinatorialInvariance.lean`
- `CommonSubdivision.lean`
- `Concatenate.lean`
- `CrosscutAtMostTwo.lean`
- `CrosscutCells.lean`
- `CrosscutEncloses.lean`
- `CrosscutExists.lean`
- `Curve.lean`
- `Direction.lean`
- `Endgame.lean`
- `FaceCycles.lean`
- `FaceCyclesLand.lean`
- `FaceCyclesProof.lean`
- `FiniteTransfer.lean`
- `FiniteTransferTarget.lean`
- `FiniteTransferTargetMesh.lean`
- `FreshAccess.lean`
- `FreshDenseSelection.lean`
- `GeneralCrosscut.lean`
- `GeneratedStructure.lean`
- `Graph/Component.lean`
- `Graph/Cycle.lean`
- `Graph/CycleJordan.lean`
- `Graph/Degree.lean`
- `Graph/Drawing.lean`
- `Graph/Ear.lean`
- `Graph/K33.lean`
- `Graph/K33Closed.lean`
- `Graph/K33Land.lean`
- `Graph/K33Planar.lean`
- `Graph/OuterFace.lean`
- `Graph/PathGraph.lean`
- `Graph/Redrawing.lean`
- `Graph/Relabel.lean`
- `Graph/RelativeEar.lean`
- `Graph/Tree.lean`
- `Graph/TwoConnected.lean`
- `Graph/TwoPaths.lean`
- `Graph/VertexSquares.lean`
- `Graph/Walk.lean`
- `GridAttach.lean`
- `InitialGenerated.lean`
- `InitialOuterCycle.lean`
- `InitialPair.lean`
- `InitialPairFixed.lean`
- `InteriorHomeomorphism.lean`
- `Inversion.lean`
- `Jordan.lean`
- `JordanClosed.lean`
- `JordanSchoenflies.lean`
- `JordanSeparates.lean`
- `LimitMap.lean`
- `Line.lean`
- `LocalGrid.lean`
- `LocallyPolygonal.lean`
- `MatchedArc.lean`
- `MatchedSplit.lean`
- `ModelCurve.lean`
- `OuterChain.lean`
- `OuterChainClosed.lean`
- `Overlay.lean`
- `OverlayExtension.lean`
- `OverlayGraph.lean`
- `Parity.lean`
- `ParitySplitting.lean`
- `Plane.lean`
- `PolyArcRealize.lean`
- `PolyLocal.lean`
- `PolyPath.lean`
- `PolygonBridge.lean`
- `Polygonal.lean`
- `PolygonalCarrier.lean`
- `PolygonalCrosscut.lean`
- `PolygonalJordan.lean`
- `PrePolygonArc.lean`
- `PrePolygonSep.lean`
- `QuantitativeForwardStages.lean`
- `QuantitativeRecursion.lean`
- `QuantitativeStages.lean`
- `Realization.lean`
- `RealizeSplit.lean`
- `RealizeSubdiv.lean`
- `RealizeSubdivHomeo.lean`
- `RefinementStars.lean`
- `SegmentCut.lean`
- `SegmentMeet.lean`
- `SegmentOrder.lean`
- `SimpleArc.lean`
- `SkeletonAccess.lean`
- `SkeletonLocal.lean`
- `SkeletonSectors.lean`
- `SourceAttachment.lean`
- `SourceJoining.lean`
- `SourceOverlay.lean`
- `Square.lean`
- `SquareCycle.lean`
- `SquareMesh.lean`
- `SquareMeshClosed.lean`
- `SquareMeshConnected.lean`
- `SquareMeshFixed.lean`
- `SquareMover.lean`
- `StageTower.lean`
- `StageTransition.lean`
- `Strip.lean`
- `StripConnected.lean`
- `StripConstants.lean`
- `StripLocal.lean`
- `Subarc.lean`
- `Subdivide.lean`
- `TargetOverlay.lean`
- `Topology.lean`
- `TwoArcs.lean`
- `UniformBound.lean`
- `Windows.lean`


## Extracted square-chain adaptation

`ArcSquareChain.lean` contains the square-chain construction and square-frontier
inclusion proof adapted from Álvaro Begué's `exists_face_of_notMem_arc`,
`Schoenflies/ArcComplement.lean`, commit
`05a43d29cde026618777db3d4e4316204ccca237` of
https://github.com/alonamaloh/schoenflies-lean (Apache-2.0).

These proofs previously appeared in the native
`Topology/PlanarJordan/ArcDiskNeighborhood.lean`; relocation corrects their
provenance classification. The original upstream theorem remains in
`ArcComplement.lean`. Its adaptation extracts the coarse/fine sampling and
nonadjacent-subarc separation into `Schoenflies.exists_square_chain`, uses the
proved `squaresTwoConnected`, and returns strict open-square coverage, arc-valued
centers, and uniform consecutive-pair bounds. The adapted frontier inclusion is
`Schoenflies.frontier_closedSquare_subset_pointSet_chainUnion`.

The new polygonal Jordan neighborhood theorem and its face-cycle/interior
assembly remain in native `Topology/PlanarJordan/ArcDiskNeighborhood.lean` and
consume these external declarations. Existing PL sphere/disk and finite-family
corollaries remain in their native modules. This replaces the former source
attribution in `docs/third_party/PlanarArcNeighborhood.md`.

## 2026-09-27: Lean and Mathlib 4.34.1 compatibility

The owner-authorized compatibility update addresses diagnostics from the
Lean and Mathlib 4.34.1 build without changing mathematical statements,
imports, namespaces, source organization, attribution, or upstream documentation.

- Replaced 235 diagnosed references to deprecated names with their supported
  replacements: `if_pos` with `ite_eq_left`, `if_neg` with `ite_eq_right`,
  `if_true` with `ite_true`, `dif_pos` with `dite_eq_left`, `dif_neg` with
  `dite_eq_right`, and `cond_true` / `cond_false` with
  `Bool.cond_true` / `Bool.cond_false`. Changes are limited to the reported
  source positions in `ArcMonotone.lean`, `Concatenate.lean`, `Endgame.lean`,
  `FiniteTransferTargetMesh.lean`, `GeneratedStructure.lean`,
  `Graph/K33Land.lean`, `InitialPair.lean`, `LimitMap.lean`,
  `LocallyPolygonal.lean`, `MatchedSplit.lean`, `OverlayGraph.lean`,
  `Parity.lean`, `ParitySplitting.lean`, `PolyArcRealize.lean`,
  `PrePolygonArc.lean`, `Realization.lean`, `RealizeSplit.lean`,
  `RealizeSubdiv.lean`, `RefinementStars.lean`, `SimpleArc.lean`,
  `SkeletonLocal.lean`, `SourceAttachment.lean`, `SourceJoining.lean`,
  `SourceOverlay.lean`, `SquareCycle.lean`, `SquareMesh.lean`,
  `SquareMeshClosed.lean`, `SquareMeshConnected.lean`,
  `SquareMeshFixed.lean`, and `SquareMover.lean`.
- In `Jordan.lean`, replaced the diagnosed `rw [inter_comm]; assumption`
  proof step with the compiler-suggested `rwa [inter_comm]` to avoid repeated
  suggestion output. The proof still uses commutativity of intersection and
  the same local hypothesis.

All pre-existing comments, copyright and license text, author headers, and
local provenance notices are preserved verbatim. No linter suppression was
added.

## 2026-09-28: Graph bridge namespace collision under Mathlib 4.34.1

Mathlib 4.34.1 now provides `Graph.IsBridge` for singleton edge cuts. The
vendor cycle layer's independently defined no-cycle predicate therefore could
not be imported after Mathlib's edge-cut module. To preserve both meanings,
the vendor predicate and its methods were renamed from `Graph.IsBridge` to
`Graph.IsCycleBridge`; the cycle proofs, all other graph declarations, and
their statements are unchanged. The compatibility rename preserves the
original copyright and author headers and introduces no linter suppression.
