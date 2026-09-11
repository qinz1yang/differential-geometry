# Local modifications

Upstream: <https://github.com/alonamaloh/schoenflies-lean>, commit
`05a43d29cde026618777db3d4e4316204ccca237`.

## 2026-09-11: initial port

- Selected the 128 source modules required by `JordanSchoenflies.lean`.
- Rewrote each internal `import Schoenflies.*` to
  `import DifferentialGeometry.External.Schoenflies.*`.
- Preserved the declaration namespaces, original copyright notices,
  documentation, license, README, and formalization metadata.
- Use the enclosing project's existing Lean/Mathlib 4.33.1 configuration.

Compatibility repairs are listed below. See `PORTING.md` for verification.

In `Plane.lean`, removed the redundant simp attribute from `det_perp_perp`:
`det_perp_right` already simplifies its left-hand side. The equality is retained.

In `RefinementStars.lean`, explicitly bound the refined decomposition domain
`D' : Set Plane` in the refinement namespace, preserving the inferred input.

In `Strip.lean`, explicitly bound the real coordinates `t'` and `s'` in
`ClosedPolygon.off_injective`, preserving upstream's inferred parameters.

In `Polygonal.lean`, explicitly bound the arbitrary parameter set `I` in
`injOn_lineMap`, which upstream's `autoImplicit` inferred. Removed the
redundant simp attribute from `poly_pair`: the general list recursion already
simplifies its left-hand side. The useful equality remains available explicitly.

In `Subarc.lean`, made the affine reparametrization and unit interval explicit
before transporting the segment-image equality. This resolves a Lean 4.33.1
elaboration mismatch without changing the statement or mathematical argument.

## Lean 4.33.1 set membership API

Replaced the deprecated `Set.mem_setOf_eq` by `Set.mem_ofPred_eq`.
The affected statements and arguments are unchanged.

Files: `SquareMeshFixed.lean`, `SquareMeshConnected.lean`, `OverlayGraph.lean`, `PolyLocal.lean`, `SourceOverlay.lean`, `SkeletonAccess.lean`, `SkeletonSectors.lean`, `QuantitativeForwardStages.lean`, `Strip.lean`, `ModelCurve.lean`, `SquareMover.lean`, `GridAttach.lean`, `SkeletonLocal.lean`, `Square.lean`, `Direction.lean`, `LocallyPolygonal.lean`, `OuterChain.lean`, `GeneratedStructure.lean`, `SourceAttachment.lean`, `ArcComplementPrep.lean`, `Bounded.lean`, `ArcCollars.lean`, `CommonSubdivision.lean`, `ArcComplement.lean`, `StripLocal.lean`, `SimpleArc.lean`, `BoundaryCycles.lean`, `SquareMesh.lean`, `InitialPairFixed.lean`, `Graph/Tree.lean`, `Graph/Degree.lean`, `Graph/PathGraph.lean`, `Graph/OuterFace.lean`.

Replaced deprecated `Graph.edgeSet_eq_setOf_exists_isLink` by `Graph.edgeSet_eq_setOfPred_exists_isLink` in `BoundaryAnchors.lean`, `CommonSubdivision.lean`, `Graph/PathGraph.lean`.

Added a local-modification notice to each vendored Lean file, preserving the original copyright and author lines.

Updated deprecated `ContinuousOn.restrict` to `domRestrict`; replaced `haveI` by `have` for proposition-valued local instances, as required by the current style linter. Files: `BoundaryContinuity2.lean`, `FiniteTransfer.lean`, `SkeletonSectors.lean`, `FaceCyclesProof.lean`, `ModelCurve.lean`, `SquareMover.lean`, `Realization.lean`, `OuterChain.lean`, `ArcComplement.lean`, `Inversion.lean`, `FiniteTransferTarget.lean`, `Graph/Tree.lean`.

In `Graph/Component.lean`, removed the redundant simp attribute from `mem_vertexSet_induce_component`; `Graph.vertexSet_induce` already normalizes its left side. The theorem is retained.

In `Graph/Tree.lean`, removed the unnecessary `[G.Finite]` assumption from both longest-path endpoint leaf theorems. Their supplied longest-path hypothesis suffices; finiteness is still used to establish existence of a longest path.

In `FaceCycles.lean`, removed the ineffective simp attribute from `IsCycleThrough.cycleGraph_vertexSet`: its endpoint parameter cannot be inferred from the rewrite target. The explicit theorem remains available.

Replaced deprecated `Set.setOf_and` by `Set.ofPred_and` in `Accessible.lean`.

Removed the extra blank line at EOF in `JordanSeparates.lean` to satisfy `git diff --check`.

Updated deprecated set domain restriction names to `Set.domRestrict`, `Set.domRestrict_apply`, and `Set.range_domRestrict` in `Endgame.lean`, `SkeletonSectors.lean`, `InitialPair.lean`.

In `SkeletonSectors.lean`, removed unnecessary `[G.Finite]` assumptions from `IsDrawing.edge_radial_unique` and `IsDrawing.not_three_localDirs_on_edge`. These facts concern individual embedded edges.

In `Graph/Relabel.lean`, explicitly bound the edge, vertices, and edge-list variables inferred by upstream autoImplicit. Their types and mathematical roles are unchanged.

In `FiniteTransfer.lean`, explicitly bound the input type of `exists_injective_pinned_avoiding`; removed unused infinity instances from the `EarStep` and `EarStepConstruction` predicates (construction theorems retain needed infinity); used `have` for proposition-valued local instances.

The three `FiniteTransfer` assembly theorems that accept a completed ear step also no longer require infinity. Replaced the local `letI` in the fresh-name proof by `let` as required by the current proof-context linter.

Applied the same predicate/assembly generalization to the five reverse-ear predicates and `targetEarStep_of_data`/`targetTransferOfEars` in `FiniteTransferTarget.lean`; construction results retain infinity. Updated local `letI` declarations to `let` in proof contexts.

Updated deprecated `continuousOn_iff_continuous_restrict` to `continuousOn_iff_continuous_domRestrict` in Endgame.lean, InitialPair.lean.

- `CommonSubdivision.lean`: use proof-local `let` instances and the current
  `Set.ofPred_eq_eq_singleton` name under Lean/Mathlib 4.33.1.

Use `have` for proposition-valued local instances in `SourceJoining.lean`, `BoundaryAnchors.lean`, `TargetOverlay.lean`, `QuantitativeRecursion.lean`, `FreshDenseSelection.lean`.

Three further reverse-ear implications need no infinity instance:
`targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo`,
`targetEarFreshInvariant_of_newBoundaryAnchored`, and
`targetEarEndpointAccessibility_of_freshInvariant`. Removed that unused input.

The corresponding combinatorial corollaries also no longer require infinity: `targetEarFreshCombinatorics_of_nonouterIncidenceUnique_of_outerIncidenceAtMostTwo`, `targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle`, `targetEarFreshCombinatorics_of_nonouterIncidenceUnique_of_outerCycle`, `targetEarFreshInvariant_of_boundaryAnchored`.

`FreshDenseSelection.lean`: explicitly bound the cell-name type `γ`, previously
inferred by upstream autoImplicit, for the generated-pair section.

`SourceAttachment.lean`: qualify the existing Schoenflies graph namespace
opening to avoid ambiguity with the root Graph namespace. Name resolution is preserved.

Apply the same explicit graph namespace opening in `SourceJoining.lean` and
`OverlayExtension.lean`, which import that same nested namespace.

Removed one trailing space in `SkeletonSectors.lean`; no proof or statement changes.
