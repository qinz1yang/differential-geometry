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

Compatibility repairs and final verification are pending.

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
