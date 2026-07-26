# StepCSourceCover.lean — finite live-source patch cover

## 2026-07-13 verified producer

`MetricCompactnessInputs.exists_live_source_cover` is proved and focused-green.
After the single common `existsLiveMetric0` refinement it defines, for every old
`LiveSlot L inp.pack r`, an open strict ellipsoid in that slot's fixed Euclidean
normal coordinates.  Eventually each patch lies in its eight-lambda model ball,
its exponential image lies in the source slot's hat and in the union of strict
inner balls, and the finitely many patch images cover the frozen source ball.

The proof uses the common limiting origin metric, a uniform quadratic-error
bound over the finite live-slot family, the scaled source-center cover, the
Item-3 scale tail, and proper normal coordinates.  No endpoint radius field was
added.  The theorem keeps the original `LiveSlot L` index and returns the one
subsequence on which all source-patch clauses hold.

This producer intentionally does not assert transition overlap for every live
target.  Such a statement is false for stable-disjoint targets.  Pairwise H6
clauses remain indexed by the old `InterSlot L inp.pack r alpha` and must be
obtained from `pair_overlap_tail` inside the fused sparse producer.  Likewise,
the patches are a finite cover; their chartwise weights are not glued or equated
on overlaps.

The source-cover producer itself is complete (100%).  The fused
`exists_atom_supp_fin` / `exists_supp_pts_fin` producer is still unstated (0%)
at this checkpoint.  Sparse active-support machinery is about 95%,
pair-to-capstone integration about 82%, dedicated Step-B/B1 machinery about
84%, Chapter 4 machinery about 80%, and whole-HCG machinery about 53%.
`StepB1RawInput`, the textbook B1 theorem, and all compactness endpoint theorems
remain theorem-level 0%.

## 2026-07-15 compactly nested coordinate cores

The stronger sibling `MetricCompactnessInputs.exists_live_cores` is now
focused-green.  On the same origin-metric subsequence it returns fixed compact
quadratic sublevels `C0 alpha` and `C1 alpha` with

```text
C0 alpha ⊆ interior (C1 alpha) ⊆ C1 alpha ⊆ U alpha,
```

and the frozen source ball is covered by exponential images of
`interior (C0 alpha)`.  The proof uses the existing strict margin

```text
243/40 < 49/8 < 99/16 < 25/4
```

between the scaled-cover estimate and the old patch threshold.  No new input,
radius assumption, or subsequence was introduced.  The old
`exists_live_source_cover` statement is preserved as a projection.

This closes the fixed nested-coordinate-core producer (100%).  It does not
give a common moving-stage implicit-center domain.  Rounded project accounting
therefore stays at about 94% for dedicated Step-B/B1 machinery, 86% for Chapter
4 machinery, and 57% for whole-HCG machinery; `StepB1RawInput`, textbook B1,
and all compactness endpoints remain theorem-level 0%.

## 2026-07-16 buffered convex inner cores

`MetricCompactnessInputs.exists_live_cores` now retains the two additional
shape facts needed by the moving-stage return argument: every `C0 alpha` is
convex and contains the origin.  Symmetry of the limiting origin metric is
proved once by passing the finite-stage metric symmetry through the existing
`MapCInfConvOnCompacts` limit.

The same producer also returns a positive radius `eta alpha` for every live
source slot.  Every source-ball point at every retained stage has a normal
coordinate representative `z` in the strict `243/40` deep core, with

```text
Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha).
```

The radius comes from compact thickening of that fixed deep core inside the
open inner core.  Thus it is uniform in the moving stage and adds no endpoint
radius assumption or new compactness input.  The old unbuffered source-cover
theorem remains a projection.  Focused verification and the exact producer
refresh passed.

This closes the buffered finite-source-cover producer (100%).  It supplies
geometry for the return-map injectivity lane but not the return estimate or the
global B1 map itself.  Current rounded accounting remains about 98% for
dedicated Step-B/B1 machinery, 90% for Chapter 4 machinery, and 60% for whole
HCG machinery; `StepB1RawInput`, textbook B1, and all compactness endpoints
remain theorem-level 0%.

## 2026-07-18 framed source-cover migration

Both public cover producers now state their patch maps with
`framedExpDiffeo`, and their radial model-ball clause is the intrinsic
`expRadiusGp` clause supplied by the migrated Item-3 profile. The local proof
uses `normalMetric_zero = innerSL`, so the stage-zero quadratic form is exactly
`‖v‖²`. For the reverse cover witness, the raw Gauss-lemma vector is converted
once through `normalFrame.symm`; the theorem exposes only the framed model
coordinate and framed exponential image.

`exists_live_cores` and its `exists_live_source_cover` projection both pass
focused verification under the canonical framed imports. The only issues met
during migration were local elaboration shapes for `innerSL`, the intentionally
disabled tangent-space norm instance, and framed-source preimage unfolding;
none was a missing geometric API or a new assumption.

The framed finite-source-cover sub-brick is complete (100%). The live framed
`MetricCompactBase.exists_b1_raw` producer and the textbook Step B1 theorem
remain theorem-level 0% until the remaining downstream chain is migrated and
revalidated; whole-HCG support machinery remains about 60%.
