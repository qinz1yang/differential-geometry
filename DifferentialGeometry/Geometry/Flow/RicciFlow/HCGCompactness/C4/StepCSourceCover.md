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
