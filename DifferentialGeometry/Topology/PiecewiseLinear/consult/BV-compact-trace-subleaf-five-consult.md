# BV — consult: sub-leaf 5 of the compact trace (`exists_admissible_operation_of_separating_trace`)

Written by the trace lane (Codex item 15) and revised by the lead on 2026-09-24. For an external
reviewer or a host-side Codex; answer in `consult/BV-compact-trace-subleaf-five-answer.md` (new file;
no git writes; no frozen statement edited; do not disturb working lanes). Chinese or English; the six
checks of `consult/REVIEW-TEMPLATE.md` apply, with the weight on checks 4 and 6. Paths are relative to
`DifferentialGeometry/Topology/PiecewiseLinear/` on `liao9yuan/differential-geometry-dev:moise-integration`
(mirror of `qinz1yang:codex/moise-integration`; observed head `7945025c2`, may advance).

READ-ONLY. If you cannot access the source, separate the mathematics you can check from API claims
you cannot; never guess a theorem name. NOTE FOR A REMOTE REVIEWER: the trace lane's 29 modules are
untracked on the host and NOT on any branch; the two theorems that matter are quoted verbatim in §3
below, and everything else you need is tracked at `7945025c2`.

## 1. Read first, in this order

`Skeleton/FILL_QUEUE.md` "Codex item 15"; `consult/BQ-section34-trace-leaves-codex-answer.md` (the
route review); the frozen `compactTrace_of_noOperation` in `Skeleton/Section34Compact.lean` (line 305,
with its `variable` block); in `Section34CompactVocabulary.lean` the definitions of
`Section34CompactCutFrame` (291), `Section34CompactGraphFrame` (384), `Section34CompactFaceBallInvariants`,
`Section34CompactCompression`, `Section34CompactBigonSlide` (594, quoted in §3), `Section34CompactTrace`
(608). Review ONLY the compact sub-leaf 5, `exists_admissible_operation_of_separating_trace`; do not
re-plan §34, the manifold twin, or sub-leaf 6.

## 2. Goal and hard constraints

Abbreviations (discussion only; no frozen signature changes): `Vw = section34CompactVertexBallImage src f₁ w`,
`∂Vw` its `srcBd` version, `Ee = section34CompactSplitDiskImage src f₁ e`, `γe` its `srcBd` version,
`N = ⋃w Vw`, `Ts = section34CompactFaceTorus V s`, `Θs = frontier Ts`, `Ps = fbl s`, `Σs = fblBd s`.

From `hcut`, `hgraph`, `hinv` and ONE actual trace circle that separates on `Θs`, produce a complete
admissible compression or bigon slide on SOME face label `t` (the operation may live on another
label; `hnc`/`hnb` of the parent leaf exclude every witness on every label). You may first exclude
the compression branch by `hnc` and then construct the bigon, but say how that feeds back into the
parent. No new named input; in particular do not assume a returning arc, an innermost clean disk or
the target operation exists.

BQ's two corrections are binding: a circle with zero image in `H₁` of a SOLID torus need not bound a
disk on its boundary (use pairwise disjoint surjective reference circles); two crossings in the same
direction do not yield a bigon (sub-leaf 6's primitive-degree argument may neither be smuggled in
nor invoked unproved).

Forbidden (P6 circularity): `Section34TraceArcs`, `Section34CompactTraceArcs`,
`Section34CompactTraceHomology`, `Section34TraceTransport`, `CrossingTraceArcNeighborhood`. No
`sorry` from any skeleton. Untracked files of OTHER lanes may not be used (items 13, 17, 18). The
following ARE tracked now and may be used: `TwoBallPocket`, `CircleArcSplit`, `CircleArcCycle`,
`SphereCircleCapSplit`, `PLDiskCapRemoval`, `PLDiskArcGluing`, `PLDiskFamilyGluing`, `BallLocalSide`,
`Section34CompactTetra*`, `Section34CompactResidual*`, `Section34CompactFaceRuns`, the compact
compression modules `Section34CompactCompression*`, and Codex item 14's cut-and-graph bricks
(`Section34CompactDual*`, `GraphDualCell*`, `Section34CompactFaceTorusCycle`, `PLBallImageComplement`,
`FiniteBallUnion`, `Section34CompactDualTetraBuffer`, `Section34CompactExteriorNeighborhoods`).

## 3. Already done — do not re-prove

Sub-leaves 1–4 are closed: finitely many disjoint PL trace circles with both frontier equalities and
a positive count; the surjective trace circle; the corrected "zero homology image ⇒ separating ⇒
bounds a disk on the torus"; and `Section34CompactMeridianSystem.split_disks_form_marked_meridian_system`
(all incident `γe` on distinct fibres of one PL product coordinate, with the actual `Ee` containment,
exact frontier intersections and relative-interior containment).

For sub-leaf 5 the lane holds (untracked, verified, quoted verbatim):

```lean
theorem exists_compact_compression_of_vertex_trace_circle
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    {J : Set E3} (hJ : IsPLSphere 1 J) (hJP : J ⊆ fblBd s)
    (hJV : J ⊆ section34CompactVertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v)) :
    ∃ t : Section34CompactSimplexIndex K 3,
      Section34CompactCompression K K' (section34CompactVertexBallImage srcBd f₁)
        (section34CompactSplitDiskImage src f₁) fbl fblBd t
```
(so `hnc` excludes any trace circle inside a single vertex ball;
`not_circle_subset_vertexBall_of_no_compression`), and

```lean
theorem exists_vertex_return_disk_avoiding_split_disks
    (hinv …) (hcut …) (hgraph …)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (e₀ : Section34CompactEdgeIndex K K') {B : Set E3} {η : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B) (hBP : B ⊆ fblBd s)
    (hBS : B ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e₀)
    (hmeet : B ∩ (⋃ e, section34CompactSplitDiskImage src f₁ e) = {η 0, η 1}) :
    ∃ (R D : Set E3) (q : (Fin 3 → ℝ) → E3) (δ : ℝ → E3),
      IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
      R ⊆ section34CompactSplitDiskImage srcBd f₁ e₀ ∧ B ∩ R = {η 0, η 1} ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = B ∪ R ∧
      D ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
        frontier (⋃ v, section34CompactVertexBallImage src f₁ v) ∧
      D ∩ section34CompactSplitDiskImage src f₁ e₀ = R ∧
      ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
        Disjoint D (section34CompactSplitDiskImage src f₁ e)
```
This settles the foreign-mouth obstruction for a SUPPLIED returning arc; what it does not give is
`∀ t, Disjoint (D \ (B ∪ R)) (Σt)`, the last clause of the target predicate:

```lean
def Section34CompactBigonSlide (K K') (tgtV tgtVBd) (tgtE tgtEBd) (fblBd) (s) : Prop :=
  ∃ (w) (e) (B B' Bb Dj Jd : Set E3),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e', tgtE e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ tgtEBd e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) ∧ Jd = B ∪ B' ∧
      ∀ s', Disjoint (Dj \ Jd) (fblBd s')
```
Other lane modules available: `Section34CompactPuncturedLink`, `Section34CompactPuncturedSphere`,
`SurfaceDiskSeparation`, `LocalDiskSeparation`, `LocalInnermostDisk`, `DiskCrosscutPair`,
`CircleComplementaryArc`, `ArcBoundaryCuts` (compiled). 29 lane modules have zero-diagnostic receipts;
27 (85 declarations) passed the axiom and 13-linter audit; the last two await the joint audit.

## 4. The two questions

A. Extracting a genuine returning arc from a separating trace circle. Can one work inside its torus
filling disk, take the finite intersection arcs with the actual marked meridians and choose an
outermost arc? Give the full argument: why the intersection decomposes into finitely many proper PL
arcs with no closed meridian component inside; how to choose so that the corresponding trace sub-arc
has interior disjoint from ALL splitting disks; why that sub-arc lies on the boundary of ONE actual
vertex ball; and, when there is no meridian intersection, how the case lands exactly in the closed
vertex-circle compression branch. Say whether the separating branch needs sub-leaf 6's
primitive-degree theory at all. "Outermost arc argument" as a phrase is not an answer.

B. Cleaning the existing return disk into a complete admissible bigon. Audit this candidate, do not
assume it: among candidates satisfying the return-disk conclusion, minimise the finite number of
points of the marked boundary arc `R` with all face traces; if the disk interior still meets a face
trace, then a closed trace circle inside is excluded by the vertex-circle compression theorem and
`hnc`; the remaining intersection arcs give a SMALLER returning arc; choose a sub-disk inside the old
disk by `DiskCrosscutPair`, inheriting every splitting-disk avoidance; show the count drops strictly,
ending with an interior disjoint from every `Σt`. Make explicit: the set minimised over, the actual
natural-number measure, the source of finiteness, why the intersection arcs' endpoints lie on `R`,
what happens when an endpoint coincides with an old corner, how a return into the same face or
component is handled, and why the decrease is strict. In particular: is `D' ⊆ D` needed for the
descent, and can re-invoking the return-disk existence theorem pick the other side of the disk (it
must not be claimed smaller without proof)?

## 5. Required form of the answer

1. Verdict: existing inputs suffice / an exact obligation is missing / the candidate route is wrong.
2. Shortest viable proof chain for A and for B, marking which steps existing theorems already cover.
3. Only the truly missing lemmas: exact hypotheses, conclusion, source location, call order — no
   auxiliary-theory expansion.
4. Clause-by-clause check of the final `Section34CompactBigonSlide` witness, especially the endpoint
   intersections with all splitting disks (`B ∩ ⋃ tgtE = Bb`), `Dj ⊆ tgtVBd w ∩ frontier N`, and the
   interior avoidance of all face boundaries.
5. If some step is not derivable from the frame, name the FIRST exact obligation and classify it:
   API not found / proof missing / statement false — a counterexample only in the last case, with the
   original hypotheses it satisfies.

Do not answer with "use an innermost/outermost argument", and do not measure completion by module
counts. We need the argument that closes this sub-leaf, or a blocking point precise enough for an
owner decision.
