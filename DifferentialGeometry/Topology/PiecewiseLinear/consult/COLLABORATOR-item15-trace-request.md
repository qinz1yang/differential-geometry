# Collaborator brief (Lean): finish the two Section 34 trace leaves (takeover of Codex item 15)

Written by the lead on 2026-09-24. One conversation for this package; say that you take it. Same
setting and rules as your earlier briefs and the item-14 brief
(`consult/COLLABORATOR-item14-marked-rim-request.md`): repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration` (branch from
its current head, c72fe420c or later; the partial results are already on it); NEW FILES ONLY; restate
each frozen leaf byte-identically (statement and `variable` block); never import a `Skeleton/` file;
no `sorry`, docstrings or comments; lines ≤ 100 codepoints; zero warnings with the lead's flags; no
named input added; do not touch `DifferentialGeometry.lean` or `FREE_INPUTS.md`; PR against
`codex/moise-integration` with a ≤ 40-line report, receipts and the audit line. Paths are relative to
`DifferentialGeometry/Topology/PiecewiseLinear/`.

## Targets

1. `compactTrace_of_noOperation` (`Skeleton/Section34Compact.lean`): from the compact cut frame, graph
   frame and face-ball invariants and `hnc`/`hnb` (no face admits a compression, none a bigon slide —
   every witness on every label is excluded), produce `Section34CompactTrace …`
   (`Section34CompactVocabulary.lean` line 608: per face a positive finite disjoint family of PL
   circles whose union is `∂P ∩ ∂N` and `∂P ∩ Θ`, each meeting every incident edge trace in exactly one
   point, with the nonzero-homology certificates on the face torus).
2. `section34Trace_of_noOperation` (`Skeleton/Section34Normalization.lean`): the manifold twin with
   `hU`, `hh`, `Section34CutFrame`, `Section34GraphFrame`, `Section34FaceBallInvariants` and
   `Section34Trace` (`Section34Frame.lean` line 791). Do the compact leaf first and deliver it as its
   own PR.

## Read first, in this order

1. `consult/BV-compact-trace-partial-handoff.md` in full (the previous lane's state, receipts, exact
   frontier at sub-leaf 6, and the verification commands it used).
2. `consult/BQ-section34-trace-leaves-codex-answer.md` (the route; its two corrections are binding: a
   circle with zero image in `H₁` of a SOLID torus need not bound a disk on its boundary — compare with
   the disjoint surjective member; two crossings in the same direction do not give a bigon —
   primitive degree first).
3. `consult/BV-compact-trace-subleaf-five-answer.md` (sub-leaf 5: the finite minimisation for the
   returning arc and the side-selected nested-disk descent; now implemented).
4. `Skeleton/FILL_QUEUE.md` "Codex item 15" and the "# Codex item 15" entries of `Skeleton/FILL_LOG.md`.

## What is already real (commit 4375f6dcf and earlier; do not re-prove)

46 lane modules with clean receipts: sub-leaves 1–5 of the compact trace — the finite disjoint PL
trace circles with both frontier equalities and positive count, the surjective circle, the corrected
"zero homology image ⇒ separating ⇒ boundary disk", the marked meridian system
(`Section34CompactMeridianSystem`), the vertex-circle compression
(`Section34CompactVertexOperations`), the return disk avoiding the splitting disks
(`Section34CompactReturnDisks`), both BV bridges (`exists_compact_vertex_return_arc_of_torus_disk`,
`exists_compact_trace_crosscut_in_return_disk`), the old-corner exclusion, the prescribed-side
nested-disk descent and the separating-operation dichotomy. A 38-module audit passed earlier; the
expanded 46-module audit has not been run — run it first (split by module group if it hits the
heartbeat limit) and report it.

Corrections to the handoff's tool list: `CircleArcSplit`, `CircleArcCycle`, `TwoBallPocket`,
`SphereCircleCapSplit`, the `Section34CompactTetra*`/`Section34CompactResidual*` modules, the compact
compression modules and Codex item 14's cut-and-graph bricks are all TRACKED on the branch now and may
be used freely; the only forbidden modules are the P6 ones (`Section34TraceArcs`,
`Section34CompactTraceArcs`, `Section34CompactTraceHomology`, `Section34TraceTransport`,
`CrossingTraceArcNeighborhood`), which assume the single-crossing conclusion.

## The work, in order

- Sub-leaf 6, `exists_admissible_bigon_of_excess_meridian_crossings`: every nonseparating trace circle
  is surjective by comparison with the disjoint surjective member; establish the primitive
  longitudinal degree ±1 FIRST (`TorusCircleHomology`, `TorusSubsurfaceCarrier`, `FirstHomologyCarrying`,
  `CoveringLift`), then extract the annulus / cyclic-cover bigon from two excess crossings with the same
  meridian, innermost-localise it and produce the full `Section34CompactBigonSlide` witness (the
  predicate's twelve conjuncts; the descent of the BV answer applies to the resulting return disk).
- The compact headline: apply `hnc`/`hnb` to the two dichotomies, get degree-one single crossings,
  nonzero component homology and the positive count; restate and close `compactTrace_of_noOperation`.
- The manifold twin: the leaf provides no target chart, so build the intrinsic finite PL face-torus
  model by cyclic gluing (`Section34FaceTorusCycle`, `CyclicBallUnion`, `Section34IncidentEdges`),
  transport the compact disk/bigon theorems through it, replace "unbounded component" by the
  carrier-frontier escape, and prove the exact degree and reindexing clauses
  (`section34_trace_of_intrinsic_operation_dichotomies`). No added `hctrl` or any other hypothesis:
  if a clause truly needs one, stop and report the exact clause with the counterexample checked
  against every Lean hypothesis.
