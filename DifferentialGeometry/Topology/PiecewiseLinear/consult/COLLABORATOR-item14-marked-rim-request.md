# Collaborator brief (Lean): finish the compact cut-and-graph leaf — the zero-marked rim core buffer

Written by the lead on 2026-09-24 (takeover of Codex item 14). One conversation for this package; say
that you take it. Same setting and rules as your earlier briefs: repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration` (branch from
its current head, 4375f6dcf or later; the partial results below are already on it); NEW FILES ONLY;
restate the frozen leaf byte-identically (statement and `variable` block); never import a `Skeleton/`
file; no `sorry`, docstrings or comments in delivered modules; lines ≤ 100 codepoints; zero warnings
(silence an unused frozen binder only in the proof body with `let _ := …`); no unused binder of your own;
no underscore in a `def`/`abbrev`/`structure` name; grep every new name and every statement shape;
compile with the lead's flags `-DautoImplicit=false -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true -Dlinter.style.header=true -Dlinter.style.longLine=true`; finish
with an audit (axioms within propext / Classical.choice / Quot.sound, the thirteen environment linters;
split it by module group if it hits the heartbeat limit); do not touch `DifferentialGeometry.lean` or
`FREE_INPUTS.md`; PR against `codex/moise-integration` with a ≤ 40-line report. Paths are relative to
`DifferentialGeometry/Topology/PiecewiseLinear/`.

## Target

`exists_compactCutAndGraph` in `Skeleton/Section34Compact.lean` (line 294): from `h331 : Moise331OnTube`,
`hC : IsPLBall 3 C`, `hV : IsOpen V`, `hCV`, `hh : IsEmbedding (V.domRestrict h)` and `ε > 0`, produce
the subdivision, the cut and the PL approximation `f₁` with `Section34CompactCutFrame` (29 clauses) and
`Section34CompactGraphFrame` (11 clauses) (`Section34CompactVocabulary.lean` lines 291 and 384).
Apply `h331` ONCE, after every neighbourhood constraint has been chosen.

## What is already real (do not re-prove)

- The complete compact cut frame with `K' = K` (`Section34CompactDualCutFrame.lean`, 51 modules),
  graph clause 11 (`PLBallImageComplement`, `FiniteBallUnion`, `Section34CompactDualTetraBuffer`,
  `Section34CompactExteriorNeighborhoods`), the solid-torus recognition of the actual cyclic vertex-cell
  union (`Section34CompactFaceTorusCycle`), the six lease-b bricks of Batch 8
  (`Section34CompactLinkCondition`, `…GraphApproximation`, `…ResidualCells`, `…Carriers`,
  `…CellSeparation`, `Section33TubeApproximation`).
- The marked bridge disk route, steps A0, L0, L1 of the BU answer: `Section34CompactTriangleDisk`,
  `GraphDualCellSurfaceTrace`, `GraphDualCellCurveTrace`, `BridgeDisk`, `GraphDualCellBridgeDisk`,
  `BridgeDiskArc` (commit 5a05246e4), plus the two accepted refutations `TubeEdgePairOverlap`
  (edge-pair cylinders overlap in three dimensions) and `GraphDualCellRadialBoundary` (a dual vertex
  cell is not a cone from its vertex).
- The only missing piece of the whole leaf is the zero-marked rim core buffer and the assembly.

## Read first, in this order

1. `consult/Item14MarkedRimHandoff.md` (the previous lane's exact frontier at L2, what each new
   module exports, and the private-check receipts).
2. `consult/BU-marked-rim-core-buffer-answer.md` in full: it refutes three routes with fixtures and
   fixes the route (C) — face bridge disk → marked SINGLE-vertex prism → cyclic gluing of single vertex
   prisms (never doubled edge prisms) → centre-preserving untwisting → outward collar of the whole
   union — with signatures for A0, L0–L6 and the assembled `exists_compactRimCoreBuffer`. Note its
   correction: `section34CompactGraphSkeleton K` is the 1-skeleton of `K` itself.
3. `consult/BT-compact-cut-graph-clauses-nine-eleven-answer.md` (graph clauses 9 and 11),
   `Skeleton/OPUS_FILL_LOG_B.md` Batch 8, `Skeleton/FILL_LOG.md` "# Codex item 14" (the latest
   entries), `Section34CompactVocabulary.lean` (`IsSpine` is in `MoiseChain.lean` line 254).

## The work, in order

- L2 (NEW_THEORY), `bu_markedPrism_of_bridge`: from a PL 3-ball `C`, two disjoint boundary cap disks
  with coordinates `r0`, `r1`, and `IsBridgeDisk C A B (r0 (stdCenter 1)) (r1 (stdCenter 1))`, a PL
  prism parametrisation `ρ` of the WHOLE of `C` matching both cap sets and centres, with
  `ρ '' ({stdCenter 1} ×ˢ Icc (0:ℝ) 1) = A` (relative ambient straightening of the marked proper arc).
  The previous lane stopped here; there is no counterexample and no known insufficiency of the leaf's
  hypotheses — this is a genuine new module, not a lookup. The marked proper arc and its exact frontier
  endpoints are already proved (`BridgeDiskArc`).
- L3 (MEDIUM), `bu_cylindricalDiagram_of_marked_cycle`: glue the SINGLE vertex prisms along the
  splitting disks with the end-disk coordinates fixed in advance (`Section34CompactFaceTorusCycle`
  gives the cycle structure: consecutive cells meet exactly in a splitting disk, non-consecutive cells
  are disjoint, no triple intersections).
- L4 (NEW_THEORY), `bu_untwist_preserving_axis`: centre-preserving untwisting of the closed-up cylinder
  (`CylinderEndMap.exists_isPLHomeomorphOn_endMap`, `IsCylindricalDiagram.isCombinatorialSolidTorus`,
  `CylindricalMonodromy` are the tools the answer names).
- L5 (SMALL): the existing quotient theorem retains coordinates
  (`CylindricalProduct.exists_homeomorph_prod_circle_of_eq_ends`, second conclusion).
- L6 (MEDIUM), `bu_thickening_fixed_on_compact`: outward collar of the ENTIRE prescribed torus so the
  buffer contains the vertex cells with their arms; then the assembled `exists_compactRimCoreBuffer`.
- Then, in the leaf: choose the rim buffers `P_s` and the tetrahedron exterior buffers before `f₁`,
  intersect the prescribed `W v` with their images, apply `Moise331OnTube` once, recognise each target
  cyclic union and shrink inside the SAME marked product (clause 9: `S₁ ⊆ interior T_s`,
  `T_s ⊆ interior S₂`, the toroidal shell, `IsSpine S₁ (h '' rim)`), transport the buffered-ball
  bicollars for clause 11 (already real), verify the remaining clauses, restate and close the leaf.

Check every BU signature against the actual definitions before proving it; if one is wrong for the
real `graphDualCell`, say exactly how and adjust the statement (not the leaf). Do not substitute an
unmarked prism, do not add a named input, do not stop because a direct API is missing — L2 and L4 are
assigned as new theory. Deliver L2 as its own PR first if you like (real modules with receipts), then
the rest.
