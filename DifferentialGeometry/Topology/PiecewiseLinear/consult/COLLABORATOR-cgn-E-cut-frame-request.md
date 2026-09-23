# Collaborator brief (Lean): Package E — the Section 34 cut frame (controlled graph neighbourhood, leaf 1)

Written by the lead on 2026-09-23. One conversation per package; say that you take Package E so the
lead does not assign it elsewhere. Same setting and rules as the earlier briefs: repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration`; branch
from its head; NEW FILES ONLY; restate the frozen leaf byte-identically (its statement and the
`variable` block it uses, `Skeleton/ControlledGraphNeighborhood.lean` lines 255–271); never import a
`Skeleton/` file (read and copy from it); no `sorry`, docstrings or comments in delivered modules;
lines ≤ 100 codepoints; zero warnings; no unused binder; no underscore in a `def`/`abbrev`/`structure`
name; grep the statement shape before proving anything (the branch has ~1900 PL modules); do not touch
`DifferentialGeometry.lean`, `FREE_INPUTS.md` or any existing file; open a pull request with a ≤ 40-line
report and `#print axioms` for every public theorem. Paths are relative to
`DifferentialGeometry/Topology/PiecewiseLinear/`.

Lanes in flight you must not touch (their files are untracked until accepted, so avoid these names):
the CGN edge matching (Codex: `Topology/LocalDegree/*`, `Topology/Manifold/BoundaryNormal*`,
`Topology/Covering/CyclicSections`, `PLBallPair*`), P4 compression (`Section34Compression*`), the §32
tower, the compact P7 residual balls, the C1 tube (`LoopTheorem/BranchCollar*`,
`ClosedBranchTubeCollarArcs`, `MarkedBranchChartPL`), the smoothing lane, and your own §31 / Package D.

Independence: the five leaves of `Skeleton/ControlledGraphNeighborhood.lean` are separate theorems whose
only coupling is the frozen vocabulary of `Section34Frame.lean`. The assembly
`controlledGraphNeighborhood` (line 591) chains them: cut frame → vertex preparation → piercing package
→ protected circle removal → deleted balls → edge matching. The edge matching (Codex) takes
`Section34CutFrame`, `Section34VertexPreparation`, `Section34PiercingConditions` and
`Section34OuterTorus` as hypotheses, never a proof of yours.

Read first: `consult/BO-cgn-first-four-leaves-codex-answer.md` §1 and the sub-leaf table (route review of
2026-09-23). Its corrections: the live cut frame has **25** top-level conjuncts; parts of the skeleton's
module docstring (a seven-leaf count, some OPEN descriptions) predate the deleted-ball proof and are stale.

## The leaf: `exists_section34CutFrame` (line 273)

Inputs: open `U`, the topological embedding `hh : IsEmbedding (U.domRestrict h)` into the PL 3-manifold
`M₂`, the locally finite combinatorial 3-manifold `𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U` realised in an
arbitrary finite-dimensional `Ea` (never the chart model), the carrier control
`hH : Section34CarrierControl U 𝒦 h η H` (`Section34Frame.lean` line 632), an open `W ⊇ graphSkeletonSpace 𝒦`
inside `U`, and a positive continuous `ψ` on `U`. Outputs, in ONE existential: the subdivision `𝒦'`, the
cut cells `src`/`srcBd`, carriers `car`, target balls `Q`, charts `ct`, discs `Sd`, with
`Section34CutFrame U 𝒦 𝒦' src srcBd` (line 656), the locally finite regular neighbourhood
`IsLocallyFiniteRegularNeighborhoodOf (section34CutNeighborhood src) (graphSkeletonSpace 𝒦) U`,
`N ⊆ W`, carriers in the complex with finite fibres, `h '' src (vertexBall w) ⊆ interior (Q w)`,
`Q w ⊆ H (car w)` with `ψ`-small diameter, the two incidence clauses of `Q` against simplex bodies, and
`Section34OuterTorus 𝒦 𝒦' h Q ct Sd` (line 908: one outer solid torus per triangle rim, with spine, buffer,
and no PL 2-cell bounded by `h '' rim` inside the incident `Q`s).

Supply map (BO §1; clause numbers in source order of `Section34CutFrame`):
1. 1–3: `SubdivisionSubordinateToCover.exists_isSubdivision_section34CarrierSupport_subset` gives the
   subdivision, the unchanged realisation map and combinatoriality for a chosen open cover; it does not
   give the later assignments.
2. 4: `DualCellDecomposition`, `LocallyFiniteSplittingDisks` (dual balls / splitting disks);
   `isTube_graphDualCell` (`TubeOfGraphDualCells`) is a finite model, not a locally finite producer.
3. 5–7, 10–25: construct the face and tetrahedral complements, their boundaries and intersections
   together; the closure formulas you need are not extra fields of the frame.
4. 8–9: transfer local finiteness from finite stars of the realisation to neighbourhoods at every point
   of `U`; prove the cut covers `U` (local finiteness on a union of selected balls is insufficient).
5. `hN`: a coherent increasing exhaustion with finite combinatorial ambient pieces, compatible graph
   restrictions, nesting, and exact realised union and core, as `PolyhedralGraph` specifies;
   `PLPiece.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood` uses a constant finite exhaustion;
   a deformation retraction alone is weaker. Tools: `LocallyFinitePieceTowerExistence`,
   `DerivedNeighborhoodCells`, `DerivedNeighborhoodRestriction`.
6. Outer torus: build a small SOURCE torus around each rim in its local PL model and transport it through
   `h` and `ct`; do NOT apply `IsPLSphere.exists_solid_torus_neighborhood` (`CircleSolidTorus`) to
   `ct '' h '' rim`, since `h` is only topological. Choose `Q` inside all buffers by finite incidence and
   positive local margins; prove the no-disk clause from the spine obstruction.
   `exists_chart_iUnion_carrier_subset_source` gives a common chart only after `Q ⊆ H` is arranged.

Named sub-leaves (BO; SMALL = bookkeeping, MEDIUM = bounded geometric lemma, NEW_THEORY = producer absent
from the tree): `exists_subdivision_with_finite_carrier_assignment` (MEDIUM;
`SubdivisionSubordinateToCover`, `Section34CarrierSupportLocallyFinite`),
`exists_locally_finite_graph_cut_cells` (NEW_THEORY; joint eight-label cells, closures, boundaries,
incidence and the two-sided local model; `DualCellDecomposition`, `DerivedNeighborhoodCells`,
`PLCellOnBoundary`), `exists_graph_cut_derived_neighborhood_exhaustion` (NEW_THEORY; `PolyhedralGraph`,
`LocallyFinitePieceTowerExistence`), `exists_outer_tori_with_fine_carriers` (NEW_THEORY;
`CircleSolidTorus`, `SolidTorusOpenNeighborhood`, `Section34Frame`).

Compact twin, for reuse of ideas (grep, do not duplicate): the compact cut frame is leaf 1 of
`Skeleton/Section34Compact.lean` (`exists_compactCutAndGraph`). Six real bricks of that lane —
`Section34CompactLinkCondition`, `Section34CompactGraphApproximation`, `Section34CompactResidualCells`,
`Section34CompactCarriers`, `Section34CompactCellSeparation`, `Section33TubeApproximation` — and the
review `consult/BT-compact-cut-graph-clauses-nine-eleven-answer.md` (zero-marked rim core buffer,
tetrahedron exterior buffer, the flag APIs for the cell descriptions) show the finite version of the
cell descriptions and of the outer-torus marking; the locally finite version is yours. Also real:
`Section34SourceFaceOrder` (the source face order from the cut frame) and
`locallyFinite_support_of_section34CutFrame` (`Section34Frame.lean` line 719).

Delivery: the sub-leaves as real modules, then a module restating the leaf and proving it. Partial
delivery is welcome: a PR with the real sub-leaves plus one clearly named `*Probe.lean` file that
assembles the leaf with `sorry` only at the named remaining sub-leaves, and a report saying which.
