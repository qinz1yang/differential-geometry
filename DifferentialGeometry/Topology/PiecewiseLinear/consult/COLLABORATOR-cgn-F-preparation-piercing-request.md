# Collaborator brief (Lean): Package F — vertex preparation and the piercing package (CGN leaves 2–3)

Written by the lead on 2026-09-23. One conversation per package; say that you take Package F so the
lead does not assign it elsewhere. Same setting and rules as the earlier briefs: repository
`https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration`; branch
from its head; NEW FILES ONLY; restate each frozen leaf byte-identically (its statement and the
`variable` block it uses, `Skeleton/ControlledGraphNeighborhood.lean` lines 255–271); never import a
`Skeleton/` file (read and copy from it); no `sorry`, docstrings or comments in delivered modules;
lines ≤ 100 codepoints; zero warnings; no unused binder; no underscore in a `def`/`abbrev`/`structure`
name; grep the statement shape before proving anything; do not touch `DifferentialGeometry.lean`,
`FREE_INPUTS.md` or any existing file; open a pull request with a ≤ 40-line report and `#print axioms`
for every public theorem. Paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.

Lanes in flight you must not touch (their files are untracked until accepted, so avoid these names):
the CGN edge matching (Codex: `Topology/LocalDegree/*`, `Topology/Manifold/BoundaryNormal*`,
`Topology/Covering/CyclicSections`, `PLBallPair*`), P4 compression (`Section34Compression*`), the §32
tower, the compact P7 residual balls, the C1 tube (`LoopTheorem/BranchCollar*`,
`ClosedBranchTubeCollarArcs`, `MarkedBranchChartPL`), the smoothing lane, Package E (cut frame) and
Package G (removal step) if someone else holds them, and your own §31 / Package D.

Independence: the five leaves of `Skeleton/ControlledGraphNeighborhood.lean` are separate theorems whose
only coupling is the frozen vocabulary of `Section34Frame.lean` (`Section34VertexPreparation` line 931,
`Section34PiercingConditions` line 1016, `Section34CutFrame` line 656). Your two leaves take the cut
frame as a hypothesis and are consumed, as predicates, by the removal step and by the edge matching
(Codex); no proof of theirs is needed. Do the preparation first and deliver it as its own PR: it fixes
the geometry that the package then approximates.

Read first: `consult/BO-cgn-first-four-leaves-codex-answer.md` §2–3 and the sub-leaf table. Its
corrections: the piercing predicate has **22** conjuncts; the skeleton docstring's claim that the tree
lacks the PL-embedding restriction theorem is stale (`IsPLHomeomorphInto.mono_of_isPLCellOn` in
`IsPLHomeomorphIntoMonoOfIsPLCellOn` exists).

## Leaf 2: `exists_section34VertexPreparation` (line 303)

From `hframe`, `hN`, `hQint` (cut-frame outputs) and `hCchart` (each `h '' src (vertexBall w)` lies in
one chart of the PL maximal atlas of `M₂`; the assembly derives it from the carrier control), produce
pierced cells `Cp`/`CpBd`, enlarged chart-local cells `Cc`/`CcBd`, compact cores `Kcore`, the edge ends,
nested tube neighbourhoods `Sn ⊇ Tn`, the marked annuli `Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁`, and a
positive scale `ε` per vertex, satisfying `Section34VertexPreparation …` (read the definition: the cores
cover the whole graph, the certified stability scale from `PLCellOnStability`, non-adjacent source
disjointness, the margins).

Order (BO §2): (1) orient the two ends of every edge; separate whole splitting disks by locally finite
disjoint open neighbourhoods, also when the graph has triangles; localise each WHOLE future lens there,
not only its boundary circle. (2) pierced cells and transverse boundary circles inside those
neighbourhoods; cover each edge by interiors of the pierced balls; compact cores subordinate to that
cover (a detour that loses part of the graph is illegal). (3) compatible nested regular-neighbourhood
tori `Tn ⊆ interior Sn` away from the graph and every core; the six end circles with the side and
component conditions; enlarge to `Cc` inside `U ∩ h⁻¹ (interior Q)` and the chart preimage, locally
finite, containing the incident tubes. (4) stability radius of each core from `PLCellOnStability`;
separation margins for compact disjoint pieces; thickening radius for a lens inside its open
neighbourhood; allocate fractions of each margin so that SUMS satisfy the strict bounds. (5) `ε w` below
this locally finite family and the stability radius, vertexwise over the finite relevant neighbourhood
(there is no common positive minimum over an infinite graph).

Producer mismatches to respect (BO): `DualCellPiercingNeighborhoods` gives finite families whose whole
intersection with each cell is a circle, not the overlapping-ball configuration with `Ab₀` inside the
opposite ball; `DualCellPiercingAnnuli` gives separate boundary bicollars only; the finite
`DualCellPiercingStability` radius preserves only its own clauses;
`InnerSolidTorusToroidalShell.exists_toroidalShell_of_isCompact_subset_interior` gives a topological
torus and shell, not the two PL regular-neighbourhood certificates or prescribed seams;
`Section28Annuli.moise286`, `PrismLateralCircleSides`, `LateralAnnulusLevels` apply after product
coordinates exist and need the constructed core-circle generator. Tools: `DualCellPiercing`,
`LocallyFiniteSeparatingNeighborhoods`, `PLCellOn`, `Section34Frame`.

Sub-leaves: `exists_locally_finite_pierced_cells_with_isolated_lenses` (NEW_THEORY),
`exists_marked_nested_piercing_annuli` (NEW_THEORY), `exists_chart_local_enlargements_and_graph_cores`
(MEDIUM), `exists_vertex_scales_with_sum_margins_and_overlap_isolation` (MEDIUM).

## Leaf 3: `exists_section34PiercingPackage` (line 371)

With `h341 : Moise341` (a named input of the endpoint; never prove it), `hQsub`, `hQlfU` and the
preparation, produce `Sp Tp`, counts `cnt`, circles `Pg`, and PL maps `G'` on the `Cc w` within `ε w` of
`h`, satisfying `Section34PiercingConditions …` (22 conjuncts). Route (BO §3): choose auxiliary
`δ w < ε w` with slack, after establishing stability of tube containment, of the inner and outer annular
sides and of the two outside-`Tp` components; approximate on `Cc` by the chart-local `Moise341` pattern
(`Moise341.exists_section34VertexApproximation`, skeleton line 322, is real and gives PL maps within
`ε w`, but no tube-side conditions); make a relative small PL move in finitely many charts per compact
edge region and assemble by local finiteness (`CurveCrossingGeneralPosition`, `ChartBallGeneralPosition`
are Euclidean ingredients, not this manifold-relative move). Define `Sp = G_a '' Sn`, `Tp = G_a '' Tn`
from the FINAL maps. In each tube the compact intersection is a closed PL 1-manifold; the finite-circle
theorem of `CrossingTraceCircles` applies once the chart/polyhedron hypotheses are proved; reindex by
`Fin (cnt e)` with arbitrary `Pg e i` beyond the count; `0 < cnt e` from the inside/outside separation of
the two ends of `Aa`. Clause division: the exporters `section34MarginConditions` (2, 3, 6, 10, 12–14,
the annular-interior part of 7, the outside part of 8, the disjointness part of 9),
`section34OverlapConditions` (21), `section34MarkerConditions` (22), `locallyFinite_support_of_section34CutFrame`
(5; `Section34Frame.lean` line 719), the definition (4); construct 1, then 11 by
`IsPLHomeomorphInto.mono_of_isPLCellOn` from the preparation's `IsPLCellOn 3 (Cp w) (CpBd w)` and
`Cp w ⊆ Cc w`; construct the rest (the `interior Tp` part of 7, the inside part of 8, the containment
part of 9, the component certificates 15–16, and 17–20).

Sub-leaves: `exists_auxiliary_scales_preserving_piercing_sides` (NEW_THEORY),
`exists_relative_crossing_vertex_approximations` (NEW_THEORY),
`exists_positive_finite_piercing_circle_family` (MEDIUM), `piercing_conditions_of_crossings_and_margins`
(SMALL).

Delivery: real sub-leaf modules, then a module restating each leaf and proving it. Partial delivery is
welcome: a PR with real sub-leaves plus one clearly named `*Probe.lean` file assembling the leaf with
`sorry` only at the named remaining sub-leaves, and a report saying which.
