# BO — first four controlled graph-neighborhood leaves

Source review, 2026-09-23, `D:/differential-geometry-moise-int`, branch
`codex/moise-integration`, HEAD `c45b6faf19e693ae1134ba6f2656e71fbd0859d5`.
Paths below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
No Lean proof or probe was compiled; no axiom-closure certification is claimed.

Two corrections to the description matter. The live cut frame has **25** top-level
conjuncts; the piercing predicate has **22**. The removal step requires
`cnt' e₀ < cnt e₀`, not a decrease of exactly one. The docstring's seven-leaf count
and some OPEN descriptions predate the imported deleted-ball proof and removal
assembly; there are five physical `sorry`s. The answer below proposes routes,
not changes to frozen statements or a ruling on BN.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_section34CutFrame` | OK, provisional | Subdivision and local pieces exist; the joint locally finite cut and regular-neighborhood exhaustion remain substantial producers. |
| `exists_section34VertexPreparation` | OK, provisional | The repaired chart input is supplied; simultaneous pierced geometry, whole-lens isolation and certified scales remain open. |
| `exists_section34PiercingPackage` | OK, provisional | It can choose finer auxiliary scales using `Moise341`; ordinary metric margins alone do not supply crossing and component data. |
| `exists_section34ProtectedCircleRemovalStep` | OK, provisional | Strict descent is the correct strength; a map-level disk/band surgery preserving fixed tube images is still needed. |

Here OK means no complete counterexample was found, **not** proved or a certified
joint fixture. In particular, failure to construct a fixture is not evidence of
VACUOUS. The missing fixture certificates are stated below.

## 1. The cut, including its outer tori

Mathematically this chooses a fine triangulation and a regular closed-cell cut of
the manifold around the original graph, with small target carriers and one outer
solid torus around each original triangle rim. All choices belong to one
existential: choosing arbitrary carriers first can fill the rim and destroy the
spine/no-disk requirement.

Hypotheses come from the controlled-neighborhood consumer: `hU`, the embedding,
the original combinatorial triangulation, carrier control, `W`, and positive
continuous `ψ`. No `Moise341` is needed for this leaf. Empty `W` is excluded for
a nonempty graph. Small `ψ` forces locally varying refinement, not one global
mesh bound. The ambient `Ea` must remain arbitrary; it is not a global chart of
the manifold.

Number the conjuncts of `Section34CutFrame` in source order. The supply map is:

| Clauses | Supply and exact remaining work |
|---|---|
| 1–3 | `SubdivisionSubordinateToCover.exists_isSubdivision_section34CarrierSupport_subset` supplies subdivision, unchanged realization map and combinatoriality for a chosen open cover. It does not itself supply the later assignment `car` with finite fibers. |
| 4 | `DualCellDecomposition` and `LocallyFiniteSplittingDisks` supply dual-ball/splitting-disk mathematics. The finite `isTube_graphDualCell` is a model, not a locally finite manifold producer. Complementary tetrahedral balls, face disks and all lower cut strata need joint recognition and transport to `IsPLCellOn`. |
| 5–7, 10–17, 18–25 | Construct the actual face/tetrahedral complements and their boundaries and intersections together. The closure formulas used in this construction are not extra fields already present in the frozen frame. Prove the eight label types, dimension exclusion, prescribed meets, foreign-incidence exclusions and coverage from this construction. |
| 8–9 | Transfer local finiteness from finite stars of the locally finite realization to neighborhoods in `M₁` at every point of `U`; prove the cut covers `U`. Local finiteness only on a union of selected balls is insufficient. |

`TubeOfGraphDualCells.exists_isTube` and `HandleDecompositionTubeFixture` are genuine
finite examples. `Section33TubeFrame` constructs a finite graph tube in `E3`, with
an embedding and an error scale. `PolyhedralTubeNeighborhoodExists` **requires**
an already supplied handle decomposition. None produces this cut or its `hN`.
`PLPiece.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood` uses a constant
finite exhaustion. The present `hN` needs a coherent increasing exhaustion with
finite combinatorial ambient pieces, compatible graph restrictions, neighborhood
nesting and exact realized union/core, as specified in `PolyhedralGraph`.
A deformation retraction alone is weaker.

For the outer torus, first construct a small source torus around the rim in its
local PL model, then transport through `h` and `ct`. Applying
`IsPLSphere.exists_solid_torus_neighborhood` directly to `ct '' h '' rim` would
incorrectly assume `h` is PL. Choose `Q` inside all relevant buffers, using finite
incidence and positive local margins; then prove the no-disk clause from the
spine obstruction. `exists_chart_iUnion_carrier_subset_source` supplies a common
chart only after `Q ⊆ H` has been arranged; a common chart is not the torus.

BM's two-sidedness issue remains a downstream derived-theorem obligation. The
noncompact frame only bounds `tetraBall` by carrier support, unlike the compact
simplex-position clause. Its explicit model can record local two-sidedness, but
a proof for **arbitrary** frozen frames must derive it. I did not work on that
collaborator-owned source-face frontier.

## 2. Preparation: make the geometry before choosing the scale

This leaf chooses pierced balls, larger chart-local balls, graph cores, nested
tube neighborhoods and marked annuli, and finally one positive tolerance per
vertex certifying every stated inequality and stability property.
Its `hframe`, `hN`, and `hQint` come from leaf 1. The assembly really supplies
`hCchart` from `hHchart`, `hcarF`, `hQint`, and `hQH`; that previously dropped
input is now accounted for.

Use the following dependency order.

1. Orient the two ends of every edge. Separate entire splitting disks by locally
   finite disjoint open neighborhoods, also when the graph contains triangles.
   Localize each **whole future lens** there, not just its boundary circle.
2. Construct the pierced cells and transverse boundary circles inside those
   neighborhoods, fixing vertex neighborhoods and covering each graph edge by
   interiors of the pierced balls. Choose compact cores subordinate to this
   interior cover. A detour that loses part of the original graph is illegal.
3. Construct compatible nested regular-neighborhood tori `Tn ⊆ interior Sn`,
   away from the graph and every core; choose `Aa`, `Bb`, `Bc` and all six end
   circles with the specified side and component conditions. Enlarge to `Cc`
   inside `U ∩ h⁻¹(interior Q)` and the already supplied target-chart preimage,
   preserving local finiteness and containing the incident tubes.
4. Obtain each core's stability radius from `PLCellOnStability`. For all compact
   disjoint pieces obtain positive separation margins; for a compact lens
   contained in its open neighborhood, obtain a thickening radius whose whole
   intersection stays there. Allocate fractions of each relevant margin to its
   endpoint radii so that **sums** satisfy the strict bounds.
5. Choose `ε w` below this locally finite family of constraints and the stability
   radius. The minimum is vertexwise over the finite relevant neighborhood,
   with separation from the remaining locally finite closed union. There is no
   common positive minimum over an infinite graph. The universal stability field
   is downward closed in this final scale.

An important producer mismatch: `DualCellPiercingNeighborhoods` gives finite
families with `(graphDualCell ... v).space ∩ C i = J i`; the whole intersection
is a circle. It is not already the overlapping-ball configuration whose `Ab₀`
lies inside the opposite ball. `DualCellPiercingAnnuli` supplies separate boundary
bicollars; it does not prove all side/component/generator clauses of preparation.
The finite `DualCellPiercingStability` radius only preserves its own containment
and disjointness assertions.

`InnerSolidTorusToroidalShell.exists_toroidalShell_of_isCompact_subset_interior`
supplies a nested **topological** solid torus and a shell, not the two required
PL-derived regular-neighborhood certificates or prescribed annulus seams.
`Section28Annuli.moise286`, `PrismLateralCircleSides`, and `LateralAnnulusLevels`
are useful after essential polygons and product coordinates have been supplied;
their no-disk/essentiality hypotheses still need the constructed core-circle
generator. None should be used to choose annuli independently of the same tubes.

## 3. The initial piercing package

The package constructs PL maps on the enlarged cells close to the original
embedding and a finite, nonempty, transverse circle decomposition at each edge.
`h341` is a named input of the outer consumer; it is not proved by CGN. All other
inputs come from the first two leaves and the assembly's carrier-local-finiteness
argument. The quantifier is existential in the approximants: an arbitrary family
merely within the public `ε` need not satisfy the missing tube-side conditions.

Choose auxiliary scales `δ w < ε w` with slack for the subsequent perturbation,
after obtaining stability of tube containment, the inner/outer annular sides and
the two outside-`Tp` connected components. Approximate on `Cc` by the existing
chart-local `Moise341` pattern. Make a relative, sufficiently small PL move in
finitely many charts per compact edge region; assemble the moves using local
finiteness. `CurveCrossingGeneralPosition` and `ChartBallGeneralPosition` supply
Euclidean ingredients, not this simultaneous manifold-relative move.

Define `Sp = G_a '' Sn`, `Tp = G_a '' Tn` from the **final** maps. In each tube,
crossing charts make the compact intersection a closed PL 1-manifold; the
`CrossingTraceCircles` finite-circle theorem applies after chart/polyhedron and
full-line-chart hypotheses are proved. Reindex its finite type by `Fin (cnt e)`;
choose arbitrary values for `Pg e i` beyond the count. Inside/outside separation
of the two ends of `Aa` proves nonemptiness and hence `0 < cnt e`. Compactness
alone does not make the number of components finite without the manifold/link
argument.

For the 22 piercing conjuncts, the precise division is:

- `section34MarginConditions`: 2, 3, 6, 10, 12–14, the annular-interior part of 7,
  the outside part of 8, and the disjointness part of 9.
- `section34OverlapConditions`: 21. `section34MarkerConditions`: 22 and the
  separately needed core containment/support disjointness.
- `locallyFinite_support_of_section34CutFrame`: 5; the definition supplies 4.
- Construct 1; 11 then follows by restriction to the supplied PL cell. Still
  construct the `interior Tp` part of 7, the inside part of 8,
  the containment part of 9, component certificates 15–16, and 17–20.

The current real module `IsPLHomeomorphIntoMonoOfIsPLCellOn` supplies
`IsPLHomeomorphInto.mono_of_isPLCellOn`: apply it to 1, the preparation's
`IsPLCellOn 3 (Cp w) (CpBd w)`, and `Cp w ⊆ Cc w`. The CGN docstring's older
claim that the tree lacks this restriction theorem is stale. Keep 11 as a field
for compatibility, but do not allocate a new producer for it.

## 4. Protected circle removal and the downstream audit

Write `a = (ends e₀).1`, `b = (ends e₀).2`. The goal is to replace one or both
parametrized balls inside `interior (Sp e₀)` so the finite crossing count drops,
with the same preparation, `Sp`, and `Tp`. `hpack` and `hlt` are the sole current
configuration inputs; a proof cannot appeal again to `Moise341` or to a distance
bound not present in this leaf.

First prove an innermost-removable-configuration lemma. It must distinguish a
circle bounding a disk in an annulus from essential parallel circles bounding
an annular band. A circle on `Bb` need not bound a disk **in `Bb`**. Several
parallel essential crossings are not refuted by merely calling a circle
innermost. Use the component clauses and generator information to find the
appropriate disk or adjacent-band cancellation. The bound `cnt' < cnt` permits
removing two crossings at once. This is a route warning, not a verified
counterexample to the frozen leaf.

Realize the cancellation by a relative PL modification of the parametrized
enlarged cell, not merely by replacing its boundary as a set. If moving the
first endpoint, clause 4 forces both `G'_a '' Sn = Sp` and `G'_a '' Tn = Tp`.
An ambient homeomorphism supported in `interior Sp` preserves `Sp`, but does not
automatically preserve `Tp`; that must be built into the move.

| Substep | Piercing clauses that require verification |
|---|---|
| Relative PL extension and fixed tube images | 1, 4, 11; establish off-support equality on all of `Cc`. |
| Support confinement/carriers/other edges | 2–3, 5–6, 10, 12–14, 21–22. Disjoint supports alone do not certify preservation of whole overlaps in 21; prove where the modified lens lies. |
| Disk or band cancellation, with sides unchanged | 7–9 and especially the connected-component assertions 15–16. |
| Rebuild and enumerate the remaining trace | 17–20, strict decrease at `e₀`, unchanged counts and annulus images at every other edge. |

`section34Step_eqOn_marker_and_boundary` then supplies marker equality and
unrelated-boundary equality. `Section34CircleRemovalDescent` supplies the global
removal, and `Section34DeletedBalls`/`Section34CapDeletion` supply the literal
deleted balls. Those modules do not perform this cancellation.

The original `ε` bound is not an invariant of the step. It holds automatically
at points fixed by the off-support equality **if it held for the old family**;
there is no such conclusion at moved points, nor a general fixed-`ε` improvement
from the stated step. A stronger quantitative producer would need its own
displacement/support estimates and budget. For BN, the assembly retains
`hG₁dist`, `hoff₂`, `hcore₂`, `hSpK`, and `hDmark`; it passes only the latter
geometric configuration requested by edge matching. It correctly transports
core containment before deletion, so deletion does not silently use closeness.
It drops removal's explicit marker-equality conjunct, and edge matching receives
neither that provenance nor `hG₁dist`/`hoff₂`. Also, `hoff₂` tests membership using
`G₁`, not `G₂`; reformulating it with the new map needs a separate support lemma.
The cut's dropped `hQtri` is already represented in the returned outer-torus
certificate. No further dropped-conjunct defect was found on the deletion path.

## Non-vacuity, missing obligation and surprise

A common nonidentity geometric model is a periodic tetrahedral triangulation of
`R³`, its small standard graph cut, and an affine shear `h(x,y,z)=(x+y,y,z)`.
Choose locally bounded PL box carriers, locally small cut/tube radii and strict
margins. For testing the removal premise use an additional local cancelling
pair of crossings at one edge, leaving the other supports fixed; a count-one
example would not test `hlt`. These are proposed geometric fixtures, **not**
existing checked inhabitants of the full cut/preparation/package predicates:
their side/component and all-label certificates remain precisely the producer
work above. The finite handle-decomposition fixture cannot fill that gap.

Missing obligation: coherent local-to-global production, including whole-lens
isolation and a supported map-level cancellation; BN separately owns the
orientation/provenance interface decision. Most likely surprise: preserving
the fixed inner tube and clauses 15–16 during an essential-band cancellation.

## Named reductions (proposals, not declarations added to the library)

`SMALL` means finite/set/transport bookkeeping with supplied certificates;
`MEDIUM` means a bounded geometric lemma; `NEW_THEORY` means a substantial
producer absent from the inspected tree. Dependencies are real modules unless
explicitly called another proposed child.

| Parent | Named sub-leaf | Size | Content and modules |
|---|---|---|---|
| Cut frame | `exists_subdivision_with_finite_carrier_assignment` | MEDIUM | Subordinate refinement, finite fibers, source and target carrier margins; `SubdivisionSubordinateToCover`, `Section34CarrierSupportLocallyFinite`, `LocallyFiniteSplittingDisks`. |
| Cut frame | `exists_locally_finite_graph_cut_cells` | NEW_THEORY | Joint eight-label cells, closures, boundaries, incidence and two-sided local model; `DualCellDecomposition`, `DerivedNeighborhoodCells`, `PLCellOnBoundary`, `Section34CompactSplitDiskIntersection` as a compact analogy only. |
| Cut frame | `exists_graph_cut_derived_neighborhood_exhaustion` | NEW_THEORY | Exact increasing ambient/core exhaustion for the chosen cut; `PolyhedralGraph`, `LocallyFinitePieceTowerExistence`, `DerivedNeighborhoodCells`. |
| Cut frame | `exists_outer_tori_with_fine_carriers` | NEW_THEORY | Source torus transport, spine, simultaneous buffers and no filling disk; `CircleSolidTorus`, `SolidTorusOpenNeighborhood`, `Section34Frame`. |
| Preparation | `exists_locally_finite_pierced_cells_with_isolated_lenses` | NEW_THEORY | Genuine overlapping cells, preserved graph interior and disjoint whole lenses; `DualCellPiercing`, `DualCellPiercingNeighborhoods`, `DualCellPiercingAnnuli`, `LocallyFiniteSplittingDisks`. |
| Preparation | `exists_marked_nested_piercing_annuli` | NEW_THEORY | Same-tube annuli, sides, components, regular neighborhoods and generators; `Section28Annuli`, `PrismLateralCircleSides`, `LateralAnnulusLevels`, `PolyhedralGraph`. |
| Preparation | `exists_chart_local_enlargements_and_graph_cores` | MEDIUM | Compact core cover and enlarged cells containing incident tubes; `PLCellOn`, `LocallyFiniteSeparatingNeighborhoods`, `Section34Frame`. |
| Preparation | `exists_vertex_scales_with_sum_margins_and_overlap_isolation` | MEDIUM | All strict metric bounds and universal core stability for the final radii; `DualCellPiercingStability`, `PLCellOnStability`, `LocallyFiniteSeparatingNeighborhoods`. |
| Package | `exists_auxiliary_scales_preserving_piercing_sides` | NEW_THEORY | Tube containment and component stability for finer approximants; `PLCellOnStability`, `PrismLateralCircleSides`, `Section34Frame`. |
| Package | `exists_relative_crossing_vertex_approximations` | NEW_THEORY | Chart-local approximation with globally compatible relative perturbations and remaining error budget; the proved `Moise341` approximation pattern, `CurveCrossingGeneralPosition`, `ChartBallGeneralPosition`, `LocallyFinitePLPastingManifold`. |
| Package | `exists_positive_finite_piercing_circle_family` | MEDIUM | Full line charts, finite circle extraction, nonemptiness and indexing; `CrossingTraceCircles`, `PLCellOnBoundary`, `Section34Frame`. |
| Package | `piercing_conditions_of_crossings_and_margins` | SMALL | Assemble the numbered exporter outputs and the three preceding children; `Section34Frame`. |
| Removal step | `exists_innermost_piercing_cancellation` | NEW_THEORY | Disk/band dichotomy, support and side eligibility when count exceeds one; `SphereInnermostDisk`, `Section28Annuli`, `LateralAnnulusLevels`, `Section34Frame`. |
| Removal step | `exists_relative_PL_piercing_cancellation` | NEW_THEORY | Extend over `Cc`, fix outside support, preserve both tube images, retain component certificates; `BoundaryCollarExtension`, `SurfaceSplitBallPair`, `Section34CapDeletion` for local geometry, not an existing cancellation theorem. |
| Removal step | `piercing_conditions_after_cancellation` | MEDIUM | Verify all 22 clauses, especially whole overlaps and 15–16, from the exact constructed move; `Section34Frame`, preceding child. |
| Removal step | `exists_reindexed_piercing_family_of_strict_decrease` | SMALL | Count/reindex circles, unchanged foreign data, marker equality; `CrossingTraceCircles`, the proved marker lemma, `Section34CircleRemovalDescent`. |
