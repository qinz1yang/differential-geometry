# BQ — Section 34 trace leaves

Source review, 2026-09-23, `D:/differential-geometry-moise-int`,
`codex/moise-integration`, HEAD `c45b6faf19e693ae1134ba6f2656e71fbd0859d5`.
Paths below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
No Lean/probe invocation, frozen-source edit, or fresh axiom audit was made.

Two assertions in the previous route sketch need correction. A circle with zero
image in `H₁` of a **solid** torus need not bound a disk on its boundary. Also,
two crossings in the same direction do not imply a bigon. Neither correction
is a counterexample to the full frozen leaves, whose whole-trace generator and
exterior hypotheses are stronger. The existing P6 arc lemmas assume the
single-crossing conclusion; they cannot establish it here without circularity.

| Leaf | Verdict | Reason |
|---|---|---|
| `compactTrace_of_noOperation` | OK, provisional; short route needs repair | Circle extraction and homology selection have real producers; the missing work is the admissible disk/bigon normal form relative to all splitting disks and other face balls. |
| `section34Trace_of_noOperation` | OK, provisional; transport route open | Same local geometry; a single target-chart argument has an unavailable input in this exact leaf, so an intrinsic finite-model transport is required unless the lead changes the interface. |
| `section34TraceCircle_homologyMap_ne_zero` | No live consumer found | It is unused by normalization, terminal assembly and both real P6 proofs; compact P6 instead consumes the separate last field of `Section34CompactTrace`. |

OK here is a feasibility judgment, not a proved endpoint or certified joint
fixture. No full counterexample or proof of vacuity was found.

## 1. Compact trace: what must actually be produced

Fix a face `s`. Write `P=fbl s`, `N=⋃w Vw`, `T=section34CompactFaceTorus V s`,
`Θ=frontier T`, and `γe=tgtEBd e`. The conclusion is a positive finite disjoint
family of PL circles whose union is both `∂P ∩ ∂N` and `∂P ∩ Θ`, with each circle
meeting every incident `γe` in exactly one point. The compact conclusion also
requires each inclusion map on integral `H₁(T)` to be nonzero.

`hcut` and `hgraph` come from `exists_compactCutAndGraph`; `hinv`, `hnc`, and
`hnb` come from the terminal-family descent. The latter forbids **every** witness
of the two operation predicates, not just one chosen surgery algorithm.
No `hcar`, `h331`, approximation tolerance argument, or new `Moise28.8` assumption
is needed as an additional public input. The underlying cut/graph producer and
operation producers still have their separate open obligations.

The extreme checks rule out shortcuts: an empty trace cannot surject onto the
nontrivial `H₁` of a solid torus; nonzero image `kZ` is not surjectivity; a point
or an arc is not a trace circle. The two crossing normal forms, not merely the
finite component count, exclude tangencies, endpoints and branching.

### Circle extraction and the corrected homology step

Use the invariant's surface crossing, PL sphere recognition of `∂P`, and the
finite ball-union frontier model to obtain full line charts. Then
`CrossingTraceCircles.exists_iUnion_isPLSphere_one_of_forall_lineChart` supplies
the finite disjoint circle family. Its polyhedron and full-line-chart premises
must be supplied; it does not follow just from the word "crossing". The compact
graph frame already supplies `IsCombinatorialSolidTorus T`. Avoidance of foreign
vertex balls gives the two trace equalities, with the local frontier argument
also present in `Section34CompactGeneralPosition`.

Here is a concrete refutation of the suggested bare null-homology lemma. In
`T=D²×S¹`, let `J=∂D²×{1}`. It is an embedded circle on `∂T`, bounds a disk in
`T`, and hence maps to zero in `H₁(T)`. It is essential on `∂T` and bounds no disk
there. The tree itself has the corresponding PL example in
`TorusMeridian.exists_embedded_solid_torus_meridian`.

The corrected route first uses the **whole family**. Apply
`IsPLTorus.carriesFirstHomologyOnto_or_subsingleton_of_iUnion` from
`TorusSubsurfaceCarrier` to `Θ`, its circles, and invariant 7. Exclude the
subsingleton alternative by the solid-torus product model (`H₁(T)≅Z`). This
produces a nonseparating trace circle `K` whose inclusion is surjective.
For another trace circle `J`, `TorusCircleHomology` says that if `Θ \ J` is
preconnected, its image subgroup equals that of `K`, and is therefore all of
`H₁(T)`. Thus a zero-image trace circle must be separating **in this disjoint
surjective family**. `SeparatingPolygonDisk` then gives a PL disk in `Θ` with
intrinsic boundary `J`.

`MaximalPolygonHomologyImage` is an alternative finite selection step, but it
still needs the union-to-individual range argument; it is not itself a
surjectivity theorem. `NonseparatingPolygonCarrier` similarly needs a disjoint
carrying reference circle. `SolidTorusInteriorHomology` proves injectivity for
`interior T → T`, not for `Θ → T`, and cannot dispose of the meridian example.

What is no longer missing from the cited part of 28.8 is the bare separating
polygon disk theorem, annular parallelism of disjoint nonseparating circles,
or selection of a carrying component. What remains is their **marked relative
version**, yielding the actual compression or bigon predicate, followed by
geometric single intersection with the specified meridian system.

### A torus disk is not yet an Operation 1 disk

`Section34CompactCompression` requires a disk in **one** `tgtVBd w`, disjoint from
**all closed splitting disks**, with exact intersection with the selected face
sphere equal to its intrinsic rim and its interior disjoint from every other
face **ball**. A disk somewhere on `Θ` supplies none of these extra facts.

Choose innermost disks/arcs relative to the finite trace and meridian arrangement.
If a separating disk crosses the incident meridians, take an outermost arc to
obtain a disk bigon. If it avoids them, it lies in a vertex strip and is a
candidate compression. There is an additional, substantial obstruction: a
candidate can enclose a foreign splitting disk. On `Θ` those are disks, but on
`∂N` they are holes. Use `Section34CompactLinkCondition` and the exterior/escape
condition to exclude this obstruction, or find a smaller admissible operation.
This is the missing Lemmas 9–10 argument; an ordinary torus Schoenflies theorem
does not do it. An innermost choice across the finite relevant face family is
needed to obtain the precise foreign-ball avoidance. The universal `hnc`/`hnb`
allows the resulting operation to be at another face label.

`SphereInnermostDisk` handles an already supplied finite family on a PL sphere.
It does not directly choose a torus disk or make that disk avoid marked holes.
The exact proposed child is: **a separating trace component produces an
admissible compression or an admissible bigon under these cut and invariant
hypotheses**. Its proof must perform the localization just described; this is
new geometric work, not a restatement of the full trace conclusion.

### Single intersection: degree one, then an admissible bigon

After excluding separating components, the preceding homology argument makes
every trace component surjective on `H₁(T)`, hence longitudinal degree `±1`.
Identify each incident splitting disk as a meridian in the cyclic ball model;
its boundary has algebraic intersection `±1` with that component.

The proposed "twice in the same direction" shortcut is false. On
`R²/Z²`, the primitive curve `t↦(2t,t)` meets the meridian `x=0` twice, with the
same sign, in minimal position and with no bigon. Its solid-torus image is
`2Z`; it violates the required family-surjectivity conclusion, not the asserted
local topology of a simple curve. A removable disk bigon gives a pair of
oppositely signed intersections.

Once degree is `±1`, more than one transverse geometric crossing forces a
bigon in a minimal-position argument (cut along meridians to annuli, or use
the cyclic cover). The hard child must improve this to the exact
`Section34CompactBigonSlide`: two PL arcs with the same two-point intrinsic
boundary; the trace arc meets the union of **all** splitting disks only at those
ends; the spanning disk lies in `tgtVBd w ∩ ∂N`; and its interior avoids every
face boundary. Again foreign holes and enclosed trace pieces require the
link/exterior argument and an innermost choice. Then `hnb` gives at most one
crossing, and degree `±1` gives at least one. This combines an algebraic count
with an innermost-bigon proof; neither alone is sufficient.

`Section34CompactIncidentEdges` supplies the cyclic incidence and two incident
edges at each vertex. `Section34CompactSplitDiskIntersection` supplies exact
ball meets. Both `Section34CompactTraceArcs.isPLCellOn_inter_vertexBallImage`
and its manifold counterpart take `hJE` (single intersection) as an argument.
They are downstream checks, not a proof of this step. The compact P6 proof uses
`hJh`, the trace's last homology field, to rule out an interior filling disk;
that field must still be produced even though manifold P6 now uses winding.

## 2. Manifold version and the unused bridge

Finite circles, the family range argument, degree one, and the marked disk/bigon
normal form are the same mathematical local results after transport. The
noncompact graph only requires finite incident stars and finite families on a
compact face region, not a global finite complex. Its link condition must be
derived from the combinatorial 2-sphere link; the compact version has it as a
field and also has boundary links and outer cut cells.

There is an exact supply issue for a proof via one target chart:
`section34Trace_of_noOperation` receives no `hctrl`. Neither `hgraph` nor `hinv`
says that a whole face torus or face ball lies in one maximal-atlas chart.
`Section34FaceTorusCycle.isPLTorus_image_frontier_section34FaceTorus` explicitly
requires such a chart and containment. `Section34FaceDisks` obtains that chart
from `Section34NormalPlus`'s carrier-control field, which this earlier leaf lacks.
Do not silently copy that proof setup.

To retain the frozen interface, construct an intrinsic finite PL torus model
from the cyclic ball/disk gluing, together with its marked meridian system, and
transport through the PL parametrization. Use the local crossing charts and
compactness to glue the trace circle parametrizations. The homology lemmas in
`TorusCircleHomology` and `TorusSubsurfaceCarrier` already permit a continuous
injective map from a model torus into a general Hausdorff target. The outstanding
geometric model and relative PL transport are additional sub-leaves. Alternatively
the lead could consider passing existing `hctrl`; no such repair was made here.
The intrinsic route must also exclude a twisted disk bundle: a cycle of balls
in an arbitrary manifold is not automatically an untwisted solid torus. The
available route is the graph-frame generator circle `h '' simplexRim`, which
bounds the embedded image triangle in the ambient manifold. Its trivial ambient
orientation character, together with surjectivity on the face-neighborhood
fundamental group, should force the untwisted case. This is a proof obligation
of the proposed model child, not an extra hypothesis or an existing export of
the Euclidean `CyclicBallUnion` theorem.
In either route local frontier equality must be proved before borrowing the
compact argument; source local finiteness is not automatically global target
local finiteness without the appropriate embedding/domain argument.

`Section34Trace` has six conjuncts and **no homology field**; its compact twin
has seven. A recursive search of current Lean sources finds
`section34TraceCircle_homologyMap_ne_zero` only at its declaration and two
docstring mentions in `Skeleton/Section34Normalization.lean`. The normalization
assembly calls only `section34Trace_of_noOperation`. The terminal skeleton
imports the real `Section34FaceDisks`, which uses `BallWindingObstruction`, not
this bridge. The compact skeleton calls its own trace and real compact P6.
Thus the named bridge is dead on the current assembly path; retirement is a
lead decision. Its mathematical content may still be a useful later corollary,
but it must not be counted as a current endpoint dependency.

## Joint test, missing obligation and surprise

A nondegenerate geometric test is a sufficiently fine tetrahedral ball, with a
bivalent subdivision vertex, the standard cut, `f₁=g` a nonzero PL translation,
and `h=g∘ψ` with non-PL `ψ` supported in a residual tetrahedron. Standard thin
face balls have parallel longitudinal trace circles meeting each incident seam
once, no vertex-contained compression circle and no returning bigon; use the
same local configuration in a triangulated open manifold for the second leaf.
All-label carrier/exterior certificates for this model are still unverified;
neither this review nor the existing local tetrahedron illustration is a
checked joint Lean inhabitant. Empty trace and identity fixtures would not
test the missing geometry.

Missing obligation: turn torus disks/bigons into operations avoiding every
foreign splitting disk and face ball, using the actual link/exterior inputs.
Most likely surprise: a perfectly good torus bigon may surround a foreign
splitting disk and therefore fail `Dj ⊆ ∂N` or the exact splitting-disk avoidance
clause. The second major risk is the unavailable single-chart input above.

## Named reductions of the requested leaves

`SMALL` is bookkeeping over supplied certificates; `MEDIUM` is a bounded
topological/transport bridge; `NEW_THEORY` is a substantial missing producer.
These labels do not claim implementation or fresh compilation.

| Parent | Named sub-leaf | Size | Content and tree modules |
|---|---|---|---|
| Compact trace | `exists_finite_trace_circles_of_crossings` | MEDIUM | Both frontier equalities, full line charts and finite circle enumeration; `CrossingTraceCircles`, `BallUnionFrontier`, `Section34CompactGeneralPosition`, `PLCellOnBoundary`. |
| Compact trace | `exists_surjective_trace_circle` | SMALL after circle extraction | Exclude trivial target homology and use whole-family surjectivity; `TorusSubsurfaceCarrier`, `TorusCircleHomology`, `FirstHomologyCarrying`; `MaximalPolygonHomologyImage` is an alternative selection ingredient. |
| Compact trace | `trace_circle_separates_of_zero_homology_image` | SMALL | Compare each nonseparating component with the surjective one; `TorusCircleHomology`, then `SeparatingPolygonDisk` for its disk. This is the corrected conditional null-homology statement. |
| Compact trace | `split_disks_form_marked_meridian_system` | MEDIUM | Track actual seams through the cyclic ball model and identify the cut annuli; `CyclicBallUnion`, `CylindricalMeridian`, `Section34CompactIncidentEdges`, `Section34CompactSplitDiskIntersection`. |
| Compact trace | `exists_admissible_operation_of_separating_trace` | NEW_THEORY | Localize the innermost torus disk; either a clean compression or a clean bigon, including all foreign-mouth and foreign-ball exclusions; `SeparatingPolygonDisk`, `SphereInnermostDisk`, `Section34CompactVocabulary` link/exterior fields, `Section34CompactSplitDiskIntersection`. |
| Compact trace | `exists_admissible_bigon_of_excess_meridian_crossings` | NEW_THEORY | Primitive degree, annulus/cyclic-cover bigon, innermost localization and the full operation predicate; `CoveringLift`, `LateralAnnulusLevels`, `Section28Annuli`, preceding meridian and localization children. `BigonDrag` performs a supplied move, not this witness extraction. |
| Compact trace | `compact_trace_of_admissible_operation_dichotomies` | SMALL | Apply `hnc/hnb`, get degree-one single crossings, nonzero component homology and positive `r`; `Section34CompactVocabulary`, preceding children. |
| Manifold trace | `exists_intrinsic_PL_face_torus_with_marked_seams` | NEW_THEORY | A model usable without an unprovided target chart; cyclic gluing from `Section34FaceTorusCycle`/`CyclicBallUnion`, `Section34IncidentEdges`, `Section34SplitDiskIntersection`. Their chart-dependent theorems are ingredients, not this output. |
| Manifold trace | `exists_polyhedral_trace_circles_from_local_models` | MEDIUM | Compact finite atlas, full local crossings and intrinsic PL circle parametrizations; `CrossingTraceCircles`, `PLCellOn`, `Section34FaceBallVocabulary`, `LocallyFiniteSplittingDisks`. |
| Manifold trace | `admissible_trace_operations_of_intrinsic_model` | NEW_THEORY | Transport the compact local disk/bigon theorem, derive sphere-link bypass, use carrier-frontier escape in place of unboundedness, and prove exact domain/frontier/avoidance statements; `Section34Frame`, `Section34FaceBallVocabulary`, preceding model child. |
| Manifold trace | `section34_trace_of_intrinsic_operation_dichotomies` | SMALL after transport | Family homology internally, singleton crossings and circle reindexing; `TorusSubsurfaceCarrier`, `TorusCircleHomology`, `Section34Frame`. No call to the dead homology bridge or to P6's single-crossing-dependent arc lemma. |
