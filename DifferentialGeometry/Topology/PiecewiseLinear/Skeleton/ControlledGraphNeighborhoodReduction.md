# Controlled graph neighborhood reconnaissance

Date: 2026-09-22. Baseline: `0642f2e7deaa33a527f3c08fe058b08ff0ee0187`.
Scope: probes only; no lead integration or progress acceptance. New leaves are **UNREVIEWED**.
Companion: [ControlledGraphNeighborhoodReduction.lean](ControlledGraphNeighborhoodReduction.lean).

## Edge matching: separate relative maps from target geometry

The original `exists_section34EdgeMatching` produces four map clauses and two geometric clauses.
The probe copies its exact endpoint and proves it from three smaller leaves. None re-assumes
the full endpoint. The ball maps are constructed by genuine boundary extension.

| Part | Status | What it must supply |
|---|---|---|
| `vertex_inter_subset_boundary` | Proved assembly from `Section34CutFrame` | The intersection of two distinct source vertex balls lies in each named intrinsic boundary. Uses common-face decomposition and strict dimension decrease. |
| `exists_extension_of_cell_boundary` | Proved wrapper of current API | An already specified PL map of the entire intrinsic boundary extends over a cell, retaining that exact map. With d=2 this is circle-to-disk; with d=3 it is sphere-to-ball. |
| `exists_joint_boundary_matching` | `NEW_THEORY` relative finite surface matching | Jointly chooses one boundary-sphere map per vertex, with identical restrictions to shared disks and exact images of every overlap. It does **not** accept arbitrary independent disk maps. |
| `face_rim_subset_interior_deleted_family` | `SMALL_NEW_LEMMA` | Local finiteness and closedness let `hQsep` discard the nonincident cells near a rim point; `hDnbhd` supplies the neighborhood for the full union. This yields the required neighborhood for the incident subfamily. |
| `exists_nested_torus_of_deleted_family`: chart containment and outer inclusion | `CURRENT_API` | `section34FaceTorus_subset_outerTorus` already proves both for the fixed Dv family from `hDvQ`. |
| `exists_nested_torus_of_deleted_family`: radial inner torus | `SMALL_NEW_LEMMA` | Shrink the disk factor in the actual `IsSpine Sd J` coordinates, using compactness of J and its containment in the target interior, and retain the radial shell up to Sd. |
| `exists_nested_torus_of_deleted_family`: cyclic target recognition | `NEW_THEORY` | Recognize the actual cyclic union of target balls, with its exact splitting disks and gluing information, as a CST. This is the genuinely new part of the bundled geometric leaf. |

The three open leaves retain the original input bundle during reconnaissance, so no supply
is silently discarded. A future proof should minimize inputs at the natural interface once its
exact dependency is established. In particular, the last two leaves refer to **Dv itself**, not
to any newly chosen map. An arbitrary reparametrization of the vertex balls cannot make these
geometric assertions true; the final proof rewrites them by the proved family equality
`(fun w => G' w '' src (.vertexBall w)) = Dv`.

The finite surface matching leaf is deliberately still a substantial frontier. It isolates the
remaining two-dimensional relative problem from the already available three-dimensional cell
extension. It does not claim that a connected punctured sphere automatically comes with the
required simultaneous PL parametrization.

## The orientation compatibility issue

`SphericalDiskPair.lean:47` proves
`exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk`: one specified disk map is fixed, while a
second disk is only mapped **as a set**. This is not an API for prescribing arbitrary maps on
every disk of a finite family. Two independently prescribed disk maps may induce opposite
orientations relative to their surrounding spheres and cannot both extend to one sphere map.

The proposed route must therefore choose the circle maps and disk maps jointly, or explicitly
produce compatible orientation data from the original geometric configuration. These are proof
outputs, not new assumptions at the frozen endpoint. A tree-by-tree choice without checking
cycles in the incidence graph can lose precisely this compatibility. The ambient manifolds in
the frozen statement are not assumed globally orientable.

The lower-dimensional implementation sequence is:

1. Use the disjoint incident splitting disks and finite vertex degree to form the marked
   boundary-sphere systems. Choose coherent maps on their rim circles, retaining the original
   adjacency labels and the orientation information supplied by the geometry.
2. Extend each common circle map once across its splitting disk using
   `exists_extension_of_cell_boundary (d := 2)`. Both neighboring vertices must consume this
   **same** disk map.
3. Extend the compatible finite family of disk maps over the remaining punctured sphere.
   A relative construction must preserve every previously matched disk and its seams. This
   finite-family relative surface theorem is not supplied merely by the one-disk or two-disk
   APIs.
4. Extend the resulting entire sphere map over the vertex ball using
   `exists_extension_of_cell_boundary (d := 3)`. The probe already performs this step and
   proves compatibility and exact overlap images from the fixed boundary restrictions.

The current probe encapsulates steps 1-3 in the **joint** boundary leaf. Further splitting them
requires a precise finite marked-sphere vocabulary and a proved producer of its orientation
compatibility; that vocabulary has not been silently postulated here.

## Target geometry is a separate producer

Several bounded pieces of the torus recognition can be attempted immediately:

- `Section34Frame.lean:1073`'s `section34FaceTorus_subset_outerTorus` already gives chart-source
  containment and inclusion of the chart image in `interior (Sd s)` from `Dv w ⊆ Q w`.
- `ChartImagePLCell.lean:54` transports each `IsPLCellOn` through a chart from the maximal atlas,
  preserving the exact named intrinsic boundary; line 75 supplies the resulting PL-ball fact.
- `finite_splitDisk_of_section34CutFrame` at `Section34Frame.lean:698` supplies finite incidence.
- Compactness of each `Dv w` and local finiteness of Q allow a neighborhood of a rim point to
  discard cells whose carriers do not meet its source face. Combine that with `hQsep` and
  `hDnbhd`, rather than assuming a global union neighborhood is automatically an incident union
  neighborhood. This is the proposed small rim-localization proof.

The genuine geometric obligations are to identify the **actual cyclic union** of target balls,
with the exact splitting disks, as the required CST, and to identify its relation to the
original rim/spine. Homeomorphism types of individual balls plus a graph-shaped nerve do not
themselves supply all the required PL gluing and orientation information.

Once the actual rim lies in the interior of this CST and its chart image lies inside Sd, the
inner torus can be chosen from the product coordinates of the given `IsSpine Sd J`: take a
sufficiently small disk radius around the compact core, inside the prescribed open interior
of the target CST. It must preserve the **same core J** and give the shell up to Sd. Compare
`InnerSolidTorusToroidalShell.lean:66`, which already builds radial shell coordinates, but whose
particular supplied theorem contains a compact set in a chosen inner torus and does not directly
state the needed small-neighborhood-of-the-core variant. That variant is bounded transport work,
not permission to substitute an unrelated spine.

## Relevant verified-source interfaces

These entries were read from current source; this reconnaissance does not re-audit their
transitive axioms.

| Source | Actual interface |
|---|---|
| `LabelledCellAssembly.lean:224` | `exists_isPLHomeomorphInto_extension_of_cell`: fixed complete boundary map extends, for arbitrary positive dimension with the existing cell parametrizations. |
| `SphericalCircleExtension.lean:17` | One specified PL circle map extends across a PL two-sphere. |
| `SphericalDiskPair.lean:47` | One prescribed disk map plus a second disk mapped as a set; not arbitrary finite prescribed disk maps. |
| `BoundaryExtension.lean:13` | PL boundary-complex map extends across PL balls, relative to the boundary. |
| `TubeOfGraphDualCells.lean:46` | A PL sphere minus a finite disjoint family of PL disks is connected; this supplies topology of the complement, not its relative parametrization. |
| `Section34DeletedBalls.lean:47` | Existing deleted-ball producer, including the literal deletion, exact disk intersections and neighborhood output. |

## Paper fixtures and negative tests

Use a finite triangulated three-ball containing a Y-shaped graph, with three small splitting
disks on the central vertex sphere, pairwise disjoint and labelled by the three incident edges.
Use a translated copy for the target and transport every rim/disk map by the same translation.
This tests genuine valence three, rather than a two-disk example. For face-torus recognition
use a triangulated polygonal cycle and its small regular neighborhood, with the original cycle
as core, nested inside a larger coordinate product solid torus. The maps can be independently
reparametrized after the target sets are fixed; the torus certificate must remain about those
same sets.

As a rejection test, prescribe an orientation-preserving disk map on one of two source disks
and an orientation-reversing map on another relative to fixed sphere orientations. No single
sphere homeomorphism realizes both. The joint-choice leaf avoids asserting this false universal
extension principle. These are paper checks only; Lean joint fixture status is **UNTESTED**.

## Verification boundary

The root reconnaissance task serializes private checker calls and will append the independent
one-step circle-removal reduction and its 22-clause dependency table. No root aggregate import,
frozen-source edit, lease mutation, ledger acceptance, or whole-project build is part of this
reconnaissance.

## Protected circle removal: partial reduction and obstruction map

This is a partial reconnaissance reduction, not a new frozen producer. It deliberately
DOES NOT claim an assembly of `exists_section34ProtectedCircleRemovalStep` from the current frozen
hypotheses. The generic support transport lemmas are written with full proofs; the geometric
selection/extension theorem needed to construct their support witness remains unformulated.
Relevant real API modules include `Section34Frame`, `Section34CircleRemovalDescent`,
`PLCellOnBoundary` for composition, and `BallUnionFrontier` for connectedness propagation.

## Concrete candidate move and actual gap

Write a=(ends e0).1 and b=(ends e0).2. A promising move changes ONLY the b-vertex by postcomposing
G b with a homeomorphism phi, leaving all other vertex maps unchanged. The homeomorphism must be
PL on the whole image G b '' Cc b (and have the PL inverse required by `IsPLHomeomorphInto`), not
merely a parametrization of the changed disk. Its support V lies in `interior (Sp e0)`.
`PLCellOnBoundary.IsPLHomeomorphInto.comp_of_image_eq` is a real composition producer once that
certificate is supplied. `Section34CircleRemovalDescent.IsPLHomeomorphInto.congr_of_eqOn` deals
with unchanged vertex maps. The image of Cp is transported with the same map, never independently.

A STRONGER possible support certificate is `V ⊆ G b '' Sn e0`. If this can be achieved, source
injectivity on Cc b and the pairwise disjoint source tubes prove that every other G b '' Sn d is
fixed. The proved generic `eqOn_comp_of_disjoint_source` isolates this mechanism. This would
protect cross-carrier clause 3 and tube-image clause 4. However, the frozen piercing conditions
DO NOT directly supply an embedded cancellation disk inside this common region. The existence
of a suitable disk there is unverified, so this stronger certificate is not asserted by a sorry
leaf with the original assumptions. That would merely hide a potentially false strengthening.

For whole-cell protection, the exact sufficient certificate is
`Disjoint V (G w '' Cp w)` for the relevant foreign vertices, not just the existing clause 13
`Disjoint (Sp e0) (G w '' CpBd w)`.
The supplied `disjoint_of_preconnected_of_anchor_outside` gives a possible route: once
`frontier (G w '' Cp w) = G w '' CpBd w`, connectedness of Sp e0 and an anchor in Sp e0 outside
the foreign cell are available, boundary avoidance implies whole-cell avoidance. The frontier
identification must be justified in the current charted ambient assumptions; the anchor must be
proved from an actual active intersection point, source adjacency, clause 14 or clause 21. None
is silently included in the support certificate. This is the exact bridge to investigate next.

A common ambient homeomorphism applied to ALL vertices cannot remove circles: injectivity
preserves all intersections and their component count. Likewise, a homeomorphism preserving both
active first-cell and inner-tube sets transports their intersection with the moved annulus and
cannot justify a decrease. An actual cancellation must change one annulus relative to the other;
its preservation of active side-connectivity conditions 15/16 is geometric, not formal transport.

## Exact piercing-clause dependency table

Numbering follows the 22 top-level conjuncts of `Section34Frame.lean:1011` exactly. `CURRENT_API`
means a named real theorem or the supplied generic proof applies AFTER its explicit certificate;
it does not assert the certificate already follows from the frozen hypotheses.

| # | Actual condition | Unchanged edge / formal transport | Active e0 / missing certificate |
|---|---|---|---|
| 1 | PL embedding of every entire Cc w | `CURRENT_API`: composition with the SAME phi; other vertices by equality | Need a PL ambient extension on all G b(Cc b), with inverse. A surface disk map alone is insufficient. |
| 2 | G w(Cc w) lies in Q w | `CURRENT_API`: support inside Sp e0, which lies in Q b by old clause 3; `image_comp_subset_of_support_subset` | Verify `Sp e0 ⊆ Q b`; then containment survives even without the old epsilon estimate. |
| 3 | Each image of Sn e lies in the OTHER endpoint carrier Q | `CURRENT_API` if all moved-vertex Sn d, d≠e0, are fixed using the common source-tube support certificate | For e0, support in Sp e0 ⊆ Q a suffices; obtain that containment from old clause 2 and Sn e0⊆Cc a. Merely support in Sp e0 does not prove the foreign-edge cases. |
| 4 | Fixed Sp e=G first(Sn e), Tp e=G first(Tn e) | Active first endpoint a is unchanged; for d≠e0 with first endpoint b use fixation of Sn d and Tn d⊆Sn d | Must preserve Sp/Tp LITERALLY, not rechoose them after surgery. |
| 5 | Local finiteness of Sp in h(U) | Literal reuse: Sp is unchanged | No new local-finiteness theorem. |
| 6 | Pairwise disjoint Sp | Literal reuse | No new disjointness theorem. |
| 7 | Full boundary intersection lies in the two open annuli and interior Tp | Foreign whole-cell/boundary protection prevents new intersections; then unchanged annular images give reuse | `NEW_THEORY`: the active replacement must control the FULL CpBd intersection, not just an enumerated subset of annular crossings. |
| 8 | Ab0 lies inside the second Cp; Ab1 avoids that Cp | Old clause transported when relevant end-circle points are fixed; phi transports ambient interiors | The active cancellation support must avoid the appropriate end-circle images or supply a direct side-preservation proof. |
| 9 | Second Bb lies inside Sp; second Bb ends avoid Tp | Sp-invariance follows from support in its interior; foreign Bb images are fixed in disjoint Sp d | Active end-circle avoidance of the unchanged Tp needs fixation or a direct certificate; support in Sp alone is insufficient. |
| 10 | Sp avoids h(graph) | Literal reuse | Sp unchanged. |
| 11 | PL embedding on every Cp w | Restriction via existing `IsPLHomeomorphInto.mono_of_isPLCellOn`, or composition on its exact image | Must use the same map as clause 1. |
| 12 | Every moving vertex marker image avoids every Sp | Markers avoid support by old clause 12, hence are pointwise fixed | `eqOn_comp_of_disjoint_image`; no new marker position chosen. |
| 13 | Sp e avoids nonincident moving boundary CpBd w | Foreign-edge Sp d is disjoint from the support; invariant-set transport preserves avoidance | Nonincident vertices for e0 are unchanged. This condition concerns BOUNDARIES, not whole foreign cells. |
| 14 | Disjoint source Cp give disjoint image Cp | `disjoint_image_of_disjoint_support` if the unchanged foreign whole cell avoids support | Need whole-cell protection or a separate relative disjointness proof; boundary-only protection is insufficient. |
| 15 | Bb∩first Cp has one component containing all points outside Tp | Reuse for foreign edges after their Bb and relevant cell membership are protected | `NEW_THEORY`: connectedness of the exterior part after active cancellation must be proved from the cut/paste geometry. |
| 16 | Bb\first Cp has one component containing all points outside Tp | Same qualification as 15 | `NEW_THEORY`: the exterior component and its witness cannot be inferred from decreased circle count. |
| 17 | Positive count and EXACT annulus intersection equals union of Pg | Foreign annulus images and counts unchanged | `NEW_THEORY`: classify the complete new intersection, produce its finite enumeration and show 0<count'<count. No unlisted circles allowed. |
| 18 | Each Pg is a polyhedral circle in both open annuli | Foreign labels unchanged | New labelled circles require actual PL certificates and exclusion of all annulus ends. |
| 19 | Pairwise disjoint Pg labels | Foreign labels unchanged | Explicit local replacement must provide disjoint surviving/new circles; injectivity of an enum alone is not enough. |
| 20 | Atlas-local PL crossing at EVERY annular intersection point | Foreign annuli unchanged gives literal reuse | New crossings need actual maximal-atlas charts, or a relative chart-transport proof. Frozen assumptions contain no extra global HasGroupoid instance to add silently. |
| 21 | WHOLE Cp-overlaps for distinct edges are disjoint | `image_inter_disjoint_of_overlap_and_support` proves one side once support avoids the foreign overlap; preservation of foreign overlaps comes from `image_inter_eq_of_disjoint_support` | Exact whole-overlap support control is required. Annular-intersection disjointness or Sp disjointness alone does not establish it. |
| 22 | Fixed h(marker w) avoids every other moving Cp w' | Fixed markers lie in h(graph), which is disjoint from Sp e0 by clause 10; transport of intersections outside support preserves avoidance | Need the real source inclusion simplexBody(vertex)⊆graph; no epsilon estimate is available after repeated removal. |

## Current decision

`CURRENT_API`: one-vertex composition; support-invariant carrier containment; fixation of foreign
source tubes under the explicit common support certificate; preservation of intersections with
sets disjoint from support; connectedness propagation from an outside anchor. All corresponding
generic proofs are in the `ProtectedMove` namespace of `ControlledGraphNeighborhoodReduction.lean`.

`SMALL_NEW_LEMMA`: deriving the foreign whole-cell avoidance certificate from boundary avoidance,
connected tube, an active common point and the precise adjacency/whole-overlap alternatives.
This should be checked first, because it determines whether the proposed support condition is
actually derivable. Identifying the moved PL ball's ambient frontier also needs the exact existing
local chart assumptions, not a global groupoid upgrade.

`NEW_THEORY`: selecting a cancellation region with those protections, doing the disk/annulus
replacement with positive count decrease, proving the two active side-component conditions,
and extending the replacement to the whole Cc embedding with correct chartwise PL inverse.
These have NOT been packaged as an assertion that the desired output already exists.

The frozen step remains **PARTIAL / NOT ASSEMBLED** in this reduction. The already proved
`Section34CircleRemovalDescent.exists_section34ProtectedCircleRemoval_of_step` handles all count
iterations and the locally finite global process once the genuine one-step producer exists;
redoing its recursion would not address the present geometry gap.

A joint Lean fixture of the stronger common-support move is **UNTESTED**. A paper test should
start with two annuli in the same standard solid-torus chart having three intersection circles,
select a cancelling adjacent pair, add a third vertex cell outside the support but sharing a
neighboring source edge, and verify both whole-cell overlap conditions and cross-carrier tube
images. An isolated two-annulus picture does not test clauses 3, 14 or 21.

## Final private compilation

The parent task checked this exact source after its final edits. Lean exit code: 0;
source stable: true; authorized child-leaf sorry warnings: 3; other diagnostics: 0.
SHA256: c46fa298604f4388f6e644d084a4233f923562f1a67a97bc53d0fd339f1ded5f.

The receipt and raw log are at
C:\Users\liao9\AppData\Local\Temp\codex-moise-recon\DifferentialGeometry\Topology\PiecewiseLinear\Skeleton\ControlledGraphNeighborhoodReduction.json
and the adjacent .log file. The checker wrapper rejects all diagnostics, including authorized
skeleton warnings; the raw Lean result and exact warning set above were checked independently.
The consolidated axiom audit and the scope of partial reductions are recorded in
[RECON_FOUR_TARGETS_20260922.md](RECON_FOUR_TARGETS_20260922.md).