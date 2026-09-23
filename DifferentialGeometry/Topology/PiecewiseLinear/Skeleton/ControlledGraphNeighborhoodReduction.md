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

- `Section34Frame.lean:1090`'s `section34FaceTorus_subset_outerTorus` already gives chart-source
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
