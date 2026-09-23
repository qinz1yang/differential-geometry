# Controlled canonical towers and the Section 32 descent

Reconnaissance only, 2026-09-22. This file accompanies
`CanonicalTowerReduction.lean`. Nothing is accepted, promoted, imported into the aggregate,
or entered as progress in `FREE_INPUTS.md` by this probe. No compilation was run by its author;
the parent task coordinates private checking. The new leaf statements are **UNREVIEWED**.

The tower is a complete conditional reduction with two child `sorry`s. The descent is a
**partial stage probe**, not a completed reduction of `exists_descentSequence`: four concrete
transition relations and their available operations are exposed, but the suppliers connecting
those operations on one evolving geometric state are still missing. In particular, this file
does not replace that gap with a full-window or full-sequence existence oracle.

## Source identity and scope

Read the current source at initial checkout
`0642f2e7deaa33a527f3c08fe058b08ff0ee0187`, not the older state in the handoff.

| Source | SHA256 at reconnaissance |
|---|---|
| `Skeleton/Section32PseudoCell.lean` | `47D9496B0154F0A38AAFEF484B65E14710E3FAB745AA08C54D6D0D61B9F7C53A` |
| `PseudoCell.lean` | `DBBAE168D92D250E219C49CC776DE15B65A7689C840E35073033F76083B3B8DE` |
| `CanonicalConfiguration.lean` | `E26CC35F7E14835347F096F1F01FBACFAD2450A2B1BA6A74AA4A3916285C1155` |
| `ExistsGeneralPositionSolidTorusRelative.lean` | `88EEA94BE977B25B8020A05D9E87AA88C20E69E36217B0192F5F51F179578011` |
| `InnerSolidTorusToroidalShell.lean` | `CB4FACEB7FB6671B48C4A5BC3F78C811A820A55461B9E5887A7149D371A6E352` |
| `CombinatorialSolidTorusOfCylindricalDiagram.lean` | `95F4FCA940308BA2A519A370824459359BA65893CF94E58FE23EEDC982D80378` |

Existing mathematical vocabulary is imported from real modules. No Skeleton is imported and
no copied declaration shadows `Fits`, `PairGP`, `IsCanonicalTower`, or `IsAnnularChain`.
New declarations are isolated in
`DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerReduction`.
The tower endpoint reproduces the frozen parameters and conclusion, within that namespace.

Reviews consulted: AD, AK, AM, AQ. Their mathematical design is evidence. Their older
availability claims are not the current source inventory: relative general position, the
inner-shell producer, the cylindrical-diagram-to-CST bridge, the initial separator, and an
`IsTube` inhabitant now all have real source modules.

## Tower: what the reduction actually proves

The choices are ordered as follows.

1. `exists_splitDisk_cylinder_coordinates` fixes one map `φ`, a topological embedding of the
   closed unit cylinder onto the two-cell union. Its middle disk, rim, and center map to the
   actual splitting disk, its rim, and `P'`.
2. `exists_controlled_revolved_tower` chooses all source data against this same `φ`. Every
   consecutive triple is an `IsRevolvedTorusChain`, embedded by `φ`. The outer images obey
   all the separation, avoidance, lower/upper closure, and local-finiteness conditions.
3. `exists_fitting_annulus_image` uses the existing inner shell, `Moise307`, and the existing
   cylindrical-diagram/CST bridge. It supplies one seed torus per integer. It does not call
   `moise311` independently on overlapping triples.
4. `exists_adjacent_generalPosition_family` chooses all seeds `R i`, keeps `R (2*k)`, and
   chooses `Q k` relative to `![R (2*k), R (2*k+2)]`. The total family is defined using integer
   quotient and remainder. Both parities, including negative indices, are handled in the
   proof. `PairGP.symm` supplies the even-to-odd orientation.
5. `ControlledRevolvedTower.exists_canonicalTower` restricts that **one family** to each
   triple, sets `T'' i = frontier (S'' i)`, and copies the unchanged outer control.

| Child leaf or implemented layer | Classification | What remains |
|---|---|---|
| `exists_splitDisk_cylinder_coordinates` | **SMALL_NEW_LEMMA** (relative assembly; unproved here) | Existing boundary-disk extension and two-ball gluing supply the main PL machinery. Still assemble a simultaneous parametrization fixing the common disk and its distinguished midpoint, then use a topological cylinder model and transport through the tube embedding. The statement is topological, not a demand that the round cylinder have a finite PL parametrization. |
| `exists_controlled_revolved_tower` | **NEW_THEORY** | A joint bi-infinite radial exhaustion and sufficiently thin planar neighborhoods, with exact two tail closures. The outer neighborhoods must satisfy the prescribed `W`, `Z` avoidance, and local finiteness simultaneously. |
| `exists_fitting_solidTorus`, `exists_fitting_annulus_image` | **CURRENT_API**, assembly written | Explicit dependence on `Moise307` is retained. No new approximation theorem or extra ambient continuity of `φ` is assumed. |
| `exists_adjacent_generalPosition_family` | **SMALL_NEW_LEMMA**, proof written | Choice and integer parity only; relative GP is already supplied by the real module. |
| Triple restriction and frozen tower endpoint | **SMALL_NEW_LEMMA**, proof written | Assembly only, pending checker confirmation. |

The second open leaf is deliberately still substantial. Its next useful internal split is
an explicit radius profile tending to `0` and `1`, then thickness selection subordinate to
the inverse images of the prescribed open neighborhoods. The chosen radii must first carry
the annular exhaustion; a theorem giving only an abstract locally finite family of open sets
would not supply the revolved-cell overlap or the two exact closure equations.

All ambient control belongs to the outer sets `φ '' S i`. General position supplies none of
`apart`, `closureLower`, `closureUpper`, or `locallyFinite`. The probe preserves them rather
than rederiving them from the inner family. The avoidance conclusion is read from the very
same controlled outer tower. The map is `φ` throughout; it is never silently identified with
the tube's original `h`.

Relevant current APIs:

- `InnerSolidTorusToroidalShell.lean:66`,
  `IsTopologicalSolidTorus.exists_toroidalShell_of_isCompact_subset_interior`.
- `InnerSolidTorusToroidalShell.lean:315`,
  `exists_innerSolidTorus_toroidalShell_of_annulusImage`.
- `CombinatorialSolidTorusOfCylindricalDiagram.lean:306`,
  `isCombinatorialSolidTorus_of_hasCylindricalDiagram`.
- `ExistsGeneralPositionSolidTorusRelative.lean:342`,
  `exists_generalPosition_solidTorus_relative`.
- `PseudoCell.lean:540`, `IsCanonicalTower`; every field is retained.
- `SphericalDiskExtension.lean:59`,
  `exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex`, extends the **same prescribed**
  disk map over each ball; `BallGluing.lean:11` shows the compatible pasting pattern and
  `BallGluing.lean:48` proves the union is a ball. This is why the relative coordinate
  leaf is assembly work over current APIs, rather than a new Schoenflies theory. The round
  cylinder conversion and distinguished midpoint still need explicit proofs.

## Descent: actual objects modified by each stage

Use the original tower's `S''`, `T''` and outer carriers `φ '' S`. Initially the even tori stay
whole and the odd surfaces are clipped outside the even interiors, exactly as
`initialSurface` in `PseudoCell.lean:559` defines. The evolving odd pieces need their own
carrier variable `L`; intersecting the entire separator with an even torus would return the
whole torus and would not count seam curves.

`traceCircles L T` is the set of actual connected components of `L ∩ T` which are PL circles.
`boundsDiskIn G T` uses a PL parametrization of a disk and its **intrinsic** boundary.
`nullTraceCount L T` is the cardinal of the inessential trace components. Its use requires
the explicit finiteness premises in `IsInnermostSplitStep`; `Set.ncard` of an infinite set
must never be interpreted as a finite geometric complexity.

The four step relations are specifications, not existence theorems. Each pins the actual
post-operation set and the protected seam set `F`. They do not take a future global annular
chain as input.

| Stage | Actual change and available operation | Missing supplier / classification |
|---|---|---|
| Innermost disk splitting | `IsInnermostSplitStep` pins `C' = T ∪ L'`, retains `T`, requires strict `nullTraceCount` decrease, and preserves the old separator on `F`. `exists_disk_split_preserving_seams` consumes the complete `Moise303` input and proves the protected-seam conclusion from `F ∩ Ω = ∅`. | **NEW_THEORY:** select an actual innermost seam; construct the two disks sharing it with `hnear`; choose `Ω` off protected seams and vertices; prove the replacement is again a finite PL surface arrangement and that the count of actual inessential traces drops. The existing 30.3 output alone does not state any trace-count decrease. |
| Delete Type 1 | `IsTypeOneDeletion` deletes a whole closed component `C`, retaining `R`; `separates_after_delete_type_one` is the Phragmén–Brouwer step. | **NEW_THEORY:** from the normalized odd surface, produce the closed disjoint component decomposition and prove that the zero-generator component does not separate the two vertices. Supply simple connectedness of the actual interior cell pair. These are not hypotheses of the frozen endpoint. |
| Delete Type 2 | `IsTypeTwoDeletion` records the returning annulus `C`, two annuli `B₀,B₁` covering one fixed even torus, exact common seams, and deletion of `C \ (J₀ ∪ J₁)`. `exists_type_two_bounded_side` consumes the full nonempty-boundary `Moise267` interface. | **NEW_THEORY:** jointly triangulate the three actual annuli with identical intrinsic boundary, identify which two form the relevant frontier, exclude both vertices from the bounded region using the controlled carrier, then prove that deleting the third annulus preserves separation. The 26.7 conclusion alone neither labels the desired pair nor gives that relative carrier control. |
| Delete redundant Type 3 bridges | `IsTypeThreeDeletion` fixes an actual finite family of bridging annuli and a surviving `keep`; the deleted set is the intrinsic interior of `discard`. `finite_bridge_count_decreases` proves that erasing a different label retains `keep` and strictly decreases cardinality. | **NEW_THEORY:** construct a finite complete list of bridging components and find a redundant one whose deletion preserves separation and protected seams. Merely counting a supplied finite list proves no topological deletion property. |

`exists_annular_component_of_essential_seams` is the existing `Moise286` consumer for an
actual complement component. It provides two distinct endpoint labels; no assertion that
their numerical labels are consecutive is made. It supplies annulus recognition **after**
all inessential seams have been removed, not the preceding classification by itself.

`delete_preserves_protected_seams` is a proved set identity once the deleted open annulus is
disjoint from `F`. It does not prove closedness or preservation of separation.

After the four stages there is still the separate half-torus selection: the two surviving
seams cut each even torus into two annuli, exactly one must be removed while preserving
separation, and the retained halves must match the neighboring bridge labels. This is the
source of `halfInterBridge`, `bridgeInterHalf`, and all three disjointness fields of
`IsAnnularChain` (`PseudoCell.lean:562`). It cannot be supplied by the bridge-cardinality
lemma. The `loGenerator` and `hiGenerator` clauses must also survive every replacement.

## Termination and scheduling: what is already implemented

The following generic results have proof bodies in the probe and no new `sorry`.

- `exists_terminal_of_strict_finite_rank`: genuine strong induction on the natural rank,
  producing a finite `Relation.ReflTransGen` path to a terminal state. The actual geometric
  rank and its strict decrease must be supplied by each finite stage above.
- `exists_compatible_sequence`: dependent recursion from a one-step producer preserving
  `valid n`. This is not yet instantiated to geometric surgery states.
- `locally_eventually_eq_iUnion_of_finite_support`: when each actual local piece eventually
  stops changing and all pieces remain inside a fixed locally finite carrier family, one
  common stabilization time works on a neighborhood. The proof takes the finite maximum
  of the individual cutoff times. It proves local equality, not just pointwise convergence.
- `isClosed_of_locally_eventually_eq_off_point`: the locally stabilized limit is closed if
  every approximant is closed and the only exceptional center is already included.

**Classification:** these are **SMALL_NEW_LEMMA** assemblies, written for checking now.
They isolate the analytic and combinatorial endgame from the missing geometric transition
theory. The existing `SeparatesOfLocallyEventuallyEq.lean:17` supplies separation of the limit
once the frozen endpoint's local eventual equality and closedness are available.

For a correct schedule, every finite neighborhood away from `P'` must eventually finish all
four stages and the half-torus deletion. Finishing stage 1 at every integer while postponing
all later stages forever does not qualify. Nor is it safe to finish all stages independently
at a single integer before choosing neighboring seams. A geometric state invariant must
record protected seams and the finite dependency neighborhood before the recursion above
can be instantiated. A generic integer enumeration by itself proves no compatibility.

Consequently **`exists_descentSequence` is not re-proved in this file**. Its unchanged frozen
statement remains in `Section32PseudoCell.lean`. Supplying a leaf that returned an arbitrary
coherent family of finite normalized windows would merely relocate this missing theory;
the probe intentionally does not claim that as a successful reduction.

## Feasibility decision and fixtures

The tower is substantially closer than the old notes suggest: the single-torus PL producer
and the relative perturbation are real inputs today. The relative disk-pair model should be
an assembly task over existing disk extension and ball gluing. The sizeable new tower
construction is the controlled infinite outer exhaustion. Parity and coherent triple
restriction are ordinary implementation work already written here.

For the descent, do not allocate a worker to “the countable choice step.” Allocate a
geometric invariant design task first: finite PL odd-surface pieces with actual boundary
components, the generator/disk dichotomy supplied by `Moise314`, protected seam labels, and
the exact disk-splitting and annulus-deletion operations. That invariant must supply the
four producer hypotheses in the table on the same tuple. This is new theory, even though
30.3, 28.6, 26.7 and the generic finite/infinite scheduling tools can then be reused.

`TubeOfGraphDualCells.lean:312` now provides an `IsTube` inhabitant, unlike the old AK/AM
snapshot. This does not constitute a joint Lean fixture for either new tower leaf. A
mathematical test model is a one-edge dual-cell tube, a cylinder parametrization of its
cell pair, radii tending to zero and one, and narrow rectangular source cells. Transport by
a non-affine embedding, prescribe a genuinely smaller `W`, and take a nonempty closed
obstacle `Z` disjoint from the disk. Test the negative as well as positive tower indices.

For descent, the same fixture additionally needs an inessential trace circle and explicit
Type 1, returning Type 2, and redundant Type 3 pieces. A returning annulus has **two** common
boundary components; imposing connected common boundary would invalidate the intended use
of 26.7. No such joint Lean surgery fixture was constructed here. All new geometric
interfaces remain **UNTESTED** and subject to review before freezing.

## Final private compilation

The parent task checked this exact source after its final edits. Lean exit code: 0;
source stable: true; authorized child-leaf sorry warnings: 2; other diagnostics: 0.
SHA256: f402c9cdb20349317716d909d765ab0d78a77f335502a1da3ff1a123786a6190.

The receipt and raw log are at
C:\Users\liao9\AppData\Local\Temp\codex-moise-recon\DifferentialGeometry\Topology\PiecewiseLinear\Skeleton\CanonicalTowerReduction.json
and the adjacent .log file. The checker wrapper rejects all diagnostics, including authorized
skeleton warnings; the raw Lean result and exact warning set above were checked independently.
The consolidated axiom audit and the scope of partial reductions are recorded in
[RECON_FOUR_TARGETS_20260922.md](RECON_FOUR_TARGETS_20260922.md).