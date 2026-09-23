# BP — Section 32 canonical tower and descent

Source review, 2026-09-23, `D:/differential-geometry-moise-int`,
`codex/moise-integration`, HEAD `c45b6faf19e693ae1134ba6f2656e71fbd0859d5`.
Paths are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`.
No probe or proof was run or changed. In particular, the collaborator-owned
Section 32 probe children remain untouched. Proposed names below are review
labels, not newly exported declarations.

The Section 32 docstring is stale about the lack of an `IsTube` inhabitant and
about `Moise303`, `Moise286`, and `Moise267` all remaining unproved: real source
producers now exist. Conversely, `moise308Nested` is **not a nested-torus existence
producer**: it proves inclusion-induced fundamental-group bijectivity for tori
and a spine already supplied. The fitted tori are nested between their own
inner/outer bounds, not nested with one another along the integer index;
`apart` actually makes non-neighboring outer tori disjoint.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_canonicalTower` | OK, provisional | The marked cylinder is bounded assembly; the joint controlled infinite outer family is new work, and PL fitting retains the explicit `Moise307` dependency. |
| `exists_descentSequence` | OK, provisional | Inputs fit the intended use, but coherent geometric transitions and preservation of already completed seams, not recursion, are the missing theory. |

These verdicts report no verified counterexample; they do not certify either
producer, a joint Lean fixture, or a transitive axiom closure.

## 1. Tower: statement, input suppliers and checks

The leaf asks for one map and one bi-infinite sequence whose every consecutive
triple is canonical. Its revolved annuli fill exactly the punctured splitting
disk; its outer tori stay in `W`, avoid `Z`, accumulate only at the marked center
on the negative end and the complete intrinsic rim on the positive end, and are
locally finite inside the two-ball interior away from the center.

In `moise322`, the consumer supplies `ht`, the actual edge and its two distinct
vertices, the pinned midpoint, and all five `W` conditions. `FreeFaceArc` supplies
compact connected `Bu`, `Bv`, disjoint from the image splitting disk, and containing
the respective vertices; their union supplies closed `Z`. Thus the tower also
avoids the vertices, a necessary input to the later separator. `h307` is an
explicit named input of `moise322`, not a consequence of the tube.

The extremes are meaningful: `W = ∅` cannot satisfy the disk-interior and midpoint
conditions; a whole two-ball union cannot satisfy the graph-intersection condition.
`Z` may be nonempty, even very close to the disk, but is closed and disjoint from
the compact disk. Shrinking widths solves that avoidance problem. Never replace
the intrinsic rim by the ambient frontier of the 2-disk. The two exact tail
closures exclude a constant/repeated finite configuration and the old pinched
single-end model. Negative indices must be included in the compatibility proof.

### The exact round-cylinder conversion

`TubeCenteredPrismCoordinates.IsTube.exists_centered_prism_coordinates` already
gives the **same** PL map

```text
ρ : stdSimplex R (Fin 3) × [-1,1]  →  C u ∪ C v
ρ(stdCenter 1,0) = midpoint,
ρ(Δ² × {0}) = D e,    ρ(∂Δ² × {0}) = Dbd e.
```

It also identifies both half-prisms with the respective balls. There is no need
to redo two-ball gluing or remark the center in this output.

Here is a specific topological model map. Let `b=(1/3,1/3,1/3)=stdCenter 1`, let
`V={q : R³ | Σ qᵢ=0}`, and choose a linear isometry `L : R² ≃ V`. The translated
triangle is `{q∈V | qᵢ≥-1/3}`. For a unit vector `v∈V`, put
`τ(v)=1/maxᵢ(-3vᵢ)>0`. Define

```text
κ(0)=b,
κ(z)=b + ‖z‖ τ(L(z/‖z‖)) L(z/‖z‖)     (z ≠ 0).
χ(x)=(κ(x₀,x₂), x₁).
```

Radial distance on each ray identifies the closed round disk with the triangle,
circle with triangle boundary, and zero with `b`; continuity at zero follows
from bounded radial lengths. `χ` sends the probe's exact cylinder
`x₀²+x₂²≤1 ∧ |x₁|≤1` to the triangular prism. Its middle disk and rim are the
probe's `meridianDisk` and `meridianRim`. Set `φ=h ∘ ρ ∘ χ` on the cylinder and
extend it arbitrarily off that closed domain. Restrict the tube embedding to
`C u ∪ C v`; compose the three embeddings and the three marked image equalities.
This gives precisely `DiskCoordinates`, with `φ 0=P'`.

For Lean, use Mathlib `Analysis/Convex/GaugeRescale` in the **two-dimensional
translated affine-hull model**, then transport back; its neighborhood hypotheses
would be false for the triangle as a subset of ambient `R³`. The map need only
be topological. Requiring the round cylinder to have a finite PL parametrization
would add a false category requirement. If using an arbitrary disk homeomorphism
instead of this centered one, center adjustment is needed once, via
`BallMarkedExtension`; the existing centered prism already removed that issue.

### A joint outer family, before any canonical fitting

Choose `rᵢ=2^i/(1+2^i)` for `i:Z`, using positive real integer powers, and
`Pt i=(rᵢ,0,0)`. These radii strictly increase from 0 to 1. In the meridian
half-plane set

```text
Dp i = [rᵢ-aᵢ, rᵢ₊₁+aᵢ] × [-bᵢ,bᵢ] × {0},
Dpint i = the corresponding open rectangle in that plane.
```

Choose positive `aᵢ,bᵢ` so that:

1. padded radial intervals stay in `(0,1)` and are disjoint whenever indices
   differ by at least two; choose pads below a fixed fraction of neighboring
   radial gaps;
2. adjacent rectangles overlap in a nondegenerate rectangle around their common
   endpoint, while the whole closed radial segment lies in the plane interior;
3. their revolutions lie in `cylinder` and map into
   `interior W ∩ interior (h '' C u ∪ h '' C v) ∩ Zᶜ`;
4. widths tend to zero at both ends, for example by also bounding them by
   a fraction of `min(rᵢ,1-rᵢ₊₁)`.

For item 3, each fixed closed annulus is compact and lies in the required open
set. Pull that set back by `DiskCoordinates`, take a neighborhood of the full
annulus, then a sufficiently thin revolved rectangle. The choice must control
**all angles**, not merely the meridian segment. Choose all widths against
neighbor-gap bounds at once; no infinite minimum is required.

Use `CanonicalConfiguration`'s convex rectangle/cell machinery,
`IsSpineRevolutionOfOfMemCellInterior`, and
`RevolutionOfCellInteriorSubsetInterior` to supply each `IsRevolvedTorusChain`.
Define `J`, `A`, `S`, `T` by their required revolution/frontier formulas. The
radial intervals partition `(0,1)`, giving `annuliEq` exactly.

For `closureLower`, escaping negative indices force both radius and height to
zero; conversely the annuli contain points approaching zero. For `closureUpper`,
escaping positive indices force radius to one and height to zero, and every
angle supplies a sequence converging to its rim point. Bounded-index subsequences
land in the finite union of compact tori. Transport these closure statements
through the homeomorphism on the **compact cylinder**. The rim lies on the
boundary of the two-ball union; therefore, on its interior away from `P'`, these
are no accumulation points. That proves local finiteness in the exact requested
ambient subspace. General position proves none of these tail statements.

### Fitted PL tori and the dependency boundary

The probe already has the right coherent mechanism: choose a fitted seed for
every `i`; keep every even seed; adjust each odd seed relative to its two even
neighbors using `ExistsGeneralPositionSolidTorusRelative`. Restrict this single
family to every triple. Choosing independent outputs of `moise311` for overlapping
triples would give no equality at shared indices.

`exists_fitting_annulus_image` uses
`InnerSolidTorusToroidalShell.exists_innerSolidTorus_toroidalShell_of_annulusImage`,
then **`h307`**, then `CombinatorialSolidTorusOfCylindricalDiagram`. Thus `Moise307`
is needed once per fitted seed in this route, not once per independently chosen
window. The source declaration

```lean
theorem moise307_of_moise252 (h252 : Moise252) : Moise307
```

is real in `Section30Torus.lean:202`; it is not unconditional. Searches of the
current PL tree found only conditional producers of `Moise252`, including
`LoopTheorem/CoverReductionOrientableProducer.moise252_of_lemmaTwoOrientable`.
The loop-theorem/descent input is not supplied by `Section30Separation`.
`moise303`, `moise286`, and `moise267` do have real producers in
`Section30Separation`, `Section28Annuli`, and `Section26ThreeSurfaces`.
The `Moise314` proof remains in the §31 skeleton and passes through its two
open polygon-carrier/linking leaves. Reading that proof does not remove them.

## 2. Descent: actual per-stage obligations

Mathematically this turns the alternating initial separator into a bi-infinite
annular chain, while providing a sequence of closed separators locally eventually
equal to that chain off the marked center. It is much larger than a finite-count
induction. The probe correctly calls itself a **partial stage probe**, not a
completed reduction of the descent leaf.

`htw` comes from the first leaf, `havoid` from its avoidance output, and `hcl`/`hsep`
from the now-real `InitialSurfaceSeparates`. The remaining four named propositions
are exactly the consumer's inputs described above. Nonempty vertex preimages are
provided by `IsTube.mem_interior_dualCell` and embedding/interior transport, not
by assuming the separated sets are nonempty. The actual pair interior is simply
connected through its two-ball/prism model; instantiate that before using
Phragmén–Brouwer.

An adequate finite geometric state records the modified **odd surface pieces**,
the fixed even tori, a finite triangulation on the current window, all actual
seam components and their labels, protected completed seams, and separation of
the vertices. Intersecting the whole separator with an even torus gives the
entire torus and is the wrong seam-count object.

| Stage | Producer that is still needed | Existing tool and its limit |
|---|---|---|
| Remove inessential seams | Select an innermost actual component, its two compatible disks and a neighborhood away from protected seams/vertices; obtain a replacement with fewer inessential components and the same state invariants. | `Moise303`, `SphereInnermostDisk`, `Section30Separation`: the split operation does not itself prove trace-count decrease or renewed finite surface structure. |
| Classify and delete Type 1 | After disk removal, classify components; prove a closed disjoint Type 1 component does not separate the two vertices, then delete it. | `Moise314` gives generator-or-disk for original canonical intersections; prove its classification is transported to the **modified** seams. `PhragmenBrouwer` needs the actual nonseparation and closedness certificates. |
| Delete returning Type 2 annuli | Produce the returning annulus and the two annuli cutting one even torus, with identical two-circle boundaries; identify the safe side and preserve separation when deleting the returning annulus interior. | `moise286`, `moise267`: the latter chooses some pair of three surfaces as a frontier; it does not choose the desired labelled pair or place its bounded region away from the vertices. |
| Delete redundant Type 3 bridges | Enumerate the finite complete bridge family, retain one, identify a redundant bridge whose deletion preserves separation and the protected seams. | Finite erasure/cardinality arithmetic only proves a count decreases **after** that geometric deletion is justified. |
| Select even-torus halves | Select one of the two complementary annuli at each even torus, coherently with the neighboring bridge ends and with separation preserved. | `Section28Annuli` and `LateralAnnulusLevels` recognize annuli; they do not choose the globally compatible retained half. |

For each finite window use phased natural-number measures: number of inessential
seams first; after that reaches zero, the numbers of unwanted Type 1 and returning
Type 2 components; then redundant Type 3 bridges; finally undecided half choices.
Later stages must not reintroduce earlier defects. If a unified lexicographic
rank is used, prove that fact for each transition rather than assuming the sum
strictly decreases. Finiteness is a hypothesis of the actual geometric state;
`Set.ncard` of an arbitrary infinite component set is not a valid measure.

Exhaust `I \ {P'}` by compact sets. For each compact set, local finiteness gives
a finite carrier window; enlarge it by neighboring indices for seams. Complete
all four stages and the half choice on that window, fixing a previously completed
inner region and its labelled interfaces. This **relative finite-window
normalization** is a genuine missing theorem, not an acceptable black-box
replacement for the whole endpoint. Its proof must be assembled from the five
local producers in the table. Dependent recursion then yields `M n`, beginning
with the exact `initialSurface`, all closed and separating and containing `P'`.

For a neighborhood meeting finitely many fixed carrier sets, take the maximum
of their stabilization times. The probe's
`locally_eventually_eq_iUnion_of_finite_support` proves the resulting equality of
sets on a neighborhood. Add the center and use
`isClosed_of_locally_eventually_eq_off_point` for closedness. Merely treating each
integer once, or convergence at individual points, is insufficient. Verify all
`IsAnnularChain` fields for the limit: exact end labels and meets, all three
disjointness assertions, containment in the fixed outer carriers, and both
fundamental-group surjectivity certificates.

### The three neighboring leaves: direction of use

The descent consumes **none** of them. The source assembly is:

```text
tower → initial separator → descent
      → SeparatesOfLocallyEventuallyEq
      → isOpenTopologicalCell_annularChain → pseudo-cell / Moise322.

IsPseudoCell → exists_generalPosition_ball_pseudoCell
            → exists_reducedDisk_of_crossesPseudoCell → Moise324.
```

Using the open-cell leaf to justify a surgery step on the still-unconstructed
annular chain would be circular. The general-position and reduced-disk leaves
are a separate 32.4 branch. Their existing probes were read only to check these
interfaces; no child was proved or edited.

## 3. Non-vacuity, Q6 and the largest risk

The Q6 note is correct that the finite standard three-cell configuration is not
a bi-infinite tower. Its claim about all its old open prerequisites must be read
historically: relative GP, inner shells, marked prism coordinates and a genuine
tube are now real source. The current standard configuration still takes
`h307`, and its finite number of sets supplies neither tail closure.

For a nonidentity joint geometric test use the genuine edge tube supplied by
`TubeOfGraphDualCells`, transport by an affine shear via `IsTube.of_isEmbedding`,
choose a small closed edge collar as `W` using `EdgeCollarFamily`, and choose
`Z=Bu ∪ Bv` from `FreeFaceArc`. Use the marked cylinder and the radial profile
above; `InitialSurfaceSeparates` then supplies the descent's separator inputs.
This is a constructive fixture recipe, not a checked full inhabitant in this
review. It tests nonempty graph data, both tails, a proper `W`, and nonempty
avoidance, rather than identity or empty-index specializations.

Even after `exists_controlled_revolved_tower` is proved, the current generic
fixture route still requires the cylinder conversion and `h307`; the finite
standard configuration does not remove either. An **unconditional specialized**
fixture could instead explicitly construct fitted polyhedral tori in the affine
sheared prism model, and then use the existing even/odd relative-GP argument.
That is an extra model-fitting proof, not a consequence of `moise308Nested` or
of the finite configuration alone. No unconditional fixture is claimed here.

The main surprise risk is preserving seam labels and generator information on
the evolving surfaces while freezing completed neighboring windows. The
original `Moise314` applies to the fixed canonical tori; one cannot repeatedly
apply it to arbitrary surgically modified surfaces without a transport theorem.

## Named reduction of each requested leaf

`SMALL` denotes bounded bookkeeping, `MEDIUM` a bounded geometric bridge, and
`NEW_THEORY` a substantial missing producer. Entries marked existing identify
reusable written layers, not new obligations or fresh compiler certification.

| Parent | Named sub-leaf | Size | Exact role and tree modules |
|---|---|---|---|
| Tower | `exists_centered_round_disk_to_simplex_homeomorph` | MEDIUM | Disk, rim and center simultaneously; Mathlib `Analysis.Convex.GaugeRescale`, `StdSimplexCone`, `BallMarkedExtension` if remarking an arbitrary chart. |
| Tower | `disk_coordinates_of_centered_prism` | SMALL | Compose `χ`, `ρ`, `h` on their actual domains; `SplitDiskCenter`, `TubeCenteredPrismCoordinates`, `PLHomeomorphTopology`. Together with the preceding child this discharges the existing coordinate sub-leaf. |
| Tower | `exists_bi_infinite_radial_profile` | SMALL | Strict radii with exact limits 0 and 1 and padded-gap bounds; real order/powers and `CanonicalConfiguration` rectangle vocabulary. |
| Tower | `exists_controlled_revolved_rectangles` | MEDIUM | Choose widths for all angles inside the pulled-back open set, prove all window cell/overlap/torus fields; `CanonicalConfiguration`, `IsSpineRevolutionOfOfMemCellInterior`, `RevolutionOfCellInteriorSubsetInterior`. |
| Tower | `revolved_tower_tail_closures` | MEDIUM | Exact lower/upper closures and local finiteness, then compact-cylinder transport; preceding two children, Mathlib compactness/closure APIs. Together these three radial children replace the substantial outer-family leaf. |
| Tower | `exists_fitted_PL_torus_family` | MEDIUM, existing conditional layer | One seed per integer; `InnerSolidTorusToroidalShell`, `Section30Torus` with an actual `Moise252` input if deriving `Moise307`, `CombinatorialSolidTorusOfCylindricalDiagram`. No unconditional source asserted. |
| Tower | `canonical_tower_of_adjacent_general_position` | SMALL, existing probe layer | Even/odd choice and restriction to all overlapping triples; `ExistsGeneralPositionSolidTorusRelative`, `PseudoCell`, existing `CanonicalTowerReduction` proof bodies, to be moved only by the owning lane. |
| Descent | `exists_finite_surface_state_on_tower_window` | MEDIUM | Actual compact PL odd pieces, finite seams and protected interfaces; `PseudoCell`, `CrossingTraceCircles`, `CanonicalConfiguration`. |
| Descent | `exists_innermost_split_with_fewer_null_traces` | NEW_THEORY | Exact geometric transition, relative to old seams; `Section30Separation`, `SphereInnermostDisk`, `SurfaceSplitAnnulus`, explicit `Moise314` input. |
| Descent | `exists_type_one_deletion_preserving_separator` | NEW_THEORY | Classify zero-generator component and prove nonseparation; `DifferentialGeometry.Topology.Connected.PhragmenBrouwer`, `TubeCenteredPrismCoordinates`, previous transition. |
| Descent | `exists_returning_annulus_deletion_preserving_separator` | NEW_THEORY | Two-circle gluing, specified safe side and deletion; `Section28Annuli`, `Section26ThreeSurfaces`, `Section30Separation`. |
| Descent | `exists_redundant_bridge_deletion_preserving_seams` | NEW_THEORY | Complete finite bridge list, one retained bridge, relative safe deletion; `Section28Annuli`, `Section26ThreeSurfaces`, `CanonicalConfiguration`. |
| Descent | `exists_compatible_even_torus_halves` | NEW_THEORY | Half selection and all chain meets/generators; `Section28Annuli`, `LateralAnnulusLevels`, `Moise308Nested` only where its actual inputs are available. |
| Descent | `exists_relative_normalization_of_finite_tower_window` | NEW_THEORY | Prove the above stages jointly preserve completed inner windows; depends on the five geometric children, not on a future global chain. |
| Descent | `exists_stabilizing_separator_sequence` | SMALL after geometric children | Dependent recursion, phased finite termination and locally finite cutoff maximum; the existing generic `CanonicalTowerReduction` lemmas. |
| Descent | `annular_chain_invariants_of_stabilized_surgery` | MEDIUM | Identify the limit with the exact `H/B` union, prove closedness and every named chain field; `PseudoCell`, `AnnularChainLocalPolyhedral`, stabilized transition certificates. Limit separation is subsequently supplied by `SeparatesOfLocallyEventuallyEq`. |
