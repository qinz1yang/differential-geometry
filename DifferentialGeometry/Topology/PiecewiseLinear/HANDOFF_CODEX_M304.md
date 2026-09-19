# Spherical-shell proof lane

Current author-verified endpoint (2026-09-19 UTC): `Moise252 -> Moise304`,
followed by the existing `Moise305Tame` consumer. This remains conditional on
Moise252 and awaits independent integration acceptance. The dated sections
below retain earlier proof frontiers; the final section records current evidence.

## Scope and source (2026-09-19 UTC)

The owner explicitly added this single independent lane until 14:19 UTC.
The clean starting point was cbfe4a73f5c5074805cc4db729f8fed5146322ef,
on codex/moise-304 in the ef23 worktree. E3 retains the actual 30.3
splitting geometry. This lane does not edit MoiseChain or the other lanes'
owned source and does not create subagents.

The complete proof of Moise 30.4 is on printed page 216, PDF index 225.
The preceding 30.3 is on page 215. The annular-neighborhood input 28.19
is on page 209. The proof constructs an initial connected separating
surface, compresses using 26.4, uses 28.19 and 30.3 to preserve the
geometric separation, and descends in the first Betti number. The general
wild-cell complement problem is not an extra input to the accepted tame
30.5 consumer. None of 26.4, 28.19, or the complete 30.4 is asserted here.

## Constructed compact-set separators (2026-09-19 UTC)

`Connected/SeparatorLocation.lean` proves three general topological results:
`separates_frontier`, `Separates.inter_nonempty_of_isPreconnected`, and
`Separates.subset_interior_of_disjoint_frontier`. The last result supplies
the exact justification for placing a connected separator inside a
connected shell when it avoids that shell's frontier.

`SeparatingSurface.lean` proves
`exists_isCombinatorialManifoldWithBoundary_neighborhood` in every positive
finite dimension and `exists_connected_separating_surface` in dimension
three. The latter takes a compact connected set A, a disjoint closed
connected set B, and any open neighborhood U of A. It actually constructs
a finite, connected, orientable, two-sided closed combinatorial surface
inside U separating A and B. It encloses A in a finite simplex, refines
an actual derived neighborhood inside U minus B, identifies its frontier,
and selects a genuine separating connected boundary component. There is
no assumed separator, triangulated neighborhood, or equivalent conclusion.

Both new modules compile with zero diagnostics through the M304 leased
checker; all five nonautomatic declarations and ten critical reused
declarations pass the transitive axiom audit, with only propext,
Classical.choice, and Quot.sound. All 13 applicable environment linters
pass. A concrete closed unit ball / radius-three sphere instance constructs
a separating surface inside the radius-two open ball. The final silent
audit took 45.809 seconds including admission. The individual source-check
wall totals were not persisted; the first completed in 7.849 seconds and
the second completed after the command yielded. An earlier external-model
attempt used two unqualified Metric names and was corrected; no source
proof failure remains. The first surface-signature attempt omitted the
local Finite instance required by IsOrientable; the final existential
explicitly installs the constructed finite-face proof.

Verification files are outside the project at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/` and private objects at
`C:/Users/liao9/AppData/Local/Temp/codex-moise-304-20260919/lib/`.
The audit source is `AuditSeparatingSurface.lean` and the full declaration
census is `separating-surface-census.json`. Frozen receipt and source copies
are retained in `separator-checkpoint/`. Shared E: artifacts are read-only.
Both leaves are registered in the flat root. The owner-stopped full-root
build was not restarted; independent integration/root acceptance remains
separate from these focused checks.

The first dependency-closed checkpoint is
f0f7bd699f9c0313c74af2f716b4778acf9ebdd1, pushed on codex/moise-304.

## Spherical-shell geometry (2026-09-19 UTC)

`ClosedBall/AnnulusHomeomorph.lean` constructs the radial homeomorphism
between the unit sphere times a closed positive radial interval and the
closed norm band. Its inverse laws reuse `homeomorphUnitSphereProd`.
It proves the norm band's compactness and exact interior.
`ClosedBall/AnnulusImage.lean` uses invariance of domain to identify the
interior and frontier of every embedded spherical cylinder, and constructs
the actual homeomorphism from the open cylinder onto that interior.

`SphericalShell.lean` now derives compactness, connectedness and disjointness
of the shell and its two boundary spheres, the exact frontier formula,
and simple connectivity of its interior. The interior proof transports
the open-cylinder homeomorphism and the proved contraction of the interval
factor. It also constructs the standard concentric norm-band shell.
`IsSphericalShell.exists_connected_separating_surface` takes only an actual
spherical shell and produces a finite, connected, orientable, two-sided
closed combinatorial surface inside its interior separating the boundary
spheres. This is an initial separating surface, not a PL sphere or 30.4.

All three new modules compile with zero diagnostics. Successful final
module checks took 14.691, 22.348 and 17.091 seconds respectively, including
admission. The final silent audit took 45.555 seconds including admission.
All 24 nonautomatic declarations, ten reused entries and three concrete
radial-shell models have only the usual foundational axioms; all 13
applicable environment linters pass. The models check an actual interior
separator, simple connectivity of the open norm band, and its frontier.
All leaves are registered in the flat root. Evidence is frozen outside
the project in `moise304-reading/spherical-shell-checkpoint/`, including
source snapshots, the census, receipts, private object hashes and exact
source hashes. No root build or shared artifact write was performed.

The disconnected compression paragraph on printed page 216 gives the
correct weak inequality: the new first Betti number is at most the old
number minus two, hence strictly smaller than the old number. An earlier
text-extraction reading incorrectly reported a strict inequality in the
book. Enlarged inspection of the printed formula confirms the weak
inequality; the earlier report of a book error is withdrawn.

The spherical-shell checkpoint is
0289bdaf43bb4f8447fb4c19ac20c319448ba35b, pushed on codex/moise-304.

## Finite ambient nullhomotopies (2026-09-19 UTC)

`FundamentalGroup/SimplyConnected.lean` proves that a path-connected space
is simply connected exactly when its fundamental group at any chosen
basepoint is trivial. Its contrapositive produces a nontrivial element at
that basepoint. The proof uses the existing change-of-basepoint equivalence
and the nullhomotopy characterization of simple connectivity.

`NullhomotopyNeighborhood.lean` solves the finite-ambient obligation in the
compression argument. Given a compact subset S of an open U and an element
g of its fundamental group whose image in U is trivial, it chooses an
actual representative loop and nullhomotopy. It captures S together with
that homotopy's compact image in a finite full-dimensional combinatorial
manifold neighborhood N contained in U. It reconstructs the relative
endpoint homotopy in N, proving that g is still killed there. Simple
connectivity of U gives the corresponding corollary without assuming a
nullhomotopy or a neighborhood.

`SurfaceCompression.lean` applies this construction to any connected finite
closed combinatorial surface which is not a PL sphere, inside a simply
connected open set. At any chosen basepoint it produces a nontrivial group
element and a finite ambient manifold N, with the surface disjoint from
N's combinatorial boundary and the inclusion killing that element. It
uses the previously proved PL-sphere recognition from simple connectivity.
Neither Moise264 nor a compressing disk is assumed or claimed by this
producer. These are the actual finite-environment inputs required by 26.4.

The three source modules pass zero-diagnostic focused checks in 7.747,
11.715 and 11.650 seconds respectively, including admission. The concrete
audit model takes the complex unit circle, proves its fundamental group
nontrivial using the existing integer equivalence, and constructs a finite
planar manifold neighborhood inside the radius-two disk killing an actual
nontrivial element. This checks the construction beyond the trivial loop.
The final silent audit took 47.693 seconds including admission, with zero
diagnostics. All five new declarations, nine reused entries and two concrete
models have only standard foundational axioms. All 13 applicable environment
linters pass. The audit source, census, source snapshots, receipts and object
hashes are frozen in `moise304-reading/nullhomotopy-neighborhood-checkpoint/`.
Earlier external-model errors concerned TypeTag lemma namespaces and sphere
membership notation; those were corrected. No source proof debt remains.

Next: the actual annular neighborhood of a polygonal circle in an orientable
surface. The existing derived-cell construction and two-dimensional disk
gluing are available; the cyclic decomposition's dimension restriction
must be removed naturally and its current consumers rechecked. The
compressing-disk theorem 26.4, annular-neighborhood construction 28.19,
E3's actual 30.3 splitting geometry and strict Betti descent remain distinct
obligations before the PL-sphere endpoint can be claimed.

## Cyclic surface neighborhoods and prescribed boundary arcs (2026-09-19 UTC)

The cyclic derived-cell construction now works in every ambient dimension
at least two. The existing three-dimensional ball-chain signatures are
preserved. Their proofs and the new two-dimensional disk-chain theorems
share the same finite-chain induction, instantiated with the existing
proved gluing theorems. A surface circle's derived neighborhood is actually
decomposed into two PL disks meeting in two disjoint PL arcs, with both arcs
in the combinatorial boundaries of both disks.

`IntervalHomeomorph.lean` constructs endpoint-preserving PL maps taking a
specified interior subinterval to another. `CircleArcPair.lean` transports
this construction through the complementary arc of a PL circle: one arc
can be held pointwise fixed while another disjoint arc is moved. Together
with the existing one-arc extension and boundary extension, it constructs
circle and disk maps prescribing the first arc pointwise and the second
arc as a set. `RectangleArcPair.lean` gives rectangle parametrizations of
disks with those two opposite boundary arcs. `IntervalCylinder.lean` glues
the two actual parametrizations. The endpoint
`exists_cylindricalDiagram_Icc_derivedNeighborhood_circle` in
`SurfaceCircleNeighborhood.lean` constructs an interval-fiber cylindrical
diagram directly from a finite polygonal circle in a surface.

This layer does not assume a disk-pair decomposition, rectangular charts or
a cylindrical diagram in the neighborhood endpoint. The private shared
inductions are instantiated by proved lower gluing operations. The output
still allows a reversing end map. Excluding the Mobius case by orientability,
straightening the end map and obtaining the annulus remain the next layer.
No core-preserving annular parametrization, spanning-disk compatibility,
full 28.19 or 30.4 is claimed here.

All seven mathematical modules compile with zero diagnostics. Final check
times including admission were 22.230 seconds for BallChain, 71.021 for
NeighborhoodCycle, 11.042 for IntervalHomeomorph, 12.331 for CircleArcPair,
12.624 for RectangleArcPair, 11.799 for IntervalCylinder and 11.790 for
SurfaceCircleNeighborhood. All five direct existing consumers were also
checked: ArcDerivedNeighborhood (27.676), BallCyclePair (11.490),
PolygonCircleParametrization (11.751), NeighborhoodSolidTorus (11.452) and
NeighborhoodCylinder (12.632). Two consumers only needed existing long
lines wrapped. The twelve missing unchanged dependencies of the solid-torus
consumer were reused from the accepted ninth integration batch after
independent receipt, object-hash, raw-source and normalized-source checks.
Original and rebound receipts retain that provenance in the private output.

The silent final audit took 47.735 seconds including admission. It checks
all 28 nonautomatic declarations in the seven mathematical modules,
including retained declarations, ten critical reused producers and three
concrete models. The models construct a nontrivial interval-subarc move, a
rectangle with prescribed opposite arcs and the cyclic disk decomposition
and cylindrical diagram around the actual boundary of the unit square.
Only standard foundational axioms occur; all 13 applicable environment
linters pass. Early external-model errors concerned numeral types and
decidable-instance selection and have been corrected. All five new leaves
are registered in the flat root. Evidence, source snapshots, object hashes,
receipts and the dependency-reuse manifest are frozen outside the project
in `moise304-reading/circle-neighborhood-checkpoint/`. The full root build
remains stopped by the owner's instruction; no shared artifact was written.

## Annular neighborhoods in orientable surfaces (2026-09-19 UTC)

`IntervalMonodromy.lean` classifies the interval end map by its endpoints.
A reversing end map produces an actual PL homeomorphism from the finite
Mobius complex onto the cylindrical diagram's entire image. The existing
non-embedding theorem excludes that case inside an orientable surface.
The endpoint-fixing case is straightened using an actual PL square
extension, producing a cylindrical diagram with equal ends.

`AnnulusCylinder.lean` constructs the standard interval cylindrical diagram
onto `stdSimplexBoundary 2` times `[0,1]`. Its exact fibers and the existing
diagram comparison produce the annulus PL homeomorphism, with the full
parameter equation when the given ends agree. The orientable-surface
corollary obtains this homeomorphism without assuming a trivial end map.

`SurfaceCircleNeighborhood.lean` applies this classification to the actual
derived neighborhood of a finite polygonal circle. The new
`exists_annular_neighborhood` also starts with any PL circle S in a finite
orientable combinatorial surface K and any open U containing S. It refines
K compatibly with S and uses a sufficiently small mesh to construct a
finite combinatorial surface N contained in K and U, which is a relative
neighborhood of every point of S and is PL homeomorphic to the standard
annulus. Neither a disk-pair decomposition, cylindrical diagram, annulus,
nor an end-map condition is an input to this neighborhood endpoint.

This is the actual annulus-shape and neighborhood-control result for the
orientable surfaces used by the spherical-shell argument. It does not yet
identify S with the central circle under the annular parametrization or
construct the compatible traces with a spanning disk. Full 28.19 in a
possibly nonorientable surface, 26.4, E3's 30.3 geometry and the Betti descent
remain separate obligations; 30.4 is not claimed.

All three modules pass zero-diagnostic focused checks: IntervalMonodromy
11.795 seconds, AnnulusCylinder 11.550 seconds and the final
SurfaceCircleNeighborhood 11.191 seconds, including admission. The initial
small-neighborhood proof needed the explicit finite-face theorem for the
derived neighborhood; the corrected proof passes. The silent audit took
69.996 seconds including admission. All 12 nonautomatic declarations in
the three modules, 12 critical reused entries and three concrete models
have only standard foundational axioms; all 13 applicable environment
linters pass. The models check the standard annulus with the parameter
equation, the derived neighborhood of the unit square's boundary, and an
annular neighborhood of that boundary in every positive metric thickening.

The two new leaves are registered in the flat root. Exact source snapshots,
raw and normalized hashes, private objects, receipts and the silent census
are frozen in `moise304-reading/annular-neighborhood-checkpoint/`. This is
scoped verification: the owner-stopped root build remains stopped, and no
shared E: artifact was modified.

## Bicollars fixing the original surface circle (2026-09-19 UTC)

`SphericalCircleExtension.lean` extends any given PL homeomorphism between
polygonal circles in two PL two-spheres to a PL homeomorphism of the whole
spheres. The proof uses the actual complementary disk decompositions and
existing disk-map extensions. `PrismSphere.lean` identifies the boundary
of a disk prism as an actual PL two-sphere, with the exact end and side sets.

`SphericalCircleBicollar.lean` constructs a PL bicollar of any polygonal
circle J in a PL two-sphere S, inside any set U that is a relative
neighborhood of J. It extends the prescribed middle-circle map from a
standard prism sphere, shrinks the interval by compactness, and proves the
image is a relative neighborhood. Its parametrization satisfies
`rho (x, 0) = x` for every x in J.

`NeighborhoodEmbedding.lean` proves that a PL embedding maps a neighborhood
of an interior point of a finite combinatorial manifold to a neighborhood
in a same-dimensional finite combinatorial manifold. It constructs a small
PL ball, uses boundary invariance, and excludes the closure of the target
complement. The source neighborhood is not required to lie in the source
manifold. A closed-source corollary removes the boundary exclusion.

`SurfaceCircleBicollar.lean` combines these producers with the previously
constructed annular neighborhood. For an orientable finite combinatorial
surface K, a PL circle J in K disjoint from its boundary, and any relative
neighborhood U of J, it constructs a polyhedron W in the interior of K and
in U, a relative neighborhood of J, and an actual PL homeomorphism
`rho : J times [-1,1] -> W` fixing J at height zero. The closed-surface
corollary needs no boundary hypothesis. The proof transports the original
circle into the annulus model, proves it has a neighborhood there, collars
it in the model sphere, and transports back. No preexisting core marking,
bicollar or spanning disk is assumed.

All five modules compile with zero diagnostics. Final times including
admission were 16.069 seconds for SphericalCircleExtension, 11.084 for
PrismSphere, 11.891 for SphericalCircleBicollar, 10.930 for
NeighborhoodEmbedding and 12.034 for SurfaceCircleBicollar. The final silent
audit took 47.407 seconds. All seven new declarations, 12 critical reused
entries and three concrete models have only standard foundational axioms;
all 13 applicable environment linters pass. The models extend a map between
two distinct latitude circles in a prism sphere, construct a narrow
bicollar of its middle circle using the general closed-surface endpoint,
and collar the boundary of an inner square inside a larger square disk,
within every positive metric thickening. Initial external-model errors in
set rewriting were corrected; no source proof debt remains.

All five new leaves are registered in the flat root. Sources, raw and
normalized hashes, objects, receipts and audit census are frozen in
`moise304-reading/circle-bicollar-checkpoint/`. The owner-stopped root build
remains stopped. The next mathematical step is attaching the two halves
of this bicollar to a given spanning disk to obtain actual larger PL disks.
Full nonorientable 28.19, the compressing-disk producer 26.4, E3's regular
neighborhood splitting and strict Betti descent remain open; this is not
a completion claim for 30.4.

## Actual larger disks from a spanning disk (2026-09-19 UTC)

`PrismDiskBoundary.lean` proves that the intrinsic boundary of the bottom
and sides of a PL disk prism is exactly its top circle. This is proved for
every PL disk parametrization by identifying the closure of its complement
in the prism boundary sphere. `DiskBoundaryCollar.lean` then glues an actual
boundary collar onto a disk and produces a parametrization of the larger
PL disk. Its boundary is exactly the far end of the collar, and is disjoint
from the original disk.

`DiskBoundaryBicollar.lean` applies that construction to both halves of a
given bicollar, reversing the interval on one side. It proves that the two
larger disks meet exactly in the original disk and that their union is the
original disk together with the full bicollar. Both intrinsic boundary
circles are the corresponding outer-end images. The exact collar-disk
intersection and the pointwise middle-circle equation are used throughout.

The main producers are the two
`IsCombinatorialManifoldWithBoundary.exists_disk_pair_of_spanning_disk` and
`IsCombinatorialManifold.exists_disk_pair_of_spanning_disk` declarations in
`SurfaceSpanningDisk.lean`. For an orientable finite combinatorial surface K,
an actual disk parametrization r with `D intersect K.space = r '' boundary`,
and an arbitrary relative neighborhood U of that circle, they construct
actual sets D1, D2 and PL disk parametrizations q1, q2. They prove:

- D lies in each Di minus its intrinsic boundary `qi '' stdSimplexBoundary 2`;
- D1 intersects D2 exactly in D;
- each Di lies in `D union (K.space intersect U)`;
- D1 union D2 is a relative neighborhood of D in `K.space union D`.

The version with a surface boundary additionally requires the spanning
circle to avoid that boundary. Neither version assumes a collar or a pair
of larger disks. The boundary exclusion is intrinsic; it is not a statement
about the interior of a two-dimensional disk in a three-dimensional space.

All four modules compile with zero diagnostics. Final times including
admission were 27.519 seconds for PrismDiskBoundary, 10.996 for
DiskBoundaryCollar, 28.082 for DiskBoundaryBicollar and 11.024 for
SurfaceSpanningDisk. The final silent audit took 46.876 seconds. All five
new declarations, ten critical reused entries and three concrete models
have only standard foundational axioms; all 13 applicable environment
linters pass. The models check the exact boundary of a capped standard
prism, the two explicit halves around its middle disk, and the complete
surface producer for a spanning disk in a prism sphere within every positive
height strip. Initial external-model errors in decidable-instance selection
and image rewriting were corrected. No source proof debt remains.

All four leaves are registered in the flat root. Sources, raw and normalized
hashes, private objects, receipts and the silent census are frozen in
`moise304-reading/spanning-disk-checkpoint/`. The full root build remains
stopped by the owner, and no shared E: artifact was written.

The identified E3 consumer is
`IsCombinatorialManifoldWithBoundary.exists_isSubdivision_disk_pair_with_derivedNeighborhood_endpoint_disk`
in `SurfaceSplitEndpointDisk.lean:920` at E3 commit `22ccb6c8d`.
It takes a three-dimensional ambient complex K3, separate from the
two-dimensional surface K above. Given `D subset K3.space` and
`K.space subset K3.space`, our output supplies its two larger PL disks,
the two inclusions from D, the exact intersection, and both ambient
inclusions. Its requested relative neighborhood of D in K3 is a separate
input. This instantiation has been checked against the source signature,
but has not been compiled: the coordinator confirmed that independently
accepted artifacts for the E3 leaf and its pending dependency repair are
not yet available. No E3 source or author-private object was copied.

The next obligations remain the essential-circle obstruction needed in
Betti descent, the actual compressing-disk producer 26.4, E3's subsequent
splitting geometry, and the final induction. This checkpoint does not
claim the full theorem 30.4.

## Disk extraction and nullhomotopies from spherical cappings (2026-09-19 UTC)

`BallHomotopy.lean` proves that every PL ball is contractible and constructs
a nullhomotopy of any inclusion factoring through a PL ball. Its cylinder
theorem starts with a continuous map of J times [0,1] into S, fixes J at
height zero, and assumes the height-one image lies in a PL ball contained
in S. It constructs the homotopy explicitly and concludes that the
inclusion J into S is nullhomotopic. The cylinder is only required to be
continuous; injectivity and a PL parametrization are not needed.

`DiskCapping.lean` proves
`IsPLSphere.exists_isPLHomeomorphOn_of_union_disk`: if A union D is a PL
two-sphere, D has a PL disk parametrization r, and A intersect D is exactly
`r '' stdSimplexBoundary 2`, then A has an actual disk parametrization q
with the same boundary image. It does not assume A is closed or polyhedral;
these follow by identifying A with the closure of the sphere minus D.
The inclusion of this boundary into any set containing A is therefore
nullhomotopic. A further theorem transports A by a given PL homeomorphism
and uses a given continuous cylinder from J into that transported disk to
nullhomotope J in the original ambient set.

This supplies an obstruction to a spherical capped component when the
original circle inclusion is non-nullhomotopic, as required by 26.4.
The capping, exact boundary intersection, PL return map and cylinder are
actual mathematical inputs to these lemmas. They still need to be produced
for the eventual split surface; this layer does not claim those geometric
inputs, component exclusion, or the completed Betti descent.

Both modules pass zero-diagnostic focused checks: BallHomotopy 9.900 seconds
and DiskCapping 10.650 seconds including admission. The silent final audit
took 44.511 seconds. All six declarations, ten critical reused entries and
three concrete models have only standard foundational axioms, and all 13
applicable linters pass. The models contract the boundary of the unit
square through the square, recover the top disk from a capped prism sphere
with its exact boundary, and explicitly contract the bottom circle along
the prism side into that recovered top disk. Initial external-model syntax
and set-normalization errors were corrected. No proof debt remains.

Both leaves are registered in the flat root. Source snapshots, raw and
normalized hashes, object files, receipts and audit census are frozen in
`moise304-reading/disk-capping-checkpoint/`. The owner-stopped root build
remains stopped, and no shared E: artifact was written.

## Betti formulas for actual split-and-cap data (2026-09-19 UTC)

`SurfaceSplitBetti.lean` adds four corollaries of the existing proved
`SurfaceSplitAndCap.eulerChar_eq_add_two`. The source is a finite connected
orientable closed combinatorial surface. If the actual result is also
connected and orientable, its first Betti number plus two equals the
source's first Betti number, hence it is strictly smaller. If the result's
faces are the disjoint union of two connected orientable closed surfaces,
their first Betti numbers sum to the source's first Betti number. If neither
component is a PL sphere, sphere recognition and the Euler-Betti formula
make both Betti numbers positive, so each is strictly smaller than the
source's.

These statements consume the actual split-and-cap structure, manifold,
orientation, connectedness and face-decomposition data. No Euler equality
or Betti inequality is assumed. The non-spherical component hypotheses
still need to come from the geometric capping obstruction. The two-component
strict inequality proved here is sufficient for natural-number descent;
this layer does not claim the book's stronger bound of a decrease by at
least two in each component.

The module compiles with zero diagnostics in 11.173 seconds including
admission. Its final silent audit takes 56.595 seconds: all four declarations
and five critical reused entries have only standard foundational axioms,
and all 13 applicable linters pass. No new geometric model is claimed for
these conditional corollaries; their verification is compilation, statement
review, the full transitive axiom audit and the standard linter suite.
The new leaf is registered in the flat root. Source and object snapshots,
raw and normalized hashes, receipts and census are frozen in
`moise304-reading/surface-split-betti-checkpoint/`. The root build remains
stopped and no shared artifact was written.

## Complementary components of surface circles (2026-09-19 UTC)

`Connected/BicollarSeparation.lean` proves that the images of the negative
and positive half intervals of a bicollar are connected, disjoint, cover
the bicollar minus its core, and both accumulate on the whole core. This
first result requires only a topological space, a connected core and a
continuous bijection fixing the core; compactness and separation axioms
are unnecessary. In a locally connected, preconnected ambient set, a
closed core with such a relative bicollar has at most two complementary
components. If the ambient set is closed and the complement is not
preconnected, there are exactly two components: their closures cover the
ambient set and meet exactly in the core.

`SurfaceCircleComplement.lean` constructs the required bicollar for each
PL circle in a finite connected orientable combinatorial surface, then
applies these topological results. It gives both the at-most-two and
separating-circle conclusions, for closed surfaces and for circles avoiding
the boundary of surfaces with boundary. The two representatives in the
at-most-two conclusion may represent the same component. The separating
versions produce actual disjoint nonempty components and exact closure
equations; they do not assume a two-component decomposition.

Both modules compile with zero diagnostics: BicollarSeparation 8.511 seconds
and SurfaceCircleComplement 11.252 seconds including admission. The final
silent audit takes 47.886 seconds. All eight declarations, including the
private local-separation lemma, eight critical reused entries and three
concrete models have only standard foundational axioms. All 13 applicable
environment linters pass. The models cover an unbounded straight core in
the plane, the actual separating middle circle of a prism sphere (with
separation proved by the height intermediate-value theorem), and the inner
square circle inside a square disk. Initial external-model elaboration
and style errors were corrected; no proof debt remains.

Both leaves are registered in the flat root. Sources, raw and normalized
hashes, objects, receipts and the census are frozen in
`moise304-reading/circle-complement-checkpoint/`. The root build remains
stopped. These are actual two-dimensional complement results. The local
manifold structure of the closures, the eventual capped components,
compression via 26.4, and the full 30.4 endpoint remain separate obligations.

## Interval and disk monodromy name compatibility (2026-09-19 UTC)

The integration audit at `1e691da48917bc2418c8310e45e0cc33f261645a`
found a genuine shared-name collision with the previously accepted
two-dimensional disk-fiber theorem in `CylindricalClassification.lean`.
The interval-fiber declaration in `IntervalMonodromy.lean` is now named
`IsCylindricalDiagram.exists_endMap_id_of_isOrientable_interval`; its one
consumer in `AnnulusCylinder.lean` uses the new name. The existing disk
declaration and its consumers retain their public names.

This lane independently recompiled the two changed modules and the four
downstream modules SurfaceCircleNeighborhood, SurfaceCircleBicollar,
SurfaceSpanningDisk and SurfaceCircleComplement, all with zero diagnostics
(12.102, 11.989, 11.532, 12.179, 12.180 and 11.319 seconds respectively).
The annular-neighborhood audit was rerun while also importing the existing
SolidTorusProduct chain, so both theorem families coexist in one environment.
All 12 declarations, 12 critical reused entries, three geometric models
and 13 linters pass, with only standard foundational axioms and zero
diagnostics in 48.010 seconds. Evidence is frozen in
`moise304-reading/interval-name-checkpoint/`. The root build stays stopped.

## Manifold closures and exact boundaries of circle complements (2026-09-19 UTC)

`BicollarDiskPair.lean` constructs a local PL disk around every point of a
circle bicollar. The disk minus the circle has two actual components. Each
component closure is a PL disk, the two closures cover the neighborhood,
and their intersection is precisely its trace on the circle, a PL arc.
The construction takes a small PL arc in the core and maps its product
with the full, negative and positive intervals through the given bicollar.
Connectedness, closure equations and component identities are all proved.

`Connected/ComponentNeighborhood.lean` gains the natural purely topological
neighborhood statement away from a closed deleted set in a locally connected
ambient set. The existing local-component neighborhood theorem keeps its
signature and proof. The two pre-existing consumers SurfaceComponentClosure
and SurfaceFilling were recompiled without source changes.

The main endpoints are
`IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_separating_circle`
and `IsCombinatorialManifold.exists_manifold_pair_of_separating_circle` in
`CircleComponentClosure.lean`. For a PL circle separating a connected
orientable finite surface, they produce two finite connected orientable
combinatorial surfaces with boundary. Their carriers are the closures of
actual complementary components, their union is the source surface, and
their intersection is the original circle. In a closed source surface,
both new boundaries are exactly that circle. For an interior circle in a
surface with boundary, each new boundary is the circle union the part of
the original boundary contained in that component closure. Neither the
manifold property nor these boundary equations are hypotheses.

The three source modules compile with zero diagnostics: ComponentNeighborhood
6.375 seconds, BicollarDiskPair 12.657 seconds, and CircleComponentClosure
22.333 seconds including admission. The final silent audit takes 49.146
seconds. All eight declarations in these modules (seven new, including
three private helpers, and one retained declaration), ten critical reused
entries and three concrete models have only standard foundational axioms.
All 13 applicable environment linters pass. Models verify the local disk
pair in the standard annulus, both manifold closures of the middle circle
in a prism sphere, and the exact inherited boundary formula for an inner
square circle in a square disk. Initial external-model decidable-instance
and line-length errors were corrected. The two old consumer checks pass
in 11.429 and 11.109 seconds with zero diagnostics.

Both new leaves are registered in the flat root. Raw and normalized source
identities, objects, receipts, the audit source and census are frozen in
`moise304-reading/circle-component-closure-checkpoint/`. The root build
remains stopped and shared artifacts remain untouched. This closes the
actual separating-circle component-closure obligation in dimension two.
Attaching caps, proving their closed-manifold structure and descent,
compression via 26.4, E3's separation-preserving geometry and the full
30.4 endpoint remain open.

## Gluing along entire boundaries (2026-09-19 UTC)

`SphereGluing.lean` proves `isPLSphere_union_of_isPLBall`: two finite
PL n-balls meeting exactly in
both entire intrinsic boundaries have a PL n-sphere as their actual union.
The statement includes dimension zero. In positive dimension the proof
extends the common boundary map across one ball and transports the existing
double construction to the actual union.

`BoundaryGluing.lean` proves `isCombinatorialManifold_unionComplex` in every
dimension, with no orientability or connectedness assumptions. At common
boundary vertices the two ball links glue to a sphere; other vertices retain
their original spherical links. `isCombinatorialManifold_of_space_eq_union`
allows any finite triangulation of the union, and
`exists_isCombinatorialManifold_space_union` constructs one. These statements
take the two actual manifold pieces and their exact entire-boundary overlap;
the resulting closed-manifold structure is proved, not supplied.

`ComplexUnion.lean` supplies realizations of compatible intersections,
intersection and union links, and a common finite triangulation whose
restrictions subdivide each original complex. This last construction
handles distinct carriers and does not assume matching triangulations.

All eight new declarations in the three modules compile with zero diagnostics.
Final checks take 10.007 seconds for ComplexUnion, 10.429 for SphereGluing,
and 10.262 for BoundaryGluing, including admission. The silent audit takes
45.727 seconds: eight declarations, ten critical reused entries, three
geometric models and all 13 applicable environment linters pass, with only
standard foundational axioms. The models cover two distinct points forming
a zero-sphere, the two explicit hemispheres of standard simplex boundaries
in every positive dimension, and two overlapping intervals with an exact
intersection carrier. External-model instance, arithmetic and import issues
were repaired before the passing audit.

All three leaves are registered in the flat root. Evidence is frozen in
`moise304-reading/boundary-gluing-checkpoint/`, including raw and normalized
source identities, private objects, receipts, audit source and census.
No existing public signature changed. The root build remains stopped and
shared artifacts remain untouched. Instantiation on the actual separating
circle components, their cap Euler identities and strict descent are next;
26.4 compression, E3's separation-preserving geometry and full 30.4 remain open.

## Actual separating-circle cappings and strict descent (2026-09-19 UTC)

`ManifoldCapping.lean` constructs a closed manifold by attaching an actual
parametrized ball along the entire boundary of a finite combinatorial
manifold. It applies in every positive dimension. `EulerUnion.lean` proves
Euler additivity for actual polyhedral unions and intersections over every
field, without assuming compatible input triangulations, and exposes the
corresponding finite-complex carrier formulas.

`IsCombinatorialManifold.exists_capped_pair_of_separating_circle` in
`SurfaceCapping.lean` starts with a finite connected orientable closed
surface, an actual spanning PL disk whose boundary is its exact intersection
with that surface, and separation of the surface by this circle. It
constructs two finite connected closed surfaces. Each is the actual closure
of one complementary component union the original disk; the two caps meet
exactly in that disk and cover the source-surface/disk union. The proof
constructs the component closures, applies entire-boundary gluing, and proves
that the sum of the two Euler characteristics is the source Euler
characteristic plus two. None of the capped manifolds or this Euler equation
is supplied as an input.

`IsCombinatorialManifold.exists_capped_pair_of_separating_essential_circle`
in `SurfaceCappingBetti.lean` specializes to ambient dimension three and a
non-nullhomotopic boundary inclusion, exactly as in the 26.4 disk contract.
It produces orientable closed connected caps P and Q, proves that neither
is a PL sphere, proves `bettiOne P.space + bettiOne Q.space = bettiOne K.space`,
and proves strict descent for both. If a cap were spherical, the actual
disk-complement theorem would contract the original circle in the original
surface. The already checked sphere-recognition and surface-homology
theorems then give positive Betti number for each cap and the strict drops.
No quantitative drop of two for each separated component is asserted here.

The four modules compile with zero diagnostics in 10.058, 10.139, 11.835
and 10.849 seconds, respectively, including admission. The final silent
audit takes 86.152 seconds. All six new declarations, eleven critical reused
entries and three geometric models have only standard foundational axioms;
all 13 applicable environment linters pass. The models cap an explicit
standard simplex hemisphere in every positive dimension, cap both sides
of the middle disk of a cube boundary, and compute Euler additivity for
overlapping intervals. The cube model produces two closed connected surfaces
with zero first Betti numbers and Euler sum four; its circle is inessential,
so it is a test of the actual cap producer rather than a nontrivial example
of the strict essential-circle theorem. External-model namespace and line
length issues were corrected before the passing audit.

All four leaves are registered in the flat root. Frozen source identities,
private objects, receipts, audit and census are under
`moise304-reading/surface-capping-checkpoint/`. The root build stays stopped
and shared artifacts remain untouched. These raw caps share the original
disk: they are not a claim of E3's disjoint pushed surfaces or of preservation
of the original separating property. Nonseparating-circle compression,
26.4 production, E3's separation step and full 30.4 remain open.

## Shared closed-cover connectedness lemma (2026-09-19 UTC)

`Topology.isPreconnected_left_of_isClosed_union` in `Connected/ClosedCover.lean`
proves that a closed set A is preconnected when A union B and A intersection B
are preconnected and B is closed. There is no nonemptiness assumption and no
connectedness assumption on B. The existing complementary-component theorem
is unchanged. The required source headers are added and the existing leaf is
explicitly registered in the flat aggregate.

The integration owner identified simultaneous F-lane work on the same result
and assigned this existing natural topic home as the sole public producer.
This dependency is delivered independently of the in-progress circle-arc and
surface-complement leaves. Source compilation takes 6.232 seconds; the final
silent audit takes 15.747 seconds. Both module declarations, six critical
reused declarations and four models have only standard foundational axioms;
all 13 applicable environment linters pass, with zero diagnostics. The models
cover an interval attachment, the empty-set case, two disjoint attachments,
and the preserved component API on two separated intervals. The initial
external audit's long-line warning was corrected before the passing run.

Frozen evidence is under `moise304-reading/closed-cover-checkpoint/`. The root
build remains stopped by the owner; no shared artifacts were modified.

## Actual complements of surface regions (2026-09-19 UTC)

`CircleArcComplement.lean` proves that the closure of the complement of any
PL closed arc contained in a PL circle is a PL arc. It reuses the existing
canonical planar parametrization and planar cut-pair theorem and transports
the actual complementary arc back to the original ambient space.

`SurfaceSubcomplexComplement.lean` proves that the generated complement of a
two-dimensional manifold-with-boundary subcomplex in a closed combinatorial
surface is a manifold with boundary. The local proof uses the actual
complementary vertex links. A common-subdivision producer then constructs a
finite manifold whose carrier is exactly the closure of the set difference,
and whose boundary carrier is exactly the original region's boundary. The
subcomplex theorem does not require a separate finite-faces hypothesis on
the subcomplex; an unused such hypothesis was removed after the first audit.

The two leaves compile without diagnostics in 10.844 and 11.294 seconds.
The final silent audit takes 46.479 seconds and checks all three new
declarations, both retained ClosedCover declarations, nine key reused entries
and three models. The models remove the bottom edge of a square boundary,
remove the bottom cap of a cube boundary while checking the exact boundary,
and remove two disjoint closed attachments. All 13 applicable environment
linters pass and all axiom closures contain only standard foundational
axioms. Both leaves are registered in the flat aggregate. Frozen evidence is
under `moise304-reading/surface-complement-checkpoint/`.

These are actual complement producers, not a completed nonseparating-circle
compression: the annulus boundary, connected core and subsequent caps still
need to be assembled. The root build remains stopped and shared artifacts
remain untouched.


## Connected complements of nonseparating annuli (2026-09-19 UTC)

`CurvePrism.lean` constructs manifold products of finite curves with intervals
and identifies their actual boundary carriers, including curves with boundary.
`AnnulusComplement.lean` constructs a finite annulus and its complementary
surface from an actual embedded PL circle-times-interval map. Both boundary
carriers and their intersection are exactly the two endpoint circles.

`Connected/BicollarComplement.lean` proves the general topological connectedness
step from a compact connected core, an actual bicollar and preconnectedness of
the complement of its middle core. It uses two closed-cover removals. The
Euler union API gains disjoint-union additivity, and `AnnulusEuler.lean` proves
that deleting an actual annulus preserves the Euler characteristic.

`IsCombinatorialManifold.exists_connected_annulus_complement` in
`SurfaceAnnulusComplement.lean` now constructs the actual finite connected
orientable surface with boundary obtained from a nonseparating circle in a
closed orientable surface. The annulus can lie in any prescribed relative
neighborhood. The theorem retains the actual bicollar map, its fixed middle
circle, the exact closed complement, both disjoint PL boundary circles, and
the equation that the Euler characteristic is unchanged.

The six changed modules compile without diagnostics in 11.498, 11.111,
8.383, 10.016, 11.774 and 12.123 seconds including admission. The final silent
audit takes 186.473 seconds. All twelve declarations in those modules (nine
new and three retained), twelve critical reused entries and three models have
only standard foundational axioms, and all 13 applicable linters pass. The
models verify a rectangle's four-edge boundary, the disconnected two-cap
complement of the vertical annulus on a cube boundary with Euler characteristic
two, and the connected complement of a point bicollar in a square boundary.
The last model is one-dimensional, not a nonseparating torus example. Two
external-model elaboration errors were corrected before the passing audit.

All five new leaves are registered in the flat root. Frozen source identities,
private artifacts, receipts, audit and census are under
`moise304-reading/annulus-complement-checkpoint/`. The root build remains stopped
by the owner; shared artifacts are untouched. Disjoint cap construction and
their attachment remain the next layer. This is not yet the full nonseparating
compression or 30.4, and does not assert preservation of ambient separation.


## Disjoint caps and exact nonseparating Betti descent (2026-09-19 UTC)

`ComplexUnion.lean` gains the actual link equalities at a nonempty face absent
from one summand. `ManifoldDisjointUnion.lean` proves manifold-with-boundary
closure under disjoint union in every dimension, including zero, together
with exact boundary face and carrier formulas. These results require neither
finite-dimensional ambient space nor finite complexes; the finite realization
corollary assumes only finite faces. A private face-disjointness lemma is
included in the audit.

`ManifoldCapping.lean` now constructs a closed manifold by attaching two actual
disjoint PL balls along their whole boundaries; it retains the original
single-ball API. `SurfaceBoundaryCapping.lean` specializes to a connected
surface with two boundary circles and constructs a finite closed connected
surface with Euler characteristic increased by two. Neither the final
manifold nor its Euler equation is a supplied hypothesis.

`IsCombinatorialManifold.exists_capped_annulus_complement` in
`AnnulusCapping.lean` consumes an actual annulus decomposition of a closed
connected surface in ambient dimension three, a connected complementary
surface, and two actual disjoint disk caps with exact intersection and
endpoint-boundary equations. It produces the closed connected orientable
capped surface, proves its Euler characteristic is the source value plus two,
and proves `bettiOne result + 2 = bettiOne source` and strict descent. The
annulus Euler equation is derived from the actual geometric decomposition.
The cap existence and separation-preserving geometric push remain inputs
for the E3 integration; disks sharing the original spanning disk do not
satisfy the disjointness hypothesis.

All five changed modules compile with zero diagnostics in 10.615, 9.972,
10.355, 9.706 and 11.428 seconds including admission. BoundaryGluing,
EulerUnion and the existing separating-circle capping consumers are also
freshly rechecked. The final silent audit takes 48.002 seconds and checks all
15 module declarations (ten new, including one private, and five retained),
ten critical reused entries, four geometric models and four explicit local
instances. All 13 applicable linters pass; all axiom closures contain only
standard foundational axioms; the final run has zero diagnostics. Models
cover two distinct points, two separated intervals with their exact boundary
and Euler characteristic, the cube's side annulus capped by its two disjoint
horizontal disks, and the retained simplex-hemisphere cap in every positive
dimension. The cube model produces a connected closed surface with Euler
two and first Betti number zero. It tests the cap producer, not a nontrivial
source-torus instance of the annulus Betti theorem. External zero-dimensional
model elaboration and one line-width warning were repaired before the final
passing audit; the five mathematical sources needed no repair.

All three new leaves are registered in the flat aggregate. Frozen identities,
objects, receipts, models and audit are under
`moise304-reading/annulus-capping-checkpoint/`. The root build remains stopped;
shared artifacts are unchanged. Actual essential disk production, disjoint
cap geometry, ambient separation preservation and the final 30.4 induction
are still not claimed complete.


## Common annulus and spanning-disk data (2026-09-19 UTC)

`SurfaceAnnulusComplement.lean` now exposes
`IsCombinatorialManifold.exists_annulus_complement_of_isOrientable` for any
PL circle in a closed orientable surface. The actual annulus, finite
orientable complement, exact boundary circles and Euler equation are retained
without assuming nonseparation. Nonseparation implies connectedness of that
same produced complement. The prior connected-complement theorem keeps its
exact signature and is a corollary.

`SurfaceSpanningDisk.lean` factors the disk-enlargement construction through
`exists_disk_pair_of_spanning_disk_of_bicollar`, valid for a closed ambient
set and an actual spanning disk with a supplied bicollar. It preserves both
half-annulus carrier equations, both endpoint boundary equations, the exact
shared original disk, and the relative-neighborhood conclusion. Both existing
manifold spanning-disk signatures remain unchanged.

`IsCombinatorialManifold.exists_annulus_complement_of_spanning_disk` in
`SpanningDiskAnnulus.lean` assembles those constructions using the same annulus
and bicollar map. It produces the finite complement R and actual enlarged
disks D0 and D1, proves R misses the original disk, proves R intersects each
Di exactly in its own boundary, and identifies the entire boundary of R with
the two endpoint circles. The original disk lies in both parameterized open
simplex images. The carrier equation `R union D0 union D1 = K union D`, the
arbitrarily small prescribed control and the relative neighborhood required
by the E3 input all hold for these same witnesses. D0 and D1 still intersect
in the original disk; no disjointness of these enlarged disks is claimed.

The three modules compile with zero diagnostics in 11.343, 11.666 and 12.090
seconds including admission. The final silent audit takes 49.477 seconds:
six native declarations (three new and three retained), ten critical reused
entries, three geometric models, one retained conditional consumer and two
explicit local instances. All 13 applicable linters pass and all axiom
closures contain only standard foundational axioms. The new prism model
checks exact cap-boundary intersections and small-neighborhood control, and
proves that its complementary surface is disconnected with Euler two. The
other geometric models replay the old bicollar pair and the old small
spanning-disk API. The conditional consumer tests the old nonseparating
interface; it is not counted as a geometric example. One set-union lemma
name and two external-model line widths were repaired before the passing
checks. All three old public signatures are compared textually to the prior
checkpoint and are unchanged.

The new leaf is registered in the flat root. Frozen sources, private objects,
receipts, audit and census are under
`moise304-reading/spanning-disk-annulus-checkpoint/`. This supplies consistent
actual witnesses for the later local split construction. The geometric push
to disjoint caps, ambient separation transfer and full 30.4 remain open; root
builds remain stopped and shared artifacts were not modified.

## Components of annulus complements (2026-09-19 UTC)

The canonical `Connected/ClosedCover.lean` now proves the component
intersection formula for a closed cover with preconnected overlap, without
separation or finite-dimensional assumptions. `Connected/BicollarComplement.lean`
uses it to identify each component of the closed annulus complement with
the corresponding component of the circle complement intersected with that
closed complement. Every circle-complement component meets the closed
complement. Connectedness is therefore equivalent, and a bicollar in a
connected locally connected space gives at most two complementary components.
The prior nonseparating-complement signature is unchanged.

`ComponentComplex.lean` now proves equality of geometric links for arbitrary
nonempty faces in a component, and restriction formulas for the boundary
complex and its carrier in every dimension, including zero. These formulas
require neither finite dimensionality nor a manifold hypothesis. The existing
vertex-link theorem is a corollary. Required headers and two old line widths
were repaired while preserving the old public signatures.

`AnnulusComponents.lean` constructs two actual finite connected disjoint
surface complexes from a separating annulus complement. They cover the same
given complement, and their entire boundaries are respectively the negative
and positive endpoint circles of the given bicollar. The source complex is
only required to be finite and preconnected; the complement supplies the
surface-with-boundary hypothesis. Closed-cover connectedness rules out both
end circles lying in one component, so the endpoint assignment is proved.

All four changed modules compile without diagnostics. Four existing consumers
are freshly rechecked. The silent audit takes 50.934 seconds including admission
and covers 28 native declarations (11 new, including one private), 12 reused
entries, six actual models, one retained conditional consumer and three
explicit local instances. All 13 applicable linters pass and all axiom closures
contain only standard foundational axioms. The new cube model constructs the
two disjoint complementary surface complexes and proves their exact opposite
boundary circles; the retained point bicollar, interval and empty-set models
check the topological interfaces. Three external-model elaboration failures
were repaired before the final passing audit.

The new leaf is registered in the flat root. Frozen source identities, objects,
receipts and the complete audit are under
`moise304-reading/annulus-components-checkpoint/`. Root builds remain stopped
and shared artifacts are unchanged. Disjoint cap production, preservation of
ambient separation and the final 30.4 induction remain open.

## Disjoint separating caps and strict Betti descent (2026-09-19 UTC)

`SurfaceBoundaryCapping.lean` now constructs a finite connected closed surface
from one actual disk capping its entire boundary, with Euler increment one.
It also caps two disjoint connected surfaces by two actual disjoint disks,
proves the results remain disjoint, retains their exact carriers, and proves
the sum of Euler characteristics increases by two. Cross-intersections are
excluded using the complete boundary and union-intersection equations.

`IsCombinatorialManifold.exists_capped_pair_of_separating_essential_annulus`
in `AnnulusCapping.lean` obtains the actual complementary components and
applies this cap construction. The two finite connected closed surfaces are
disjoint and orientable in ambient dimension three. If either were a sphere,
its disk complement together with the corresponding half-annulus would
nullhomotope the original circle inclusion, contradicting the essential-circle
hypothesis. Thus both are nonspheres. Their Euler sum is the original Euler
characteristic plus two, their first Betti numbers sum to the original first
Betti number, and each is strictly smaller. The exact resulting union is
`R union D0 union D1`. No decrease by two for each separate component is claimed.

Both changed modules compile with zero diagnostics; AnnulusCapping takes
14.272 seconds including admission. The final silent audit takes 48.159
seconds and checks five native declarations (three new and two retained),
13 reused entries, three actual geometric models and four explicit local
instances. All 13 applicable linters pass, all transitive axiom closures are
standard, and the final audit emits zero diagnostics. The new model attaches
two disjoint bottom-and-side prism disks to two distinct horizontal square
disks. The resulting actual carriers are disjoint cube boundaries, each with
Euler two and first Betti number zero. The old connected annulus with two caps
and the simplex-hemisphere model in every positive dimension also pass. These
are geometric capping tests; no explicit essential separating genus-two
surface model is claimed.

Both prior public signatures are unchanged. Frozen sources, receipts, objects,
audit and census are under
`moise304-reading/separating-annulus-capping-checkpoint/`. The actual disjoint
caps and separation-preserving geometric push remain inputs from E3; the
30.4 induction is still open. Root builds remain stopped and shared outputs
are unchanged.

## A smaller connected separator after annulus capping (2026-09-19 UTC)

`SurfaceCompression.lean` now proves
`IsCombinatorialManifold.exists_separating_surface_bettiOne_lt_of_annulus_capping`.
Given an actual essential circle, its actual annulus decomposition, actual
disjoint disk caps, and separation by their resulting union, it produces a
finite connected orientable two-sided closed surface contained in that union,
separating the same preconnected target sets, with strictly smaller first
Betti number. The proof covers both circle-complement cases. In the connected
case it uses the connected capped surface; in the separating case the actual
disjoint capped pair and Phragmen-Brouwer select a separating member. The
separation hypothesis is on the given geometric union, not on a purported
already-produced smaller surface.

The source check takes 11.050 seconds including admission with zero diagnostics.
The final silent audit takes 52.876 seconds and checks both native declarations,
ten critical reused entries and three concrete probes: the circle's nontrivial
fundamental group, its actual finite ambient neighborhood killing a nontrivial
loop, and selection of the effective separator from two separated real points.
All 13 applicable linters pass and all axiom closures are standard. Two
external-model inequality elaborations were repaired before the passing audit.
The original nontrivial-kernel neighborhood signature remains unchanged.

Frozen evidence is under `moise304-reading/surface-compression-checkpoint/`.
This is the proved compression consumer of concrete annulus and cap geometry;
it does not produce the essential spanning disk or the disjoint caps and does
not establish their union's separation. The root build remains stopped and
shared outputs are unchanged. Full 30.4 remains open.

## Actual separators of minimal first Betti number (2026-09-19 UTC)

`SeparatingSurface.lean` now constructs a finite connected orientable two-sided
closed surface of minimal first Betti number among the finite connected closed
surface separators in the given open region. It starts from the existing
actual compact-set separator construction and minimizes its natural-number
Betti value. No nonempty family or compression conclusion is introduced as a
new external hypothesis.

`IsSphericalShell.subset_interior_of_separates` states the general location
fact for any preconnected separator of the two shell boundary components.
The existing shell surface producer uses it with its unchanged signature.
`IsSphericalShell.exists_connected_separating_surface_bettiOne_min` produces
an actual finite connected orientable two-sided separator inside the shell
whose first Betti number is minimal among all finite connected closed surface
separators of the two boundary components. The comparison surface does not
need an additional inside-shell hypothesis.

Both changed sources compile with zero diagnostics in 11.277 and 11.964
seconds including admission. NullhomotopyNeighborhood and SurfaceCompression
are freshly rechecked, and the reachable native import graph (576 modules)
has no cycles. The final silent audit takes 49.323 seconds and checks all
19 native declarations (three new and 16 retained, including one private),
11 critical reused entries and five concrete models. All 13 applicable
linters pass and all axiom closures are standard. The models retain the
radial shell's frontier, simple connectedness and old separator API, add its
actual minimal separator, and use a cube boundary as a comparison to prove
that a produced minimum separating two explicit points has first Betti zero
and is a PL sphere. Three external-model elaboration issues were repaired
before the passing audit; no source proof repair was needed.

The older separator signatures are unchanged. Frozen source identities,
objects, receipts and full audit are under
`moise304-reading/minimal-separator-checkpoint/`. This gives the actual
minimizer for the 30.4 argument but does not prove that the general shell
minimizer has Betti zero. Essential spanning disks, physical disjoint caps,
and separation by their union remain the upstream obligations. Root builds
remain stopped and shared outputs are unchanged.


## Essential singular disk in a finite neighborhood (2026-09-19 UTC)

`IsCombinatorialManifold.exists_essential_singular_disk_in_neighborhood`
now produces the actual singular filling needed before applying 26.4. From
a finite connected closed combinatorial surface which is not a PL sphere,
contained in an open simply connected U, it constructs a nontrivial based
loop p, a finite combinatorial manifold-with-boundary N contained in U,
and a piecewise affine map f from a genuine PL two-ball P in the Euclidean
plane into the interior of N. The whole surface also lies in that same
interior. Ambient dimension three gives a finite WB3 neighborhood.

The output includes b : C(frontier P, L.space), a homeomorphism e from the
loop circle onto frontier P, the pointwise equation f(z) = b(z), and a
free homotopy from pathToCircle p to b composed with e. It proves that b
is not nullhomotopic in L and that the original nontrivial class of p maps
to one in this same N for every proof of the inclusion. No singular disk,
embedding, or nullhomotopy is assumed as a new premise. The first N chosen
by the older kernel producer is not reused as an unverified target: the
final N is built around the surface together with the actual PL disk image.

The reusable chain consists of OpenTargetApproximation (relative PL
approximation retaining an open target), DiskFilling (exact boundary
extension on any planar PL two-ball), FreeLoopFilling (PL boundary freely
homotopic to the specified loop), and the new neighborhood filling producer
in NullhomotopyNeighborhood. General disk extension transports from a convex
model, while the open-target estimate preserves the full prescribed boundary.
The three new leaves are registered in the flat root aggregate. The native
reachable import graph has 538 modules and 1052 edges with no cycles.

All five changed/new modules compile with zero diagnostics. The existing
Homotopy.FreeLoopNullhomotopy module was separately compiled, without source
changes, under the coordinator's exact-module private lease; its original
source SHA256 is 0C86E609F45B37A8450C9068555AF9034E07DDEBFE621C3098E751D056BBB745.
The final silent audit takes 51.721 seconds including admission. It checks
all 11 native nonautomatic declarations (five new public, two private,
four retained), 13 critical reused declarations including the full axiom
closure of pathToCircle_nullhomotopic_iff, and six external declarations.
Those external declarations include two nondegenerate geometric models:
a fixed square boundary with a nonconstant PL filling, and an essential
polygonal circle in actual three-dimensional Euclidean space filled inside
an actual finite WB3 neighborhood. The circle's nontrivial fundamental group
and three supporting model declarations are also checked. All 13 applicable
linters pass, with only the standard foundational axioms.

Frozen raw/normalized source identities, six source/object/receipt sets and
the complete passing audit are under
`moise304-reading/essential-singular-disk-checkpoint/`. All four retained
public signatures are unchanged. Root builds remain stopped, the shared E
output library is unchanged, and no other lane's source was edited.

This closes actual essential singular disk production. It does not turn
the map into an embedded spanning disk: the unrestricted 26.4 producer is
still required. Physical disjoint caps and preservation of ambient
separation remain E3 obligations. Full 30.4 remains open.


### M304 embedded positive-genus compression (2026-09-19 UTC)

The premise-free native `exists_embedded_torus_compression` constructs an
actual finite embedded torus K in Euclidean three-space, a nonseparating
essential PL circle C, its PL annular neighborhood W, and the same connected
complement R = closure(K minus W). A fixed standard triangle circle is first
thickened to a finite embedded solid torus; the untwisted disk cylindrical
diagram supplies all subsequent objects. A middle cross-section is an actual
embedded spanning disk with intersection K exactly C. Two other cross-sections
are actual nonempty disjoint PL cap disks. Their intersections with both K
and R equal exactly their prescribed boundary circles, which are the two
ends of W. Native annulus capping gives an actual PL sphere P with first Betti
number zero; the same chain proves first Betti number two for K and strict
descent. The product homeomorphism and non-nullhomotopy of C are independently
retained in the statement, as is connectedness of K minus C.

Seven new natural-topic leaves are registered in the flat root aggregate.
AnnulusComplement now reuses the extracted annulus boundary/triangulation API;
its public signature is unchanged. All eight new/changed sources and three
existing consumers compile without diagnostics. The complete audit covers
12 native declarations, 18 critical reused entries and three concrete
nondegeneracy certificates, with all 13 applicable linters and only standard
foundational axioms. The native reachable import graph has 561 modules and
1110 edges without cycles. Eleven source/object/receipt sets, the passing
audit and raw/normalized hashes are frozen under
`moise304-reading/torus-compression-checkpoint/`.

This closes a genuine positive-genus nonempty compression instance, including
the geometric disk/cap producers for this torus. It does not supply arbitrary
30.4 surfaces with disjoint caps or prescribed ambient separator targets.
The unrestricted embedded-disk producer and general separation-preserving
compression remain upstream obligations. Root builds remain stopped; shared
E outputs and other lanes' source files were not changed.


### M304 full frontier of a disk cylindrical diagram (2026-09-19 UTC)

`IsCylindricalDiagram.image_side_eq_boundaryComplex` and
`IsCylindricalDiagram.frontier_eq_image_side` identify the entire boundary
of a finite embedded three-manifold carried by a disk cylindrical diagram
with the actual cylindrical side image. No pointwise untwisted-end hypothesis
is needed. Interior strip charts first put any remaining frontier in the
bottom disk. The native closed-surface complement producer would turn an
extra boundary component into a nonempty closed surface inside that disk;
the new general `IsCombinatorialManifold.not_subset_of_isPLBall` excludes
this by invariance of domain. It applies in every positive dimension.

Both new leaves are registered in the flat root. Their final source bytes
compile with zero diagnostics. The audit checks all four native declarations,
nine critical reused declarations and an actual triangle solid-torus example
with nonempty interior and exact full frontier, all with only standard
foundational axioms. All 13 applicable linters pass. The reachable native
import graph has 477 modules and 919 edges and is acyclic. Sources, objects,
receipts, audit and raw/normalized hashes are frozen at
`moise304-reading/cylindrical-frontier-checkpoint/`.

This supplies the missing ambient-boundary identity for the concrete torus
compression. Common actual separator targets are the next obligation; this
checkpoint does not assert general separation-preserving compression or
close Moise 30.4. Root builds remain stopped and shared E outputs are unchanged.


### M304 common actual targets for torus compression (2026-09-19 UTC)

The premise-free native `exists_embedded_torus_compression_separating_points`
retains the same embedded torus, essential nonseparating circle, annulus,
connected complementary annulus, proper spanning disk, exact disjoint caps,
and first-Betti descent from two to zero. It additionally returns the actual
finite solid torus N and identifies the original surface with frontier N.
The capped sphere is exactly the frontier of the remaining embedded disk
prism, an actual three-ball B. It produces q in interior B and z outside N,
proves q and z distinct, and proves that both surfaces separate {q} and {z}.
The original `exists_embedded_torus_compression` keeps its exact public
signature and is now a corollary of this stronger producer.

`IsPLHomeomorphOn.frontier_prism_image` gives the general ambient-frontier
identity for embedded disk prisms. The new cylindrical separation API works
for any targets H contained in the remaining ball interior and K contained
in the full three-manifold exterior. It derives both separations from the
actual frontier identities; neither separation is assumed.

All three new/changed modules compile without diagnostics, and both new
leaves are registered in the flat root. The complete audit checks five native
declarations, 25 critical reused declarations and five external certificates,
with all 13 applicable linters and only standard foundational axioms. The
certificates recheck the original nonempty disjoint caps and essential proper
disk, then certify common nonempty open regions and two actual disjoint PL
three-ball targets with nonempty interiors for the same torus/sphere pair.
The two-ball certificate is external audit evidence, not a separate native
public theorem. The reachable native import graph has 565 modules and 1118
edges, with no cycles. Three source/object/receipt sets, the audit, census and
raw/normalized hashes are frozen at `moise304-reading/torus-separation-checkpoint/`.

This closes the concrete positive-genus compression instance through actual
preserved separation. It does not produce embedded splitting disks or safe
replacement neighborhoods for arbitrary surfaces in Moise 30.4. Those general
26.4/30.3 obligations remain in their existing lanes. Root builds remain
stopped; shared E outputs and other lanes' source files were not changed.


### M304 native three-ball target production (2026-09-19 UTC)

`IsCylindricalDiagram.exists_separating_ball_pair` now constructs actual
PL three-ball targets for any disk cylindrical diagram carrying a finite
three-manifold in an ambient real normed space of dimension three. Their
interiors are nonempty, they are disjoint, the first lies inside the remaining
prism interior, and the second lies outside the full three-manifold. Both
the original side and the capped side separate these targets. The target
locations, nonemptiness and separations are produced, not assumed.

The premise-free native `exists_embedded_torus_compression_separating_balls`
retains every essential-circle, annulus, complement, proper disk, exact-cap
and Betti field of the original torus compression, and adds these same actual
ball targets with their locations and both separations. The original and
point-target theorem signatures are unchanged. The three-ball witness is
therefore no longer confined to external audit evidence.

Both changed modules compile without diagnostics. The complete audit covers
seven native declarations, 26 critical reuses and six concrete certificates,
including a certificate coupling the same essential circle and proper disk
to the native ball targets and first-Betti descent from two to zero. All 13
applicable linters pass and all axiom closures contain only standard
foundational axioms. The reachable import graph remains acyclic, with 565
native modules and 1119 edges. Three source/object/receipt sets and the audit
are frozen at `moise304-reading/torus-ball-targets-checkpoint/` with raw and
normalized source hashes. Root builds remain stopped and shared E outputs
are unchanged. General 26.4/30.3 and arbitrary-shell 30.4 remain open gates.


### M304 positive-genus compression in an actual spherical shell (2026-09-19 UTC)

The premise-free `exists_embedded_torus_compression_in_spherical_shell`
retains every original same-object torus, essential nonseparating circle,
annulus, complement, proper spanning disk, exact disjoint caps and first-Betti
2-to-0 field. It constructs a positive-width distance-band spherical shell.
The torus, capped PL sphere, entire left compression three-ball and middle
spanning disk lie in this shell's interior. Both surfaces separate the shell's
actual inner and outer metric boundary spheres.

The general `exists_isSphericalShell_separating_frontiers` only assumes a
compact outer set N, a subset B of N and a nonempty interior of B. It constructs
a round shell containing N minus interior B and both frontiers in its interior,
and proves that both frontiers separate the shell boundary spheres. B need
not be closed. Spherical shells are also transported through embeddings, and
the standard norm-band example is extended to distance bands about any center.
All earlier SphericalShell declarations are retained unchanged; TorusShell is
registered in the flat root.

The new combined import first exposed a stale inherited MoiseChain object that
still defined IsTopologicalSolidTorus internally. Current source already
imports the canonical SolidTorus definition. A readonly private refresh of
MoiseChain resolved the collision; SphericalShell, TorusShell and the existing
TameNestedCells consumer then compiled with zero diagnostics. Neither readonly
source nor any MoiseChain contract was edited, and shared E outputs remain
unchanged.

The final audit covers all 20 native declarations in the two changed/new
leaves, 31 critical reuses and nine concrete certificates, with all 13 applicable
linters and only standard foundational axioms. The certificates keep the same
essential disk inside the actual shell, check an open inner set for the general
frontier producer, and instantiate the existing Betti-minimal separator producer
on this shell: its first Betti number is zero and native sphere recognition
proves it is a PL sphere. The reachable native graph has 618 modules and 1236
edges and is acyclic. Four source/object/receipt sets, including the two readonly
refreshes, are frozen with audit and raw/normalized hashes at
`moise304-reading/torus-shell-checkpoint/`.

This is a concrete positive-genus instance with an actual Moise304 shell input.
It does not prove Moise304 for an arbitrary supplied shell. General embedded-disk
and safe replacement-neighborhood producers remain upstream gates. Root builds
remain stopped as instructed.

### M304 embedded meridian and nontrivial boundary kernel (2026-09-19 UTC)

The premise-free `exists_embedded_solid_torus_meridian` projects the same
embedded solid torus, quarter-height circle and spanning disk from the actual
torus-compression producer. It retains the exact disk-boundary parametrization,
frontier intersection, connected boundary complement and first Betti number two.
The disk minus its boundary lies in the solid torus interior and is nonempty.
The same circle inclusion is not nullhomotopic in the torus boundary, but is
nullhomotopic inside the solid torus through that embedded disk. A loop on this
circle has nontrivial image in the boundary fundamental group and trivial image
in the solid torus fundamental group.

The general `fundamentalGroup_map_eq_one_of_nullhomotopic` belongs in
Topology/FundamentalGroup/Nullhomotopy. It works for arbitrary topological spaces
and every basepoint, without connectivity or separation hypotheses. It uses the
existing free-to-based nullhomotopy equivalence; no new contraction assumptions
are introduced into the concrete meridian producer. Both new leaves are in the
flat root aggregate.

Both modules compile with zero diagnostics. All two native declarations, eight
critical reuses and three independent certificates have only standard
foundational axioms. All 13 applicable linters pass. The certificates preserve
the same nonempty proper disk and circle, derive a genuinely nontrivial kernel
and noninjective boundary inclusion, and check that the generic nullhomotopy
lemma does not need connectivity. The native import graph is acyclic with 571
modules and 1128 edges. Two complete source/object/receipt sets and the audit
are frozen at `moise304-reading/torus-meridian-checkpoint/` with raw and normalized
source hashes. Root builds remain stopped; shared E outputs are unchanged.
This is an actual solid-torus instance, not a general embedded-disk producer for
arbitrary three-manifolds or a proof of arbitrary-shell Moise304.

### M304 essential meridians at every cylinder height (2026-09-19 UTC)

`IsCylindricalDiagram.exists_essential_slice_disk` is a generic producer for
finite embedded cylindrical three-manifolds with a PL disk as cross-section and
pointwise identified ends. For every t in the closed interval [0,1], it supplies
an actual parametrized slice disk, its exact boundary circle and exact ambient
frontier trace. The disk minus its boundary is nonempty and lies in the ambient
manifold interior. The boundary circle is nonseparating and not nullhomotopic in
the manifold frontier, but is nullhomotopic inside the same manifold through
that slice disk. No torus or compression conclusion is assumed.

`IsCylindricalDiagram.isConnected_sdiff_slice` now accepts the closed interval,
including the glued end slices. Its assumptions still require neither untwisted
ends nor a finite-dimensional target. The original two other CylindricalCircle
signatures are unchanged. CylindricalFrontier and all three existing torus
consumers were privately rebuilt after this deliberate hypothesis weakening.
The new CylindricalMeridian leaf is registered in the flat root.

Six modules compile without diagnostics. The audit covers all four native
declarations in the two changed/new leaves, 12 critical reuses and two actual
model certificates. The first constructs one embedded solid torus and validates
all its slice disks simultaneously. The second checks both glued ends, their
nonempty disk interiors and disjointness from the middle disk. All 13 applicable
linters pass and every axiom closure uses only standard foundational axioms.
The reachable native graph is acyclic with 479 modules and 922 edges. Six complete
source/object/receipt sets and the audit are frozen with raw and normalized
source hashes at `moise304-reading/cylindrical-meridian-checkpoint/`.
Root builds remain stopped and shared E outputs remain untouched. Arbitrary-shell
Moise304 and a general embedded-disk producer remain separate open gates.

### M304 boundary-only endpoint data and general cylindrical compression (2026-09-19 UTC)

`IsCylindricalDiagram.image_subcylinder_inter_slice` now requires only equality
of the two endpoint images of the subcylinder. Its conclusion no longer assumes
pointwise endpoint agreement on the entire cylinder cross-section. The proof
uses endpoint injectivity and the actual invariant endpoint sets. It still
requires no finite-dimensional source or target. Its former CylindricalProduct
import has been removed.

This removes the endpoint agreement hypothesis entirely from the capping
producer. Its canonical name is now `IsCylindricalDiagram.exists_capped_surface`,
replacing `exists_capped_surface_of_eq_ends`. For any embedded PL disk cylindrical
diagram in a three-dimensional real normed space, the same actual annulus,
complement and two disjoint caps produce a PL sphere, with exact cap traces and
first Betti numbers two and zero. No pointwise endpoint agreement is assumed.
All existing Lean callers have been updated; the three TorusCompression public
statements remain exactly unchanged.

The essential-slice-disk producer now requires pointwise endpoint agreement
only on the disk boundary circle. The interior of the cross-section is no longer
constrained by that additional equation. All closed-interval heights, exact
proper disk traces and both nullhomotopy conclusions are retained.

Seven affected modules and the final external audit compile without diagnostics.
All eight native declarations in the four changed leaves, 12 critical reuses
and two actual all-height/glued-end model certificates have only standard
foundational axioms. All 13 applicable linters pass. The native import graph is
acyclic with 566 modules and 1120 edges. Seven source/object/receipt sets and the
complete audit are frozen with raw and normalized source hashes at
`moise304-reading/cylindrical-boundary-checkpoint/`. No root build or shared E
output write was performed. Arbitrary-shell Moise304 and the remaining upstream
embedded-disk and replacement-neighborhood producers are not claimed complete.

## Common annular solid torus neighborhoods in a prescribed shell (2026-09-19 UTC)

This round consumes integration `20d59136a23b53e0b700c8f8c5c20516cbabbe4c`,
whose common-circle construction originates in `77b982ae8`. The integration
merge is `5a419f176`; the four mathematical files from `734c87b5f` were preserved.
The exact integration sources and blob identities are frozen outside the
project at `moise304-reading/common-neighborhood-integration-baseline/`.

The only cross-lane mathematical edit is `CommonCircleNeighborhood.lean`.
`exists_common_annular_derivedNeighborhood_of_isOrientable` now constructs the
same common ambient derived neighborhood for two arbitrary finite orientable
combinatorial surfaces with boundary. Manifold structure and orientation are
transported through the actual identity PL homeomorphisms of their common
triangulations. The nested version is also generalized. Both old sphere-only
signatures are byte-for-byte unchanged after newline normalization; the old
single-neighborhood proof is a corollary of the general producer, and the old
nested proof consumes that corollary. `CommonCircleDerivedNeighborhood.lean`
and `DerivedNeighborhoodRestriction.lean` are unchanged from integration.

`CommonCircleSolidTorus.lean` proves that this same derived neighborhood in an
orientable finite three-manifold has an actual finite WB3 triangulation, is a
topological solid torus, and admits an untwisted PL disk cylindrical diagram.
If the given circle lies in the ambient interior, it lies in the constructed
neighborhood interior. `exists_common_solid_torus_neighborhood` retains the
given ambient complex and open U. Its three-dimensional ambient-space variant
constructs an enclosing simplex from the two supplied surfaces and shrinks the
neighborhood into the original U; it does not replace U by a newly chosen shell.

`IsCombinatorialManifoldWithBoundary.exists_spanning_disk_annular_neighborhood`
in `SpanningDiskNeighborhood.lean` starts with an actual parametrized disk D
whose intersection with the supplied surface is exactly its boundary circle J.
It produces the common solid torus N in the prescribed open U, disjoint from
a prescribed closed forbidden set F. A point in D minus J is produced from the
disk parametrization and excluded during neighborhood construction, so
`(D \ N.space).Nonempty` is proved rather than assumed. The same ambient
derived neighborhood has exact annular traces on the surface and the disk.
Only J must lie in U; the theorem does not infer containment of all of D in U.

`IsSphericalShell.exists_spanning_disk_annular_neighborhood` consumes the
original shell X, its original boundary components B0 and B1, and a connected
closed surface separating those targets. It derives containment of the original
disk boundary in the shell interior and produces N entirely within that same
interior, disjoint from both original targets. No round-shell substitution,
new target selection, or hypothesis asserting the resulting neighborhood is used.

The audit checks all 19 nonautomatic declarations in the three changed/new
leaves and the two unchanged common-derived dependencies, 18 critical reused
results including the old sphere-interface consumers, and two new external
nondegeneracy certificates. The first certificate applies the new theorem to
the existing positive-genus torus, its actual essential spanning disk and its
same spherical shell, retaining first Betti number two, essentiality, the full
disk's containment in that shell, and the original nonempty boundary targets.
The second extracts both actual annulus parametrizations and proves their
intersection is exactly the nonempty original essential circle, with a point
of the same disk still outside N. These are external certificates, not additional
premise-free native torus models. All 13 applicable linters pass; every audited
axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.

The three changed/new modules, two unchanged common-derived modules, and nine
readonly dependency/consumer refreshes compile with zero diagnostics. This
includes `DualCellPiercingNeighborhoods` and the actual trivalent model using
the retained sphere interface. The reachable native import graph has 600
modules and 1201 edges, is acyclic, and avoids `HurewiczLowDegrees`. Both new
leaves are registered in the flat root. Fourteen source/object/receipt sets,
the complete audit and raw/normalized hashes are frozen at
`moise304-reading/common-spanning-checkpoint/`.

The integration's `PolyhedralGraph` and `MoiseChain` objects were reused only
after matching exact verified source bytes and object hashes; the source
newline adjustment has no Git content diff. Origin receipts are preserved in
the integration-baseline evidence. Missing readonly dependencies were rebuilt
privately. No shared outputs or other lanes' worktrees were modified, and the
owner-stopped full-root build was not restarted.

This closes the common annular regular-neighborhood input for actual supplied
surface/disk data, including prescribed-shell containment and target avoidance.
It does not mark the abstract annulus parametrizations by the original surface
bicollar or align their endpoint circles with a splitting prism. E3 retains
that compatibility task. No disjoint cap pair or separation of a capped union
is produced here; unrestricted embedded-disk production and the subsequent
separation-preserving compression remain necessary for arbitrary-shell 30.4.

## Local separation transfer for the original spanning disk (2026-09-19 UTC)

`SpanningDiskSeparation.lean` consumes the common annular neighborhood from
the previous checkpoint and the existing `SurfaceSpanningDisk` and
`SurfaceSplitSeparation` producers. No E3 geometric source is changed.

`IsCombinatorialManifoldWithBoundary.exists_polyhedral_separator_of_spanning_disk`
retains the supplied surface S, disk parametrization r, compact neighborhood A,
open U and targets H,T. It allows a finite orientable surface with boundary,
provided the original disk boundary avoids that surface boundary. Only
compactness and the relative-neighborhood condition on A are required; no
triangulation or annular structure of A is assumed. The entire disk and A must
lie in U and avoid the two closed targets. The proof constructs the two
enlarged disks inside D union (S intersect A), then a finite ambient WB3
neighborhood inside the same U away from the targets, and invokes the existing
local splitting-ball producer. This ambient complex need not contain the whole
surface. `IsCommonAnnularDerivedNeighborhood.exists_polyhedral_separator_of_spanning_disk`
is a corollary that derives these inputs from the actual common triangulation.

The result is an actual finite PL three-ball B and a finite polyhedral
separator P. It proves all of the following for those same objects:

- The original D lies in a parametrized disk M in the boundary of B.
- The other disk Q satisfies boundary B = M union Q and
  M intersect Q = q(image of the standard disk boundary).
- M minus D and the removed local piece V lie in S intersect A.
- S intersect B = (M intersect S) union V.
- P = closure(S minus B) union boundary B, P intersect B = boundary B,
  and P minus B = S minus B.
- P separates the original H,T, and P minus S is nonempty. The latter is
  witnessed by the image of the original disk's standard interior point.

`IsSphericalShell.exists_polyhedral_separator_of_spanning_disk` constructs A
using the actual common-annular solid-torus producer and applies this transfer
in the original shell X. The hypothesis D subset interior X is explicit;
containment of D's boundary alone is not promoted to containment of D. Both A
and B avoid the original B0,B1, and P lies in that same shell interior and
separates the same targets. The conclusion uses the intrinsic frontier of B.
`Separates.mono` is the only addition in the general topology file; no existing
separation declaration or signature changes.

Thirteen private module checks, including the current E3 dependency chain,
pass with zero diagnostics. The audit checks all 15 nonautomatic declarations
in the two changed/new mathematical modules, 18 critical reuses and two actual
essential-torus-disk certificates. The first retains the original positive
genus surface, its essential disk, its original shell and nonempty targets.
The second starts from the same supplied common annular neighborhood and
checks the exact local traces, nonempty M intersect Q, and the inclusion of
D minus S in P minus S. All 13 applicable linters pass, and all axiom closures
contain only standard foundational axioms. The reused SurfaceSpanningDisk,
common-neighborhood, SeparatingSurface, SphericalShell and TorusShell receipts
match their current source bytes. The reachable native graph has 848 modules
and 1789 edges, is acyclic, and avoids HurewiczLowDegrees.

Source/object/receipt sets for all 13 checks and the complete external audit
are frozen at `moise304-reading/spanning-separation-final-checkpoint/`. Its manifest
SHA256 is `DD2BAA3BB8A125C327C9BABAED04C73BF46603A943852F33DC7A038B1D7A9BBF`.
The new leaf is registered in the flat root. The owner-stopped root build is
not restarted, and no shared E output is written.

The resulting P is a polyhedral separator, not a proved closed two-manifold.
Its whole local boundary sphere cannot be substituted for the desired pair
of disjoint caps: the produced M and Q have a proved nonempty intersection.
Thus no Betti decrease or final compression is claimed. The accepted
`ab29b2d71` SurfaceSplitRealization/SurfaceSplitCapping declarations were
inspected at that exact integration commit. They require an actual disjoint
cap pair with the original split-surface boundary equations and do not supply
separation of its capped union. This round does not duplicate those modules
or E3's relative-prism/end-circle marking work. That marking and a separation
argument for the actual capped surface, together with general production of
the embedded essential disk, remain the precise upstream gates for 30.4.

## Separation of the actual capped surface (2026-09-19 UTC)

`SurfaceCappingSeparation.lean` proves the missing separation transfer once
an actual compression region and its original-surface traces are supplied.
It does not consume the larger polyhedral separator from the previous round.

The primary theorem is
`IsCombinatorialManifold.separates_of_boundary_replacement`. Its old surface
S is finite, connected and a closed PL two-manifold in a three-dimensional
real normed space. It assumes the original separation of arbitrary H,T,
a closed candidate C, and a region N satisfying
closure(interior N) = N and preconnected interior. The geometric equations
are S intersect N subset frontier N, frontier N subset S union C, and
S minus N = C minus N. Both original targets avoid N. It proves
`Separates C H T`; no separation of C is an input, and the targets need not
be connected. The PL three-ball version derives both interior conditions.

The proof constructs a separating region, rather than inferring separation
of a smaller set from separation of a larger set. The actual interior of N
lies in one of the two open regions U,V of the original separation. The
canonical two complement components of the connected closed PL surface
show that S is contained in the closure of either nonempty region. At each
point of the old wall away from C, native PL local separation supplies a
small neighborhood with two preconnected complement pieces. One meets
interior N and the other meets V. Since frontier N is contained in S union C,
the first piece cannot cross frontier N, so it lies entirely inside N.
Consequently frontier(U minus N) is contained in C. The original H and T
are on opposite sides of this newly constructed frontier. Only then does
`Separates.mono` enlarge that frontier into C, in the valid direction.

The reusable topological calculation is
`Topology.frontier_sdiff_subset_of_local_separation` in
`Connected/BoundaryReplacement.lean`. It only needs the local separation and
opposite-side closure conditions on S intersect N, and inclusion of S minus N
in C. `SurfaceComplement` generalizes its former private local lemma to
`IsCombinatorialManifold.exists_connected_neighborhood_pair_sdiff` inside any
prescribed ambient neighborhood, and reuses it in the existing complement
pair theorem. Existing public signatures are retained. `BallRegularClosed`
adds `IsPLBall.isConnected_interior_of_finrank`; the existing Euclidean
`isConnected_interior_of_isPLBall` is now its corollary.

`IsCombinatorialManifold.separates_capped_surface` applies the result to the
literal union R.space union D0 union D1, using a real PL three-ball N, two
PL disks, S intersect N = W, W union R.space = S, and
frontier N = W union D0 union D1. The stronger disjoint-cap, annulus and
boundary-marking data required for the manifold realization are compatible
inputs, but separation itself does not need those extra assumptions.
`IsSphericalShell.separates_capped_surface` keeps the supplied X,B0,B1. From
N subset interior X it proves separation of those same B0,B1, containment
of the capped union in interior X, and exact agreement with S outside N.

The external test uses the existing embedded essential-torus compression
model, including its proper middle spanning disk with nonempty interior away
from S, non-nullhomotopic boundary circle, nonempty disjoint caps and actual
annular wall. It derives the compression-region trace using the cylindrical
slice intersection theorem and derives its frontier using the PL prism
frontier theorem. It discards the model's supplied separation of the capped
surface. In the original spherical shell chosen for the model, the new
theorem re-proves separation of the same two nonempty boundary targets by
the same finite sphere P = R union D0 union D1. The test retains Betti numbers
2 for S and 0 for P, shell containment and outside agreement.

The five mathematical modules contain 18 nonautomatic declarations. All 18,
16 critical reuses and the actual model pass the axiom audit with only
standard foundational axioms. All 13 applicable linters pass. The five
modules and eight direct dependent modules pass private compilation with
zero diagnostics. The native source graph has 545 reachable modules and
1085 edges, is acyclic and avoids HurewiczLowDegrees. Both new leaves are
registered in the flat root. The owner-stopped root build is not restarted;
no shared E output is written. Frozen receipts are recorded below.

The 13 source/object/receipt sets, complete external audit, census and source
review are frozen at `moise304-reading/capping-separation-checkpoint/`.
Manifest SHA256:
`F89F34F3073B370BC754499102908695823F6601874DA8C873B6C71256316DC8`.
The source review also verifies all 11 pre-existing public signatures in the
three edited foundational files are unchanged. Final audit completion is
2026-09-19T16:20:27.4702876Z.

This closes separation transport for a genuine wall-to-caps compression.
It does not produce the original-surface wall/end-circle marking from the
previous common derived neighborhood, nor does it produce an embedded
essential disk for an arbitrary prescribed shell. Those geometric producers
remain the upstream obligations for arbitrary-shell Moise 30.4. The accepted
SurfaceSplitRealization/SurfaceSplitCapping APIs remain the canonical
manifold-realization consumers; their capped-space equation rewrites the
literal union in the new separation theorem. No E3 geometric source or
existing native torus-model theorem is modified in this round.

## Connected separating component with strict Betti descent (2026-09-19 UTC)

`SurfaceCompressionSeparation.lean` closes the conditional compression step
from actual marked wall, ball and cap geometry. Its primary theorem is
`IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_annulus_replacement`.
It starts with the supplied finite connected closed surface S, the original
separation of preconnected H,T, an essential PL circle J in S, a centered PL
annulus parametrization rho, and an actual PL three-ball N. The geometric
equations are S intersect N = W, frontier N = W union D0 union D1,
W intersect Di = the parametrized boundary of Di, and those boundaries equal
the two endpoint circles of rho. The supplied PL disks D0,D1 are disjoint,
and the original targets avoid N.

The result constructs a finite closed connected PL surface P, orientable and
two-sided, contained in C = closure(S minus W) union D0 union D1. It proves
that P separates the original H,T and has strictly smaller first Betti number
than S. It also identifies P as an actual connected component: for every
x in P, connectedComponentIn C x = P. Neither a result manifold, separation
of the capped union, nor any Betti descent is an input.

The nearest missing upstream step was construction of the retained surface
and its compatibility data. The proof uses the existing
`IsCombinatorialManifold.exists_annulus_complement` to produce the finite WB2
complex R with R.space = closure(S minus W). Injectivity of the centered
annulus proves that J avoids R. The open complement of R then supplies the
relative-neighborhood condition on W. The actual wall equation and the
produced boundary of R derive the cap traces R intersect Di = boundary Di.
The preceding `separates_capped_surface` theorem proves separation of the
literal capped union from the original separation.

The hard capping and Betti arguments already existed in the native chain;
they are reused. `SurfaceCompression` strengthens its existing selection
theorem to
`IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_annulus_capping`,
adding the exact connected-component equation. Its former public theorem
remains a corollary with the same signature. In the nonseparating case,
`exists_capped_annulus_complement` constructs the entire connected capped
surface with beta(result) + 2 = beta(S). In the separating case,
`exists_capped_pair_of_separating_essential_annulus` constructs two disjoint
closed connected surfaces P,Q and proves both nonspherical. If either were
a sphere, its disk complement and the actual half-annulus cylinder would
make the original inclusion J into S nullhomotopic, contradicting the
original essential-circle hypothesis. Their positive Betti numbers sum to
beta(S), so both are strictly smaller. Phragmen-Brouwer selects one still
separating the original targets. The native closed-cover component theorem
identifies it as a connected component of the actual cap union.

`IsCombinatorialManifold.exists_separating_component_bettiOne_lt_of_spanning_disk`
ties J to the boundary of the original supplied embedded disk, whose
intersection with S is exactly that boundary. The shell specialization
`IsSphericalShell.exists_separating_component_bettiOne_lt_of_spanning_disk`
retains the original X,B0,B1 and proves P lies in interior X and separates
those same boundary targets. It derives their avoidance from N subset
interior X. The disk boundary data are not used to assert containment of the
whole disk in N or in X; the disk-to-wall geometry remains an upstream task.

The actual essential-torus test invokes this new shell producer. It retains
the original proper middle disk, the original shell and nonempty targets,
the same actual end disks, and the wall/frontier equations. It derives the
centered annulus parametrization on the actual original boundary circle and
discards the model's previous final separation. The producer constructs a
new finite surface P'. Its component equation then identifies P' with the
original literal capped sphere; the original sphere is a geometric reference
after production, never an input to the new producer. The test verifies
source beta 2, result beta 0, strict descent, original separation, shell
containment and exact equality to the cap union. This is a concrete
nonseparating model; the separating case is established by the audited
general native proof, not by a claimed second model.

The accepted `ab29b2d71de0bb8dc92ab6a9906137d2244235ef` realization/capping
interfaces were inspected. The physical capping chain in `AnnulusCapping`,
`DiskCapping` and `SurfaceBoundaryCapping` is unchanged from that integration
commit, and no deleted private gluing proof was copied. General
`SeparatingComponent`, the existing `SurfaceSplitBetti` consumers and the
original-shell minimum-Betti producer were inspected rather than duplicated.
The optional verification of the critical `SphericalDiskComplement` exposed
two pre-existing long lines. The coordinator authorized their formatting
repair and the required standard header. No imports, statements or proof
tokens change; the before/after source hashes and complete seven-declaration
audit are retained in the evidence package.

The remaining arbitrary-shell 30.4 obligations are production of an embedded
essential disk and production of the actual compression ball with its wall
marked by the original surface bicollar and its two disjoint cap rims.
E3 retains that geometric interface. Once these genuine inputs are supplied,
the new theorem produces the connected closed separator and strict Betti
descent in the original shell. Arbitrary-shell Moise 30.4 remains open.

All 14 nonautomatic declarations in the three changed/new mathematical
modules, 26 critical reused declarations and the actual torus model pass
the axiom audit with only propext, Classical.choice and Quot.sound. All 13
applicable linters pass. The three mathematical modules and the downstream
DiskCapping/AnnulusCapping chain pass fresh private compilation with zero
diagnostics. Ten former public signatures are unchanged. The new leaf is
registered once in the flat root; the reachable native graph contains 605
modules and 1216 edges, is acyclic and avoids HurewiczLowDegrees. The stopped
root build is not restarted, and shared E outputs are untouched.

Fourteen source-matching source/object/receipt sets, the complete external
audit, declaration census, source review, and before/after formatting
evidence are frozen at `moise304-reading/compression-separation-checkpoint/`.
Manifest SHA256:
`1CFD2E35A20139953B6018EECF6C975CB686E266BD62D97BA3C85A5AF614BFC1`.
Final audit completion is 2026-09-19T16:55:49.8860324Z. The frozen manifest
records the individual receipt times, including valid earlier unchanged
dependency receipts. SphericalDiskComplement's raw source SHA256 changes
from `95EB5E0587DB26D1D6496B52C17D5CF2985C2DB607441298282ED77CCFB988CC`
to `9A815DA01518E972B5C5B166EB5BC2DC3C08E7B9F170B7A352C483FB6D43EFC2`;
its source tokens agree after removing whitespace and required headers.

## Finite interior-surface cuts and open-cover kernels (2026-09-19 UTC)

The corrected Moise252 statement in MoiseChain applies to an actual connected
component of the boundary of an orientable finite WB3 complex. The present
round constructs those geometric boundary components in the separating case
and proves a reusable open-cover kernel bridge. It does not prove
Moise252 implies Moise264, and it does not produce an embedded essential disk.

`SurfaceCutting.lean` provides four public theorems and one private helper.
The general producer
`IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_separating_surface`
starts with the original finite connected WB3 complex K and finite connected
closed PL2 surface L inside K, disjoint from its original boundary. Given
geometric separation of K minus L, it constructs finite connected WB3
complexes A,B with A union B = K and A intersect B = L. Their boundaries are
exactly L union (A intersect boundary K) and L union (B intersect boundary K).
It constructs actual ConnectedComponents labels in both boundaries whose
connectedComponentComplex spaces equal L. No cut manifold or boundary-copy
identification is supplied as an input. The proof reuses the native
complement-component closure manifold and boundary theorems and the closed
partition connected-component theorem.

`IsCombinatorialManifold.not_isPreconnected_sdiff_of_subset_interior` proves
separation by a connected finite closed PL2 surface L in any real
three-dimensional ambient normed space, whenever L lies in the interior of
the set being cut. The ambient complement components meet each neighborhood
of L and cannot connect in its complement.
`IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_surface_interior`
therefore derives separation from the original interior condition and
produces the same A,B, additionally proving both orientable. The enclosing
simplex is used only to prove orientability of these actual cut complexes;
it never replaces the original K.

`IsCombinatorialManifoldWithBoundary.exists_twoSidedCollar_of_interior_surface`
converts the existing closed PL bicollar into an open TwoSidedCollar of the
literal inclusion L.space into the original K.space. Its entire ambient
image lies in the supplied relative neighborhood U. It assumes intrinsic
two-sidedness in K and preserves the original K, L and U. The construction
uses the native closed PL bicollar and the checked closed-interval-to-open-
collar theorem; it introduces no singular-disk normalization assumption.

`FundamentalGroup/OpenCoverKernel.lean` contributes two public theorems.
`injective_fundamentalGroup_map_inter_of_open_cover` proves that injectivity
of both overlap-to-side maps for an actual open path-connected cover implies
injectivity of the overlap-to-ambient map. It uses the native van Kampen
amalgamated-product equivalence and Monoid.PushoutI.base_injective.
`exists_nontrivial_fundamentalGroup_kernel_of_open_cover` uses an actual
nontrivial overlap element killed in the original ambient space to produce
a nontrivial kernel element for at least one side. The resulting element
need not be the initially supplied element. No side kernel is an input.

`FundamentalGroup/BicollarKernel.lean` proves
`ThreeManifold.TwoSidedCollar.exists_nontrivial_fundamentalGroup_kernel_of_simplyConnectedSpace`.
For a compact path-connected nonsimply-connected surface with an actual
two-sided collar in a simply connected, locally path-connected Hausdorff
ambient space, it constructs a nontrivial element killed by one of the two
canonical overlap-to-side maps. The overlap is homotopy equivalent to the
original surface, and the ambient group is trivial. Simple connectivity of
the original ambient space is an explicit restriction of this theorem.

The external actual model fixes a finite enclosing PL ball K once and uses
the existing embedded connected torus L, with first Betti number two, inside
its interior. The new producers cut that same K along that same L, construct
the orientable A,B and both actual boundary labels, and produce a nontrivial
element of pi1(L) killed in pi1(K). An actual collar of the same inclusion
has image in the prescribed neighborhood interior K, and the new bicollar
kernel theorem produces a nontrivial side kernel. The model proves these
facts together for the same objects. It does not identify that side kernel
with the kernel into either finite closed cut complex A or B.

The remaining bridge is now explicit: for the general original K and L,
construct the appropriate collar open cover, identify its overlap with L
and its sides with the finite cut pieces by maps inducing the required
fundamental-group isomorphisms, and transport a produced nontrivial kernel
to one of the actual boundary-component inclusions required by Moise252.
The based-group/free-loop and boundary-copy transports must retain their
commuting maps. The full hypotheses of Moise264 also require handling
components, the nonseparating case and orientability outside the real
three-dimensional specialization. The existing neighborhood-kernel and
essential-singular-disk producers were inspected and axiom-audited, not
duplicated. F retains the actual Loop Theorem proof; E3 retains compression
wall/cap geometry. No F, E3 or h/S mathematical source is edited.

All eight nonautomatic declarations in the three new leaves, 27 critical
reuses, the single actual geometric model and its four private helpers pass
the transitive axiom audit with only propext, Classical.choice and Quot.sound.
All 13 applicable linters pass. The three new leaves have zero-diagnostic
private receipts; the critical SurfaceComponentClosure is also freshly
checked, and its consumer and the final audit are refreshed afterward.
The native graph has 508 reachable modules and 989 edges, is acyclic and
avoids HurewiczLowDegrees. All three leaves are registered once in the flat
root. All pre-existing mathematical source files are unchanged. The stopped
root build is not restarted, and shared E outputs are untouched.

Nine source-matching source/object/receipt sets, the complete external audit,
declaration census and source review are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/surface-cutting-checkpoint/`.
Manifest SHA256:
`2B430531079C51AF7D64907068EC554DA6D77FD463A60ABEDE4C582AE76F8552`.
Final audit completion is 2026-09-19T17:43:57.5655663Z. The individual receipt
times are recorded in the manifest, including valid earlier receipts for
unchanged dependencies. Full Moise264 and arbitrary-shell Moise304 remain
open; independent integration acceptance is not claimed.

## Kernels in actual finite cut boundaries (2026-09-19 UTC)

The open-side kernel is now transported to the actual closed cut manifold
and its actual connected boundary component. This completes that bridge
when the original ambient complex K is simply connected. The kernel element
produced after van Kampen splitting is constructed anew; it is not asserted
to equal an initially supplied element.

`FundamentalGroup/BicollarBoundary.lean` defines the zero section into the
canonical open-cover overlap and its projection to the original surface.
It proves `fundamentalGroup_map_collarMiddleInclusion_bijective`, using the
native collar-middle homeomorphism and contractibility of the interval.
The two `negativeRetraction_comp_collarMiddleInclusion` and
`positiveRetraction_comp_collarMiddleInclusion` equalities identify the
composites through the existing native retractions with the literal boundary
inclusions into the closed sides. Thus
`exists_nontrivial_fundamentalGroup_kernel_boundary_of_simplyConnectedSpace`
produces a nontrivial group element killed by one actual closed-side map.
These are equalities of continuous maps and their induced based group maps,
including the required basepoint casts.

`Connected/ClosedCover.lean` adds
`closure_connectedComponentIn_sdiff_inter_eq_or_eq`: for a closed cover with
connected dense exclusive parts, the closure of each complement component
equals one of the two original closed sets. `SurfaceCutKernel.lean` derives
the connected dense exclusive parts from the native connectedness and
density of manifold interiors. Its
`closure_collar_component_eq_of_manifold_pair` consequently identifies the
actual collar side closures with the supplied finite cut complexes A,B.

`exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair` transfers the
closed-side kernel into the literal inclusion of L into one of those same
A,B. `exists_boundary_component_kernel_of_manifold_pair` transports it
further into the actual `connectedComponentComplex` boundary inclusion,
using the proved equality of its space with L. No closed-side or boundary
kernel is an input to either theorem.

The full producer
`IsCombinatorialManifoldWithBoundary.exists_boundary_component_kernel_of_interior_surface`
starts with the original finite simply connected WB3 complex K, a finite
connected closed PL2 surface L in its interior, a nontrivial element of
pi1(L), and an arbitrary prescribed relative neighborhood U. In real
ambient dimension three it constructs a collar of L into that original K
whose entire image lies in U, a finite connected orientable WB3 cut piece
R inside K, its exact boundary L union (R intersect old boundary K), and
an actual boundary component equal to L carrying a nontrivial kernel into
R. This covers any such simply connected K, not only balls. The enclosing
simplex remains only an orientability proof device and never replaces K.

`FundamentalGroup/Nullhomotopy.lean` adds
`exists_non_nullhomotopic_freeLoop_of_nontrivial_fundamentalGroup_kernel`.
For an arbitrary continuous map it converts a proved nontrivial based-group
kernel into a free loop nonnullhomotopic in its source and nullhomotopic
after that map. It reuses the native path-to-circle and nullhomotopy API.

The external actual model fixes one nonempty finite PL ball K and its
embedded connected beta-two torus L. It invokes the complete producer for
that same K,L and U = interior K, retains the original pi1(L)-to-pi1(K)
kernel, and verifies the actual cut boundary, its nontrivial kernel and the
corresponding essential free loop together. It does not invoke Moise252,
construct an embedded essential disk, or assert singular-disk normalization.

All 22 nonautomatic declarations in the four changed/new mathematical
modules, 43 critical reused declarations, the actual model and its three
private helpers pass the transitive axiom audit with only propext,
Classical.choice and Quot.sound. All 13 applicable linters pass; all checks
have zero diagnostics. Five former public signatures are preserved. Both
new leaves are registered once in the flat root. The native dependency
graph has 527 modules and 1024 edges, is acyclic and avoids
HurewiczLowDegrees. The stopped root build is not restarted, and shared E
outputs and F/E3/h/S mathematical sources are untouched.

Thirteen source-matching source/object/receipt sets, the complete external
audit, declaration census and source review are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/surface-cut-kernel-checkpoint/`.
Manifest SHA256:
`080A9AD86A7A930F66371D76EE824CCECDEB73D2DA387A6F02F7F400C0FA08AA`.
Final audit completion is 2026-09-19T18:20:39.5754872Z. Individual receipt
times distinguish newly checked modules from unchanged earlier dependencies.

The general ambient-kernel version still requires an open-cover construction
for the original separating closed cut without ambient simple connectivity.
The existing outward-collar and domain-retraction APIs are the next native
route under investigation. Nonseparating cuts, general ambient orientability
and the actual Moise252 theorem remain separate upstream obligations.
Full Moise264 and arbitrary-shell Moise304 remain open; independent
integration acceptance is not claimed.

## Closed-cut kernels from the original ambient inclusion (2026-09-19 UTC)

The kernel transfer now accepts an actual nontrivial element killed by the
original inclusion L into K. Ambient simple connectivity is no longer a
hypothesis of the primary theorems. The previous simply connected results
are corollaries of this general construction.

`FundamentalGroup/CollaredClosedCover.lean` proves
`ThreeManifold.TwoSidedCollar.exists_nontrivial_fundamentalGroup_kernel_of_closed_cover`.
It applies in an arbitrary topological ambient X to a path-connected
bicollared S and path-connected closed pieces P,Q. The geometric inputs are
P union Q = X, P intersect Q = range e, and closure(P minus Q) = P,
closure(Q minus P) = Q. Given g != 1 killed by e into X, it produces a new
nontrivial element killed by the literal inclusion into P or Q. A closed-side
kernel is never an input, and the output is not equated with the input g.

Three elementary results in `Connected/ClosedCover.lean` derive
interior P = complement Q, closure(interior P) = P and frontier P = P
intersect Q from these dense-side hypotheses. The generic proof then reuses
the native outward-collar orientation to obtain a collar d negative on P
and its reverse negative on Q. The actual open sets are interior P union
d.range and interior Q union d.reverse.range. They cover X, are path
connected, and their intersection equals d.range. The native domain
retractions fix the zero section and commute with both literal closed-side
inclusions. The based ambient inclusion square also commutes, including
the mapOfEq casts. The range homeomorphism and contractibility of the real
factor give the overlap-to-S homotopy equivalence and zero-section group
isomorphism. Native van Kampen then supplies the new side-kernel element.

`FundamentalGroup/Retraction.lean` now exposes
`fundamentalGroup_mapOfEq_leftInverse` and
`bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse`.
Its original injection theorem and the earlier collar-middle bijection
reuse this common based-map argument. The existing injection signature and
all ten declarations of BicollarBoundary retain their public signatures.

`SurfaceCutKernel.lean` supplies the primary theorems
`exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair_of_map_eq_one`
and `exists_boundary_component_kernel_of_manifold_pair_of_map_eq_one`.
They work with the same supplied finite connected WB3 pieces A,B in any
finite-dimensional real ambient space, their actual common surface L and
actual boundary labels. Dense connected manifold interiors establish the
closed-cover hypotheses. Literal subtype maps carry the resulting kernel
into A or B and then into the actual connectedComponentComplex inclusion.
No replacement ambient simplex or free cut object is introduced.

The complete producer
`IsCombinatorialManifoldWithBoundary.exists_boundary_component_kernel_of_interior_inclusion`
starts with the original finite connected WB3 K and finite connected closed
PL2 L in its interior in real ambient dimension three. It takes an actual
nontrivial pi1(L)-to-pi1(K) kernel and the specified relative neighborhood U.
It constructs the U-contained collar, the same finite connected orientable
cut piece R inside K, the exact old-boundary trace, its actual boundary
label equal to L and a nontrivial boundary kernel. The original full simply
connected producer is a corollary with its former signature. Two intermediate
simply connected corollaries additionally lose their unnecessary ambient
local-path-connectedness instance; their other binders and conclusions
are preserved. Eighteen other former public signatures are unchanged.

The external actual model retains its original finite nonempty PL ball K,
embedded beta-two torus L and U = interior K. It supplies the actual source
inclusion kernel to this new general producer, then verifies the actual
cut boundary, nontrivial kernel and essential free loop together. The ball
is still the test model; a nonsimply-connected geometric test ambient is
not claimed. The theorem statement and checked proof use the supplied
ambient kernel directly.

All 37 nonautomatic declarations in the five changed/new mathematical
modules, 54 critical reused declarations, the actual model and three
private helpers pass the transitive axiom audit with only propext,
Classical.choice and Quot.sound. All 13 applicable linters pass. The five
modules and final audit have zero-diagnostic private receipts. The new leaf
is registered once in the flat root; the native graph has 527 modules and
1032 edges, is acyclic and avoids HurewiczLowDegrees. The stopped root build
is not restarted. Shared outputs and F/E3/h/S mathematical sources are
untouched; independent acceptance is not claimed.

Fifteen source-matching source/object/receipt sets and the complete external
audit, declaration census and source review are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/collared-closed-cover-checkpoint/`.
Manifest SHA256:
`8F96C466CCC27FB5683F03258247AE40693FE8EFF66D16AD4CCC7E5DBF06C0EA`.
Final audit completion is 2026-09-19T18:43:31.3239295Z. The manifest retains
individual receipt times for freshly checked modules and unchanged earlier
dependencies.

Full Moise264 still requires the full component and ambient generality,
including nonseparating cuts and the relevant orientability construction.
The actual Moise252 theorem and embedded essential-disk production remain
upstream. This checkpoint does not assert Moise252, Moise264 or arbitrary-
shell Moise304. The existing based-kernel-to-free-loop theorem continues
to provide the exact input shape for a later explicitly conditional Moise252
consumer on the produced boundary.


### M304 essential disks from the boundary Loop Theorem (2026-09-19 UTC)

The new registered leaf `SurfaceEssentialDisk.lean` takes the explicit
parameter `h252 : Moise252`. It proves the connected-surface,
three-dimensional ambient case needed by the original-shell argument.
It does not assert the Loop Theorem or the full Moise264 statement.

`IsCombinatorialManifoldWithBoundary.exists_essential_disk_of_loop_theorem`
starts with the original finite WB3 K, finite connected closed PL2 L,
ambient dimension three, preconnected K, an actual nontrivial kernel of
the literal inclusion L to K, and the specified relative neighborhood U.
The existing `exists_boundary_component_kernel_of_interior_inclusion`
produces the orientable cut piece R, its exact boundary trace and its
actual boundary-component kernel. The native kernel-to-free-loop theorem
provides the input to h252 on that R and that boundary label. The result is
an embedded PL disk D in K minus the old boundary, with exact intersection
`D ∩ L.space = r '' stdSimplexBoundary 2`, and a nonnullhomotopic boundary
inclusion into the original L. The U-contained collar remains in the
output. Neither the essential disk nor the final closed-side kernel is an
additional hypothesis.

Old-boundary avoidance follows from the exact cut-boundary equation:
a disk point on the old boundary lies on the boundary of R, hence on the
disk rim and in L, contradicting the original interior hypothesis.
The actual boundary-component equality transports the nonnullhomotopy to
the original L. This argument retains all of L under the explicit
connectedness hypothesis; it does not silently discard other components.

`exists_connected_neighborhood_fundamentalGroup_map_eq_one` strengthens
the neighborhood API for compact connected S. The union of S with the
actual nullhomotopy image is compact and connected, since the homotopy
image meets S at its original loop. The native connected-neighborhood
theorem gives a finite connected manifold neighborhood containing that
whole union. The same nullhomotopy is rebuilt in this neighborhood.
`IsCombinatorialManifold.exists_connected_neighborhood_nontrivial_fundamentalGroup_kernel`
uses it; the former neighborhood-kernel theorem remains a corollary with
its original signature. All seven former public signatures in the two
edited modules are unchanged.

`IsCombinatorialManifold.exists_essential_disk_in_neighborhood_of_loop_theorem`
therefore produces a proper essential disk inside a prescribed simply
connected open neighborhood of the entire original connected nonspherical
surface. `IsSphericalShell.exists_essential_disk_annulus_of_loop_theorem`
applies this to the interior of the original X with the same S, B0 and B1.
It produces the disk, proves that D has a point outside S, and supplies its
essential PL circle and a centered PL annulus in S. For those same objects,
the existing `SurfaceCompressionSeparation` theorem then produces a
strictly lower-Betti separating component once supplied with the actual
compression ball, wall, two caps and exact trace equations. These are
genuine geometric inputs; this checkpoint does not construct them for an
arbitrary produced disk. Separation, capping and Betti arguments are reused.

The complete external audit preserves two unconditional actual geometric
models: the nonempty finite ball with its embedded beta-two torus and
actual cut-boundary kernel, and the torus compression in its original
spherical shell with two nonempty targets. Two separate h252-conditional
models exercise the new API on those original objects. The first retains
the original K, L, actual source kernel and U = interior K while producing
the proper essential disk. The second retains the original S, X, B0 and
B1 and produces the disk/annulus plus the stated geometric-input consumer.
Neither conditional model is evidence that h252 has been proved.

All 15 nonautomatic declarations across the three changed/new modules and
the unchanged actual compression consumer, 74 critical reuse entries,
four models and three private helpers have transitive axiom closures
contained in propext, Classical.choice and Quot.sound. All 13 applicable
linters pass. ConnectedNeighborhood, MoiseChain, every changed module and
the actual compression consumer have zero-diagnostic private receipts;
the changed chain was rebuilt after the connected-neighborhood refresh.
The native source graph has 698 modules and 1427 edges, is acyclic and
avoids HurewiczLowDegrees. The root only adds the one new leaf import.

23 source-matching source/object/receipt sets and the final audit,
census and source review are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/essential-disk-checkpoint/`.
Manifest SHA256:
`4C0794FAAC0C53E13EF333D6FCE8388E3AD08F80CC44A4379A7F6757CA7266B9`.
Final audit completion: 2026-09-19T19:14:07.3227336Z.
Individual receipt times distinguish refreshed modules from unchanged
earlier dependencies. The stopped full-root build was not restarted.
Shared outputs and F/E3/h/S mathematics are unchanged. Independent
integration acceptance is not claimed.

The remaining boundaries are the actual Moise252 proof, full arbitrary
ambient/component/nonseparating Moise264 generality, and production of the
compression-ball wall/cap geometry for an arbitrary original-shell disk.
Arbitrary-shell Moise304 is not complete.


### M304 relative ball neighborhoods of the original spanning disk (2026-09-19 UTC)

The new registered SpanningDiskBallNeighborhood leaf proves two geometric
producers. exists_isPLBall_neighborhood_of_proper_disk starts with an actual
properly embedded PL disk in a finite WB3 K and a prescribed open U
containing that disk. Exhaustion and the native disk derived-neighborhood
theorem produce a finite PL3 ball B inside K and U, containing the entire
original disk and a relative neighborhood of every disk point. The disk
meets frontier B in exactly its original rim, and boundary K is a relative
neighborhood of that rim in frontier B.

exists_isPLBall_neighborhood_of_spanning_disk starts with the original
finite connected closed surface S inside a finite preconnected WB3 K in
ambient dimension three, and the actual original D/r in interior K with
D intersect S equal to its rim. Connectedness of the disk interior puts
the whole disk in one actual cut side; density recovers its boundary.
The first producer is applied on that side inside U intersect interior K.
It produces B containing the same D, with D minus S in interior B,
D intersect frontier B equal to the rim, S intersect B contained in
frontier B, and S a relative neighborhood of the rim in frontier B.
No relative product chart or final compression ball/cap package is an input.

The new actual-model consumer retains the original beta-two torus, ball,
h252-produced essential disk and U = interior K and checks all these
properties together. The geometric producers themselves do not use h252.
The audit separately retains two unconditional geometry models and three
h252-conditional consumers. All 17 declarations in the audited layer,
79 critical reuse entries, five models and three helpers have standard
transitive axioms; all 13 applicable linters and the final private audit
pass without diagnostics. The two new declarations and their actual
derived-disk and centered-prism dependencies have fresh private receipts.

Twenty-six source/object/receipt sets and complete audit evidence are frozen
at `C:/Users/liao9/AppData/Local/Temp/moise304-reading/relative-ball-checkpoint/`.
Manifest SHA256: `31444C22AB47B279280A535C0D73EB291839B2BE58F8A3409E4024B9F7277E8A`.
Final audit completion: 2026-09-19T19:34:51.8777909Z. The new native import graph has 508
modules and 1000 edges, is acyclic and avoids HurewiczLowDegrees.
This is a dependency-closed checkpoint inside the ongoing compression-ball
round. The smaller centered prism, exact side wall and disjoint cap
construction are not yet delivered by this checkpoint. No other lane
source or shared output is changed; the stopped root build is not restarted.


### M304 compression balls for the same original disk and shell (2026-09-19 UTC)

Done in this feature branch, pending independent integration acceptance:
the geometric compression producer no longer requires a supplied product
neighborhood, compression ball, side wall, caps, or equivalent final geometry.
The preceding relative-ball layer is checkpoint 714b1599a29980d7fb7e74571a838fbb26475ff5.

SpanningDiskPrism proves the centered-prism construction and its boundary
geometry. IsPLBall.exists_centered_prism_subset_of_boundary_neighborhood
uses the native centered-prism theorem on the same original D/r, then
compactness of the standard rim to choose one positive thickness whose
entire side wall lies in the original surface. Strictly smaller thickness
excludes both old end faces. Injectivity gives exact surface trace.
IsCombinatorialManifold.exists_centered_prism_neighborhood_of_spanning_disk
constructs the needed auxiliary ball internally from the original finite
connected closed surface and disk, in any prescribed open U containing D.
The auxiliary ball and cut side are not hypotheses of this public result.
IsPLHomeomorphOn.exists_wall_and_caps_of_centered_prism takes the two actual
end faces of that same prism and proves their disjointness, exact frontier
union, cap/wall intersections, and both labeled rim identities. Its
intermediate prism input is produced by the preceding theorem.

SpanningDiskCompression exposes
IsCombinatorialManifold.exists_compression_neighborhood_of_spanning_disk.
For the same D/r and S it returns N, W, D0/D1, f, rho, r0/r1, with
N a PL3 ball contained in U, D contained in N, D minus S inside interior N,
D intersect frontier N equal to the original rim, and N a relative
neighborhood of all D in S union D. The prism has f(x,0) = r(x).
S intersect N equals W; W is a relative neighborhood of the rim in S.
The rim parameterization satisfies rho(r(x),t) = f(x,t), fixes the rim at
t = 0, and matches the two cap boundary labels exactly. The caps are
disjoint and frontier N = W union D0 union D1. W and the caps are chosen
compatibly from this D, not from an arbitrary previously selected annulus.
The neighborhood proof uses only the annulus-complement leaf, without an
import of the higher compression-separation consumer.

SphericalShellCompression exposes
IsSphericalShell.exists_compression_of_essential_disk. It preserves the
given X, B0, B1, S, D/r and prescribed U, constructs all the above geometry
inside U intersect interior X, and applies the unchanged separation/Betti
consumer to produce an actual connected component P of the capped surface.
P remains in interior X, separates the same B0/B1, and has strictly smaller
bettiOne than S. No Loop Theorem hypothesis is needed once the actual
essential disk is supplied. Its sibling
IsSphericalShell.exists_separating_component_bettiOne_lt_of_loop_theorem
obtains that disk using the explicit h252 input and gives strict Betti
decrease for an arbitrary nonspherical connected separator in the same shell.

Verification: all three new modules compile without diagnostics; the
compression leaf and shell consumer were rebuilt after narrowing imports.
All 25 declarations in the cumulative native audit, 84 critical reuse
entries, eight actual models and three model helpers have only approved
foundational axioms. All 13 applicable linters pass. The eight models are
three unconditional models and five explicit-h252 conditional consumers.
The new unconditional and conditional compression models both retain a
nonempty actual disk in the original beta-two torus and shell with nonempty
targets, and quantify over every open neighborhood of that same disk.
They check all ball/wall/cap, centered parameterization, relative neighborhood,
component, target and Betti conclusions together. A separate conditional
model consumes the new arbitrary-shell strict-decrease theorem directly.

Thirty source/object/receipt sets and the complete audit are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/compression-checkpoint/`.
Manifest SHA256: `7FE6FE9B969793268DA6857A4880FA26962828724136D282FC88181C73CF5C4B`.
Final zero-diagnostic audit completion: 2026-09-19T19:59:17.5691222Z.
The native import graph has 907 modules and 1927 edges, is acyclic,
and avoids HurewiczLowDegrees. All three leaves are registered in the flat
root. The owner-stopped root build was not restarted; all output is private.
No other lane source or shared object is modified.

Remaining scope: the actual Moise252 proof, broader Moise264 generality and
the final arbitrary-shell Moise304 endpoint/integration are not claimed here.
The previously reported missing ball/wall/cap producer for an original
essential disk is closed by this round. Independent acceptance remains with
the coordinator; the feature branch audit is not an acceptance substitute.


### M304 arbitrary-shell sphere endpoint from the Loop Theorem (2026-09-19 UTC)

Author-verified in this feature branch; independent integration acceptance is
pending. The only native change is thirteen added lines in the existing
SphericalShellCompression leaf: moise304_of_moise252 (h252 : Moise252) : Moise304.
There are no deleted native lines, new modules, signature changes or extra
public wrapper declarations. MoiseChain, the E3 lane and the h-circle lane
are unchanged.

The exact conclusion quantifies over every original X, B0, B1 in Euclidean
three-space with IsSphericalShell X B0 B1, and constructs B with IsPLSphere 2 B,
B contained in interior X and Separates B B0 B1. The proof obtains an actual
connected separator minimizing bettiOne from the existing native selection
theorem. If it is not a sphere, the previous compression producer supplies a
connected separator with strictly smaller bettiOne in the same shell and for
the same targets, contradicting minimality. The supplied hypothesis is only
h252; no disk, annulus, compression ball, minimality or sphere is assumed.

The unchanged moise305_tame_of_moise304 consumes moise304_of_moise252 h252.
This gives the full existing Moise305Tame statement: the original two nested
topological cells and their shell, with a bicollared outer frontier, produce
an actual intermediate PL3 ball. Its native proof uses SphereNesting and the
proved PL Schoenflies chain. No extra Schoenflies hypothesis was introduced.

Two new explicit-h252 models use the concrete nonempty norm band 1 <= norm <= 2
and the same spheres of radii one and two. One constructs the separating PL2
sphere; the other constructs an actual PL3 ball containing the closed unit
ball in its interior and contained in the radius-two open ball. The latter
also verifies its nonempty PL2 frontier lies in 1 < norm < 2 and separates the
same targets. The outer bicollar is constructed by radial exponential scaling.
The previous three unconditional disk/ball/compression models are retained.
These conditional consumers do not independently prove Moise252.

The complete audit checks 31 nonautomatic native declarations, 91 critical
reuse entries, ten models (three unconditional, seven with explicit h252),
and three model helpers. All transitive axiom closures contain only the
approved foundational axioms; all 13 applicable linters pass. The endpoint,
unchanged tame consumer and SphereNesting have zero-diagnostic private
compile receipts. Other frozen dependency receipts retain their actual dates.

A separate kernel-body and type dependency traversal covers 9309 native
constants for moise304_of_moise252 and 7184 for the tame consumer. It includes
private declarations and records every edge and non-native boundary module.
Neither closure contains Moise303 or wide Moise264. Live source search finds
only the Moise264 definition in MoiseChain, not a use in this chain; no
Moise303 declaration is present in this checkout. The book route and E3's
separate 30.3 proof are therefore not prerequisites of this compiled route.
This does not claim the full wider Moise264 statement has been proved.

Thirty-three source/object/receipt sets and all evidence are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/shell-endpoint-checkpoint/`.
Manifest SHA256: `6D9EBB844D1C8660963E136D047B81C29BD62CD9F70D06F699EE47BEB59FDEE6`.
Final zero-diagnostic audit: 2026-09-19T20:22:52.2507249Z. The interval from the first successful
endpoint compile to this final audit is 782.934 seconds; it is not a
measurement of the entire round's effort. The source import closure contains
910 native modules and 1934 edges, is acyclic and avoids HurewiczLowDegrees.
The existing leaf remains registered in the unchanged flat aggregate.
The owner-stopped root build was not resumed; shared outputs were untouched.

Remaining inputs and acceptance: Moise252 is still an explicit upstream
input; Moise305Tame retains its bicollared-outer-frontier condition. Neither
unconditional Moise304 nor general Moise305 is claimed. The arbitrary-shell
conditional endpoint is now closed in the author lane, pending the
coordinator's independent replay and integration acceptance.


### M304 original toroidal-shell incompressibility and fundamental groups (2026-09-19 UTC)

Author-verified mathematical checkpoint; Moise306 and Moise307 remain open.
Six new leaves and one existing leaf contribute 595 added native lines,
zero deleted native lines, 34 source declarations and one generated local
notation constant. The flat aggregate gains exactly six imports. Existing
declarations in SurfaceEssentialDisk and all other earlier APIs are unchanged.
MoiseChain and other lanes are unchanged; independent integration is pending.

The new actual-kernel disk producer in SurfaceEssentialDisk takes a nonidentity
loop killed by the inclusion into its prescribed open neighborhood, without
an ambient simple-connectivity assumption. SurfaceIncompressibility then
constructs a lower-Betti connected separator for the same two targets from
that kernel. A minimal separator consequently has injective inclusion on
fundamental groups. All disk and compression geometry is produced using the
explicit upstream Moise252 input and the existing checked relative machinery.

Manifold.CylinderImage proves the interior and frontier formulas for embedded
compact manifold cylinders by invariance of domain. ToroidalShell applies
them to the original homeomorphism in IsToroidalShell Y T0 T1: frontier Y is
exactly T0 union T1, and interior Y is homeomorphic to the torus times (0,1).
It constructs a finite connected oriented two-sided PL2 separator in this
original interior and an actual minimum of bettiOne for these original
targets. ToroidalShellCompression's
IsToroidalShell.exists_connected_separating_surface_fundamentalGroup_map_injective
produces that separator with injective inclusion into interior Y from h252.
No minimum, sphere, torus, compression disk or classification is assumed.

FundamentalGroup.Torus computes the torus group at every basepoint as Z x Z.
ToroidalShellFundamentalGroup transfers this to both Y and interior Y and
proves both actual endpoint inclusions T0 -> Y and T1 -> Y induce bijections
on fundamental groups. These are the native group inputs for the book's
sphere-exclusion argument, not a completed sphere-exclusion theorem.

The new unconditional model starts from the existing actual embedded PL
torus, constructs its ambient bicollar, and restricts that embedding to a
closed unit cylinder. Its shell, interior and both targets are nonempty;
the targets are disjoint; its interior is proved not simply connected.
A second unconditional model constructs its minimum separator. A third,
with explicit h252, constructs an incompressible separator of exactly those
same targets and proves its fundamental group commutative. No standard
shell is substituted for the arbitrary shell in the public results.

The cumulative audit checks 66 nonautomatic native constants (including the
local notation constant), 106 critical reuse entries, thirteen models (five
unconditional, eight with explicit h252), and four model helpers. Every
checked transitive axiom closure uses only the approved foundational axioms,
and all 13 applicable linters pass. Every changed leaf has a private compile
receipt with zero diagnostics. Kernel type-and-body traversals for the
separator, interior group computation and left endpoint inclusion contain
no Moise303 or wide Moise264. The source import closure has 912 native
modules and 1938 edges, no cycles or HurewiczLowDegrees.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/toroidal-checkpoint
contains 39 source/receipt sets, raw and normalized source identities,
AuditToroidal.lean, toroidal-census.json, ToroidalModels.lean, source review,
compiled dependency closures and timing. Manifest SHA256: 215C4D6BFEE73F394D4B8908EB424E518FD5BFAEDAB99EABAE3827865521560C.
Final zero-diagnostic audit: 2026-09-19T21:07:56.0084065Z. The compile-to-audit window is
1660.493 seconds, not total effort.
The owner-stopped root build remains stopped; shared artifacts are untouched.

The remaining geometric obligations are exact: (1) a PL2 sphere in interior Y
cannot separate T0 and T1, using the actual cut sides and the endpoint group
isomorphisms; (2) a connected closed orientable finite PL2 surface with the
resulting nontrivial fundamental group embedded in Z x Z is homeomorphic to
S1 x S1. The current SurfaceInvariants API computes counts from an already
supplied handle profile; it does not construct that profile or a torus
homeomorphism. SurfaceSphereRecognition handles Euler characteristic two,
not the required Euler-zero orientable case. Betti number two alone has not
been used as torus recognition. Work toward these obligations continues;
this checkpoint does not claim Moise306, Moise307 or Moise252 complete.


### M304 parity and commutative-cover primitives; exact recognition frontier (2026-09-19 UTC)

The preceding original-shell layer is committed and pushed as
6f227c0576feb906bb14e8bb693bc8e7d0fdaf72. Its 39 frozen source/receipt sets were
checked again against working-tree raw bytes, committed normalized bytes,
and all artifact hashes. This follow-on layer adds two registered leaves,
three proved declarations and 90 native lines, with zero deletions or
changes to previous declarations. Across the toroidal round this is
685 native lines, eight new leaves and 37 source declarations plus
one generated local-notation constant.

SurfaceEulerParity proves
IsCombinatorialManifold.even_eulerChar_of_finrank_eq_three and
IsCombinatorialManifold.even_bettiOne_of_finrank_eq_three for any connected
finite closed PL2 surface in a three-dimensional real normed space.
The proof produces its actual bounded PL3 filling with that exact boundary,
uses the boundary Euler formula, and uses the already proved orientability
and rational Euler-Betti formula. No handle profile or parity assumption is
introduced. The added unconditional models check an actual embedded torus
and the actual minimum separator in the non-simply-connected shell model.

FundamentalGroup.CommutativeCover proves
simplyConnectedSpace_or_of_open_cover_of_isMulCommutative. For a two-set
open cover with path-connected sides and simply connected intersection,
commutativity of the ambient fundamental group forces at least one side
to be simply connected. The proof applies the native van Kampen free-product
isomorphism and proves two nonidentity letters from different factors cannot
commute by uniqueness of reduced words. Ambient simple connectivity is not
an assumption. This closes the group's free-product obstruction on book
page 217, but does not yet construct the actual cut cover of the original Y.

The round reaches two explicit geometric frontiers. First, for the ORIGINAL
IsToroidalShell Y T0 T1, prove that no IsPLSphere 2 S with S inside interior Y
can satisfy Separates S T0 T1. Required construction: the closures of the
two components of Y minus S, their path connectivity and regular-closed
properties, a collar contained in original Y, the corresponding open cover,
and factorization of the two actual endpoint maps through their own sides.
The group isomorphisms and commutative-cover obstruction are proved; the
closed-cover kernel theorem is for actual nontrivial boundary kernels and
cannot substitute for this sphere case. The older negative/positive collar
cover intersection API assumes the ambient space simply connected and
therefore cannot be instantiated at this toroidal Y.

Second, construct a torus homeomorphism for a connected closed orientable
finite PL2 surface with nontrivial commutative fundamental group (here it
embeds into Z x Z). The weaker intermediate numerical statements do not
give that homeomorphism. SurfaceInvariants only starts from a supplied
handle/crosscap profile; SurfaceSphereRecognition only treats Euler
characteristic two. A native polygonal presentation/classification or a
proved orientable Euler-zero torus-recognition construction is missing.
The PI1-to-integral-H1/abelianization step used by the book is also not
supplied by the checked path-cone vanishing API. No blocked HurewiczLowDegrees
import, new axiom, sorry or conclusion-shaped hypothesis has been added.

Moise306 remains PARTIAL at these actual geometric interfaces. Moise307 is
not started, in accordance with the required 30.6 -> 30.7 order. Neither the
incompressible separator nor parity is reported as IsPLTorus, and the
explicit upstream Moise252 input remains unresolved. Independent integration
acceptance remains pending.

Final cumulative verification: 69 nonautomatic native constants, 112 critical
reuse entries, fifteen actual models (seven unconditional, eight with h252),
four model helpers, and all 13 applicable linters. All audited axiom closures
contain only the approved foundational axioms; changed-module compiles and
the full audit have zero diagnostics. Five kernel body/type traversals show
no Moise303 or wide Moise264. The source graph has 940 native modules
and 2019 edges, with no cycle or HurewiczLowDegrees.
The owner-stopped root build was not run; shared outputs remain untouched.

Frozen final evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/recognition-final-checkpoint
contains 41 source/receipt sets, the complete audit/census, actual models,
kernel dependency reports and source/timing review. Manifest SHA256:
D04395C683F14D90E0886B7F637B0E536E8E7F6DC1F6103CF98120009B7D9F87.
Final zero-diagnostic audit: 2026-09-19T21:21:28.6825480Z; 2473.167 seconds since the first
successful changed-module compile, not a measurement of total effort.


## M304 original toroidal-shell sphere exclusion checkpoint, 2026-09-19

This entry supersedes the sphere-exclusion frontier of checkpoint 8236587e5.
The arbitrary ORIGINAL IsToroidalShell Y T0 T1 now satisfies
IsToroidalShell.not_separates_of_isPLSphere: an IsPLSphere 2 S contained
in interior Y cannot separate the original endpoint sets T0 and T1.
This theorem has no Moise252 input. The finite-surface corollary
IsToroidalShell.not_simplyConnectedSpace_of_separates also has no Moise252
input. Combining it with the existing minimum/compression producer gives
IsToroidalShell.exists_non_simply_connected_separating_surface_fundamentalGroup_map_injective
with the same explicit h252 input as before.

The sphere proof constructs the Schoenflies ball D with frontier D = S.
Its actual closed sides in Y are P = val^(-1)(D) and
Q = val^(-1)((interior D)^c). Frontier S inside interior Y gives the exact
relative closure equalities closure(P \ Q) = P and closure(Q \ P) = Q.
A given sphere collar is shrunk into interior Y and codomain-restricted to Y.
The collar determines an open cover whose intersection is exactly its range.
Connectedness of the closed sides follows from the connected closed-cover
intersection; open collar neighborhoods are path connected and retract to
the actual sides. No side, regularity, connectivity, intersection identity,
kernel, or non-sphere hypothesis is supplied by the caller.

The simply connected sphere makes the collar intersection simply connected.
The commutative-cover obstruction therefore makes P or Q simply connected.
Schoenflies component connectivity and the ORIGINAL separation relation put
T0 and T1 in opposite actual sides. Each actual endpoint inclusion T_i -> Y
is written as T_i -> P -> Y or T_i -> Q -> Y. A simply connected middle
space makes its fundamental-group map trivial, contradicting the checked
surjectivity of that actual endpoint map onto pi1(Y) isomorphic to Z x Z.
All pre-existing public signatures are preserved; the old closed-cover kernel
proof now reuses the extracted open-cover construction.

Changes: 389 native lines added, 53 removed; eleven new declarations,
four new leaf modules registered in the flat root, eight changed native modules.
Cumulative verification covers 87 nonautomatic native constants, 119 critical
reuse entries, eighteen actual models (nine unconditional and nine conditional
on h252), four model helpers and all thirteen applicable linters. Every audited
axiom closure is a subset of propext, Classical.choice and Quot.sound. Fresh
changed-module compilation and the complete audit produced zero diagnostics.
Nine exact kernel type/body dependency traversals contain no Moise303 or wide
Moise264. The source import graph has 951 modules and
2049 edges, with no cycle or HurewiczLowDegrees.
The explicit owner stop on the root build remains in force. Shared outputs
were not changed. Independent integration replay is still pending.

The remaining Moise306 frontier is the actual torus homeomorphism of the
produced connected closed orientable finite PL surface, now proved non-simply
connected and with fundamental group injecting into pi1(interior Y) = Z x Z.
SurfaceSphereRecognition supplies only Euler-characteristic-two recognition;
SurfaceInvariants consumes a supplied handle/crosscap profile. Neither proves
the needed torus recognition. The checked PathCones/FieldPathCones API proves
degree-one homology vanishing under simple connectivity, not the general
pi1-to-integral-H1 abelianization comparison needed by the book's rank argument.
No numerical invariant or supplied profile is being counted as IsPLTorus.
Moise307 remains unstarted, and Moise252 remains an explicit unresolved input.

Before later Moise307/308 consumers, repair the Moise308 spine contract:
the book's inner S1 spine must generate pi1 of every intermediate S through
the actual inclusion map. The current contract assumes a spine of intermediate
S itself. Preserve that true result, add the missing inclusion transport, and
do not consume Moise312/314 until this transport is proved. MoiseChain was not
edited in this checkpoint.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/sphere-exclusion-checkpoint
45 source/receipt groups. Manifest SHA256: 69B2B74D52D5C659058B905AB9B216AF35F0FAF4CDAB3F5B14EB22E04ABFE701.
Complete zero-diagnostic audit: 2026-09-19T21:54:51.8379979Z.
Kernel dependency audit: 2026-09-19T21:57:34.0194709Z.


## M304 degree-one Hurewicz homomorphism checkpoint, 2026-09-19

The original toroidal-shell sphere exclusion from 87826c69c remains unchanged.
A general integral degree-one Hurewicz homomorphism now exists for every
based topological space. hurewiczOne_surjective proves its surjectivity for
every PathConnectedSpace, with no simple connectivity, manifold, compactness,
local path connectivity, or finite complex assumption.

PathConcatenation gives an explicit singular triangle for any composable
paths; its boundary is q - (p.trans q) + p. PathHomotopy triangulates an
arbitrary endpoint-fixed path homotopy into two singular triangles, with
constant-path corrections, and proves that homotopic path chains differ by
a boundary. HurewiczOne descends the resulting loop class to the actual
fundamental group, respecting Mathlib's reversed concatenation convention.
Surjectivity closes every singular edge using chosen basepoint paths; their
endpoint corrections cancel for every cycle. The proof compares the actual
linear maps on the singular-chain basis and then uses the cycle quotient.

Three new leaf modules, 384 native source lines, eighteen public and four
private declarations; all three are registered in the flat root. Every
changed module compiled with zero diagnostics. The cumulative main audit
checks 109 native constants, 133 critical reuse entries, twenty models and
four helpers under all thirteen applicable linters. A separate checked model
adds two reuse entries and one actual circle model: there exists an actual
loop whose integral homology coordinate is exactly 1, using the independently
checked sphere top homology equivalence. The other two new models exercise
surjectivity on the circle and torus with explicitly nontrivial fundamental
groups. Thus the cumulative evidence has 135 reuse entries and twenty-one
models (twelve unconditional, nine retaining h252).

All checked axiom closures contain only a subset of propext,
Classical.choice and Quot.sound. Twelve actual kernel type/body dependency
traversals are nonempty and avoid Moise303 and wide Moise264. The native
source import graph has 954 modules and 2052 edges,
with no cycle or HurewiczLowDegrees. No shared outputs were changed. The
explicit owner root-build stop remains in force; integration replay is pending.

This checkpoint proves the map and its surjectivity, not the abelianization
isomorphism, rational coefficient comparison, Betti-one rank bound, or actual
surface-to-torus homeomorphism. Those remain the Moise306 recognition frontier.
Moise307 is not yet started. Moise252 remains an explicit unresolved input.
The earlier Moise308 original-inner-spine inclusion-transport obligation is
unchanged; MoiseChain and other lanes were not edited.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/hurewicz-one-checkpoint
48 source/receipt groups. Manifest SHA256: 53E017AC78CAC17877AF7EF20F662CFB3602F1E09405B05B4884F4F01E891D84.
Main audit: 2026-09-19T22:35:19.9060986Z.
Circle model audit: 2026-09-19T22:39:46.2922313Z.
Kernel dependency audit: 2026-09-19T22:33:14.9531106Z.
