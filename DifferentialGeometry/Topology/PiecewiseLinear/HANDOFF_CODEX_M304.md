# Spherical-shell proof lane

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

Independent visual review of printed page 216 confirms the disconnected
compression inequality is p1(M2) <= p1(M1) - 2. The extracted PDF text lost
the lower stroke and was initially misread as a strict inequality; this was
an OCR error, not an error in the book. The weak bound is sharp for a
separating compression of a genus-two surface into two tori. The formal
induction should prove this bound and hence strict decrease from p1(M1).

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
