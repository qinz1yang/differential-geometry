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
