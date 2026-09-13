# Tau Ceti proof adaptations

These native modules adapt Apache 2.0 source from
[Tau Ceti at 3358033ba2fd35f321356dceaf2372a0fd6c0bfd](https://github.com/TauCetiProject/TauCeti/tree/3358033ba2fd35f321356dceaf2372a0fd6c0bfd).
The repository LICENSE supplies the license text. Original copyright and
author headers remain in the Lean files; NOTICE also records attribution.
The upstream root NOTICE path returns 404 at this pinned revision.

| Native module | Upstream source and authors |
| --- | --- |
| Analysis/Calculus/Sard | [Sard/EqualDimension.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Sard/EqualDimension.lean), Joseph Tooby-Smith and Codex |
| Topology/Morse/Generic | [Morse/Generic.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Analysis/Calculus/Morse/Generic.lean), The Tau Ceti contributors |
| Topology/Embedding/SliceChart | [LocallyFlat/Smooth.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/LocallyFlat/Smooth.lean), The Tau Ceti contributors |

The Haar-null transport also adapts
[Haar/NormedSpace.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/MeasureTheory/Measure/Haar/NormedSpace.lean),
Copyright 2026 The Tau Ceti contributors, under the same license.

## Local modifications, 2026-09-13

The port uses the existing Lean 4.33.1 and Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. No Tau Ceti dependency is installed;
its 4.34.0-rc2 environment is not substituted for the local pins.
Upstream module-system syntax and explanatory docstrings are removed while
the required attribution headers are preserved.

The Sard proof uses Mathlib's actual Jacobian null-image theorem, constructs
the domain Borel structure locally, and transports Haar-null sets through a
continuous linear equivalence. Source and target may have different norms
and universes, with equal finite dimension. Rank zero and empty sets are allowed.

The Morse proof uses DG's existing IsCriticalPointAt,
IsNondegenerateCriticalPointAt and native quadratic Hessian. It introduces
no competing critical-point vocabulary. Actual second-derivative surjectivity
implies the native Hessian's separating condition. Public results give almost
everywhere, density and arbitrarily small operator-norm perturbations on the
original open set. Tangent-space coercions, obsolete lemma names and the
quadratic consumer were adapted to the pinned compiler. Mechanics stay private.

The slice-chart proof retains the two open restrictions from Tau Ceti: one
forces slice points to belong to the immersion chart, and the other excludes
distant branches of the embedded range. It uses native immersion charts and
returns an OpenPartialHomeomorph with ContMDiffOn laws for both directions.
Its exact image equation uses the entire range of the given map. The source
may have corners; only the ambient model must be boundaryless. The general
engine needs a topologically inducing map and an immersion at the given point;
the smooth-embedding method is its corollary. No Tau embedding, slice or local
flatness definitions are imported. Continuous-linear-equivalence smoothness
and the Euclidean sphere's dimension instance were adapted to the pinned APIs.

## Verification

Source request 1789297179397566825-schoenflies-73efb952 passed in Slurm 13821107
on della-r3c4n2 in 35.43 seconds: 28 guards and eight signature/axiom pairs.
Imported gate 1789297419650760082-schoenflies-50b26acf passed in 112.58 seconds,
with 31 guards and six public/consumer pairs matching the source readbacks
except Function.Surjective qualification. Both new modules freshly compiled
offline in 1:18.39 with zero diagnostics.

The imported DG declarations and consumers pass unusedArguments, simpNF,
synTaut and checkType. defLemma is unavailable in this pinned Mathlib; source
declaration-kind review is retained. All audited transitive axioms lie in
propext, Classical.choice and Quot.sound. Consumers exhibit the actual critical
point of a perturbed real quadratic and a nondegenerate point of a constant
function on the rank-zero model. Both leaves are registered in the flat root.
These checks are not a completed full DifferentialGeometry aggregate build.

The slice-chart source gate, 1789301170338217570-schoenflies-b3900a3e, passed
in the same Slurm allocation in 34.41 seconds, with 14 guards and five
signature/axiom pairs. The final imported gate,
1789301267798740740-schoenflies-d05544f3, passed in 81.91 seconds, with 16
guards and five pairs. The new module freshly compiled with zero diagnostics;
artifact generation took 50.32 seconds with maximum RSS 1639036 KiB.
Both public methods and all three consumers have standard-only transitive
axioms and pass the stock declaration linters listed above. Consumers cover
an arbitrary smooth embedded two-sphere, the actual unit sphere inclusion,
and a model-with-corners inclusion. The leaf is registered in the flat root;
this is a fresh leaf and imported-source gate, not a full aggregate build.
Local slice charts do not establish a global tubular neighborhood or ambient
isotopy extension.

## Native local retraction, 2026-09-13

Topology/Embedding/Retraction consumes the accepted slice-chart theorem and
constructs an open neighborhood stable under projection onto the embedded
slice. The original source manifold is recovered through Mathlib's embedding
homeomorphism and its immersion criterion for smoothness. The resulting map
is smooth, its embedded image remains in the same neighborhood, and it fixes
every source point whose image lies in that neighborhood. Both source and
ambient models are boundaryless. No replacement smooth structure is introduced.

This is original native glue. Inspected proof patterns include the coordinate
projection and immersion-lifting step in Tau Ceti's
[Boundary/Collar/Diffeomorph.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/Boundary/Collar/Diffeomorph.lean#L105)
and the native embedding inverse in
[LocallyFlat/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/3358033ba2fd35f321356dceaf2372a0fd6c0bfd/TauCeti/Geometry/Manifold/LocallyFlat/Basic.lean#L754).
Those sources belong to The Tau Ceti contributors under the same Apache 2.0
license. Their supplied collar structures are not imported or assumed here.

Source gate 1789302206549346026-schoenflies-1067041b passed in 3.43 seconds
with 16 guards and three signature/axiom pairs. Imported gate
1789302368061612316-schoenflies-b705f016 passed in 73.77 seconds with 18
guards and three pairs. The new module freshly compiled without diagnostics;
the public method and arbitrary-embedded-S2 and unit-sphere consumers pass
the stock declaration linters and standard-only transitive axiom checks.
The leaf is registered in the flat root. These checks do not establish a
full aggregate build, a global retraction, or a joint-time tubular neighborhood.

Distinct critical values, global positioning of an embedded sphere, smooth
relative disk absorption and full Schoenflies remain open.

## Graphs of compact parameterized families, 2026-09-13

Topology/Embedding/ParametricGraph proves properness of the actual map
(t,x) ↦ (t,e(t,x)) for jointly continuous e, compact X and Hausdorff target Y.
Fiberwise injectivity gives a closed embedding. The parameter space need not
be compact or Hausdorff. These two general topological results use the pinned
Mathlib proper-projection and ultrafilter APIs; this is original glue, with
no copied Tau Ceti or Lean Pool code.

The private source check 1789303104679795989-schoenflies-cc7d654a passed in
31.29 seconds with 11 guards and five signature/axiom pairs. Final imported
check 1789303194374561190-schoenflies-af96cedc passed in 47.28 seconds with
15 guards and five pairs; all five exact types match the source check.
Fresh leaf artifact generation took 17.46 seconds, maximum RSS 996164 KiB,
with zero diagnostics. Stock declaration linters and standard-only axioms
pass. Consumers use an arbitrary smooth family of embedded two-spheres,
the actual unit sphere and a singleton fiber over any topological parameter.
The first also retains joint smoothness of the actual graph. The leaf is
registered in the flat root; no full aggregate build is claimed.

The native smooth-immersion step is now supplied by
Topology/Embedding/SmoothParametricGraph. For a jointly smooth family of native
smooth embeddings of a compact boundaryless manifold into finite-dimensional
real normed space, it proves that the actual parameterized graph is a native
smooth embedding. The parameter space may be any real Banach space. The
fixed-complement immersion engine requires no compactness of the source.
Topology/Embedding/FiniteDimension derives a chosen normal complement of the
correct codimension from a native immersion at any order, over a complete
nontrivially normed field and with arbitrary corners. Source-model finite
dimensionality is derived locally; no source nonemptiness is assumed.

The graph proof reuses the published local retraction, the existing parameter
inverse-function engine and the existing local-diffeomorphism transport proof.
An eight-line wrapper preserves the fixed normal complement without copying
that transport proof. All six previous public transport statements and bodies
are retained. This is original glue; no additional upstream source was copied.

Private graph check 1789305462130027714-schoenflies-30a41974 passed in 34.30 seconds,
with 30 guards and 17 pairs. Public source 68465e15 passed in 36.98 seconds,
with 28 guards and 17 pairs. Imported check
1789305862830682920-schoenflies-6e6d83c9 passed in 105.89 seconds,
with 56 guards and 13 pairs.
All public and consumer types retain their source content, with scoped notation
expanded by the imported driver. The three changed/new leaves freshly compiled
in 1:14.56, maximum RSS 1704808 KiB, with zero diagnostics. Imported-package and
consumer declaration linters and standard-only transitive axioms pass. Probes
include an arbitrary actual S2 family with literal real complement, the unit
sphere, and a noncompact real-line identity family with zero codimension.
Both new leaves are registered in the flat root; no full DG aggregate build
is claimed. Compact velocity extension, relative vanishing, time endpoints,
source boundary faces and arbitrary ambient isotopy extension remain separate.

## Extension from an embedded subset, 2026-09-13

Topology/Embedding/Extension proves a global Cⁿ extension of a native Cⁿ map
from a subset whose embedded image is closed. For a compact subset it produces
an extension with compact topological support inside any prescribed open set
containing the image. Orders include every finite order and C∞. The source
uses its actual boundaryless model; the ambient is a finite-dimensional real
normed space, and the values lie in any real normed space. Neither compactness
of the entire source nor completeness of the value space is assumed.

The proof composes with the existing local retractions, uses pinned Mathlib's
smooth partition-of-unity gluing of convex value constraints, then applies its
smooth cutoff between the compact image and a compact neighborhood. The exact
extension equation and actual support inclusion remain public. This is original
native glue; no additional upstream source or dependency was copied.

Public source check 1789306923296827846-schoenflies-dbd64b12 passed in
36.20 seconds with 18 guards and six signature/axiom pairs. Final imported
check 1789307005086953798-schoenflies-6a6370ef passed in 73.18 seconds with
20 guards and six pairs. All six readbacks preserve their exact mathematical
content, with only scoped notation and formatting differences. The fresh leaf
compiled without diagnostics in 41.26 seconds, maximum RSS 1772716 KiB.
Stock declaration linters and standard-only transitive axioms pass. Consumers
check an arbitrary embedded S² map, the actual nonzero unit-sphere identity,
the identity on a compact interval in a noncompact source, and order zero.
The new leaf is registered in the flat root. This is not a full aggregate build
or an ambient isotopy-extension theorem. Time endpoints and source boundaries
remain separate. The subsequent velocity and relative-extension layers are
described below.

## Compactly supported velocity along an embedding family, 2026-09-13

Topology/Embedding/ParametricVelocity constructs the actual jointly smooth
spatial velocity field for a whole-real C∞ family of native embeddings of a
compact boundaryless manifold. On any compact part of its spacetime graph,
the produced field equals the actual time derivative of the given family.
Its topological support is compact and lies in a prescribed open neighborhood
of that trace. The interval statement is a thin specialization to Icc × univ;
empty intervals are included. Native manifold structures are retained.

The proof uses the published graph embedding and smooth extension. The existing
partial-derivative proof is generalized once in Bundle/PartialMfderiv as the
natural method ContMDiff.deriv_fst, for arbitrary normed real values. The old
scalar DifferentialGeometry.contMDiff_partial_deriv_fst has exactly its former
public signature and is now a thin corollary. Original scalar and scalar-slice
consumer readbacks match the independent baseline byte for byte. Existing
analytic call sites and their source files remain unchanged. Their full source
closure has 1178 missing artifacts; no broad analytic rebuild is claimed.

Private velocity check 1789307469075330896-schoenflies-5dc551d3 passed in
34.68 seconds with 36 guards and eight pairs. Final public source check
1789307867190354247-schoenflies-6d437c67 passed in 33.42 seconds with 65 guards
and nine pairs. Final imported check
1789308065595270119-schoenflies-8d9030c4 passed in 102.05 seconds with 67 guards
and nine byte-identical pairs. Both changed/new leaves freshly compiled without
diagnostics in 1:05.34, maximum RSS 1784880 KiB. Stock declaration linters and
standard-only transitive axioms pass. Consumers include arbitrary embedded S²
families, a translated unit sphere whose exact velocity is the supplied vector,
and an empty interval with empty support. The new leaf is in the flat root.
These are fresh module/source checks, not a full aggregate build.

This uses existing native proofs; no additional upstream source or dependency
is copied. The whole-real smoothness hypothesis remains essential to this
statement. Extension from interval-only data and source boundary faces remains
open. Relative fixing of the velocity remains separate from the relative
function extension below; the ambient isotopy specialization follows afterward.

## Relative support for embedded smooth extensions, 2026-09-13

The compact extension now needs only the image of K intersected with the
input function's topological support to lie in the prescribed open set.
A second method produces an open neighborhood of a closed fixed set on which
the extension vanishes, provided that fixed set misses the active image.
The original full-image method retains its exact public signature as a thin
corollary. Both results cover finite smoothness orders and C∞, arbitrary
normed values and noncompact boundaryless source manifolds. They reuse the
existing compact bump producer, removing the repeated cutoff construction.

Source request 1789309035946733917-schoenflies-9ec53756 passed in 36.42 seconds,
with 71 guards and 20 signature/axiom pairs. Final imported request
1789309174856603358-schoenflies-cf3c89bf passed in 108.61 seconds, with 74 guards
and the same 20 byte-identical pairs. All nine previous velocity/scalar pairs
remain byte-identical. Extension and its velocity dependent freshly compiled
without diagnostics in 1:10.23, maximum RSS 1787880 KiB. Stock declaration
linters and standard-only transitive axioms pass. Consumers retain all earlier
extension and velocity probes and add nonempty zero data with empty ambient
support at order zero and an actual nonzero smooth transition that vanishes
near a specified closed half-line. The existing root imports remain unchanged.
This is a fresh affected-module and consumer gate, not a full aggregate build.

## Ambient extension of an embedding family, 2026-09-13

Topology/Embedding/AmbientIsotopy extends a jointly C∞ whole-real family of
native embeddings of a compact boundaryless manifold into finite-dimensional
real normed space. It produces actual ambient diffeomorphisms, jointly C∞
forward and inverse evaluations, identity at the initial time, both exact
embedding equations on the chosen closed interval, and one compact spatial
support inside a prescribed open neighborhood of the trace for all real times.
The existing velocity and time-dependent flow supply the construction;
Mathlib's closed-interval ODE uniqueness with right derivatives proves matching.
No second flow framework, supplied velocity certificate or upstream code is added.

Private source request 1789309381212917316-schoenflies-95698f64 passed in
36.34 seconds with 69 guards and 13 pairs. Public source request
1789309501970504343-schoenflies-9857864e passed in 41.37 seconds with 127 guards
and 13 pairs. Final imported request
1789309621101432454-schoenflies-f108b7e8 passed in 86.20 seconds with 129 guards
and 12 public/consumer pairs, all byte-identical to the public source. The leaf
freshly compiled without diagnostics in 45.99 seconds, maximum RSS 1805112 KiB.
Stock declaration linters and standard-only transitive axioms pass. Consumers
retain every conclusion for arbitrary embedded S² families, derive a nonidentity
endpoint for a genuinely translated sphere, and force identity at all times
from the empty interval and empty support. The leaf is registered in the flat
root; this is not a full aggregate build.

This proves the stated whole-real, boundaryless, Euclidean-ambient specialization.
The stronger interval-only, boundary/corners and general-ambient versions in
Chapter 42 remain open. An embedding family taking an arbitrary sphere to the
round sphere is still required for Schoenflies; isotopy extension does not
produce that family.

## Relative ambient isotopy, 2026-09-13

The velocity and ambient isotopy constructions now require only the image of
points in the topological support of the actual time derivative to lie in the
prescribed open set. They still match the entire chosen compact set or time
interval. A closed set disjoint from this active image has a produced open
neighborhood fixed by both the isotopy and its inverse at every real time.
The original three public signatures remain thin compatible corollaries.
The existing embedded extension and time-dependent flow proofs are reused.

Source request 1789310722740437247-schoenflies-2cb3d58b passed in 50.12 seconds
with 136 guards and 31 signature/axiom pairs. Final imported request
1789310981089422100-schoenflies-faf431fc passed in 120.12 seconds with 134 guards
and 30 public/consumer pairs, all byte-identical to the source readbacks. All
nine earlier velocity/scalar pairs and twelve earlier ambient-isotopy pairs
remain byte-identical. Both changed leaves freshly compiled without diagnostics
in 1:11.73, maximum RSS 1812824 KiB. Stock declaration linters and standard-only
transitive axioms pass. Consumers include a stationary sphere with empty support
and identity at all times, and a nontrivially translated sphere fixing an actual
neighborhood of a sufficiently distant point. The existing flat-root imports
are unchanged. These are fresh affected-module checks, not a full aggregate build.

Whole-real smooth input, boundaryless source and finite-dimensional Euclidean
ambient space remain the stated scope. The stronger interval-only and boundary
versions and the sphere-rounding family required for Schoenflies remain open.

## Stability of compact manifold embeddings, 2026-09-13

Topology/Embedding/Stability proves that a jointly Cⁿ family has native Cⁿ
embedding slices near any one embedded slice, for n : ℕ∞ with n ≥ 1.
The parameter and ambient spaces may be arbitrary finite-dimensional real
normed spaces. The compact source is a native boundaryless Cⁿ manifold;
no source finite-dimensionality, nonemptiness, derivative estimate or supplied
extension certificate is assumed. The old whole-real C∞ target is a direct
specialization. This is local stability, not an assertion about all parameters.

Analysis/Calculus/LipschitzFamily supplies the general C¹ analytic engine:
for a jointly C¹ compactly supported function on arbitrary real normed
parameter, spatial and value spaces, the difference from a fixed slice is
uniformly ε-Lipschitz in space for nearby parameters. Compact uniformity and
Mathlib's mean-value theorem prove the bound. The geometric theorem extends
the family along the fixed initial embedding, then uses the existing
Diffeomorph.addLipschitz and native embedding postcomposition. No second
immersion or function-space framework is introduced.

Private generalized request 1789311821322070080-schoenflies-1bd256e3 passed
in 35.87 seconds with 40 guards and 18 readbacks. Public source ca8d102a passed
in 7.86 seconds with 42 guards and 18 pairs. Imported request
1789312288798658195-schoenflies-4b578ec9 passed in 102.44 seconds with 45 guards
and 18 pairs, all byte-identical to the public source. Both leaves freshly
compiled without diagnostics in 1:05.02, maximum RSS 1764484 KiB, after adding
the analytic leaf's explicit ContDiff.Operations import. After removing one
trailing blank line, final imported request
1789312563889506874-schoenflies-19041c33 passed in 75.32 seconds with all 45
current source guards and 18 byte-identical pairs. The changed analytic leaf
freshly compiled without diagnostics; artifact checking took 37.54 seconds,
maximum RSS 1497988 KiB. Stock declaration linters and standard-only transitive
axioms pass. Exact readbacks resolve the printed isCompact_closedBall alias
to ProperSpace.isCompact_closedBall.

Six consumers cover arbitrary S² families, a shrinking sphere that ceases to
embed at time one, rank-zero source, empty source, C¹ families with two real
parameters, and rank-zero parameter space. Both leaves are registered in the
flat root without changing existing imports. These are fresh leaf and consumer
checks, not a full DG aggregate build. Interval-only extension and source
boundary/corner extension remain separate requirements for Chapter 42.

## Smooth manifold maps from closed time intervals, 2026-09-13

Topology/Manifold/IntervalExtension proves
Manifold.exists_contMDiff_extension_Icc: an actual jointly C∞ map given only
within Icc a b times a native boundaryless manifold extends to one whole-real
jointly C∞ map agreeing throughout that closed interval. The real source model
is finite-dimensional; the manifold is Hausdorff and sigma compact, and the
values may be an arbitrary real Banach space. No compact source or ordered
endpoints are required. A singleton uses the actual spatial slice, and an empty
interval permits vacuous agreement. The positive-interval proof stays private.

The proof reuses the existing BorelHalfLineParam construction, native extended
charts and Mathlib's smooth convex-selection theorem. The latter glues local
extensions while fixing every prescribed value. Root inspected the full
1345-line parametric Borel proof, full 325-line BorelHalfLine and 162-line mixed-jet
matching source, the decisive DirectionalJet derivative-commutation body and
the actual partition-of-unity selection construction. Borel rescaling depends
on the degree; geometric derivative bounds produce one jointly smooth series.
Both endpoint seams match every mixed jet. Tangential chart coordinates are
interior points because the source is boundaryless. These are actual reused
proofs, without installing or upgrading dependencies. The four missing old
artifacts compiled offline in Slurm 13821107 in 2:33.05, RSS 2019788 KiB, with zero
diagnostics.

Private request 03eafb96 passed in 39.60 seconds with 39 guards and 14 pairs. Public source
1789313621356943063-schoenflies-747fbd47 passed in 34.97 seconds with 39 guards and 14 pairs. Final import
1789313711633052192-schoenflies-afd3ed69 passed in 114.89 seconds with 40 guards and 13 pairs, all
byte-identical to the public source. The public leaf freshly compiled without
diagnostics; artifact checking took 1:16.07, RSS 1794604 KiB. Stock declaration
linters and standard-only transitive axioms pass. Five consumers cover arbitrary
sphere maps, a translated sphere discontinuously truncated outside the closed
interval with both endpoint values preserved, noncompact source and arbitrary
Banach values, a rank-zero singleton and an empty interval. The new leaf is
registered in the unchanged flat-root import list. This is a fresh leaf and
consumer check, not a full DG aggregate build. Source-boundary/corner extension,
embedding preservation and the full Schoenflies theorem remain separate.

## Embedding families from closed time intervals, 2026-09-13

Topology/Embedding/IntervalExtension now produces a whole-real smooth family
of native embeddings from joint smoothness and embedding slices only on a
nonempty closed time interval. Agreement holds on the entire original interval,
including both endpoints. Compact boundaryless source and finite-dimensional
real ambient space are the natural hypotheses; source finite dimension and
Hausdorffness are derived locally from an actual embedding when the source is
nonempty. An empty source is handled independently. Singleton intervals work.
Empty interval data alone cannot produce an embedding, as a sphere-to-point
consumer verifies, so the family theorem correctly requires a <= b.

The proof reuses the published map extension and local embedding stability.
It obtains a larger OPEN interval of embedded slices and composes with a smooth
time map fixing the original interval. Analysis/Calculus/SmoothExtension/ConvexOpen
provides the natural general helper: a smooth map into a nonempty convex open
set fixing a prescribed compact subset. The existing compact bump constructs
it by convex interpolation. No smooth retraction onto a closed interval is
asserted. The two new leaves are 67 and 28 lines and are registered in the root.

Public source request 1789314346667667796-schoenflies-72da2402 passed in 42.16
seconds with 73 guards and 27 type/axiom pairs. Imported request
1789314879940888683-schoenflies-765d6356 passed in 87.65 seconds with 74 guards;
all 27 types are byte-identical to source. The embedding leaf freshly compiled
without diagnostics in 47.97 seconds, maximum RSS 1771024 KiB. ConvexOpen had
already freshly compiled at these exact bytes in request e0ca0e78; that earlier
combined source probe failed only because it both imported and redeclared the
same helper. The final source gate elaborates both final leaf bodies directly.
Stock declaration linters and approved-only transitive axioms pass. Consumers
include an actual nonzero truncated translated sphere, arbitrary sphere families,
singletons, rank zero, empty sources with arbitrary normed model, and the original
Banach-valued map-extension consumers. These are fresh leaf/source and consumer
checks, not a full DG aggregate build. Boundary/corners and the actual
Schoenflies isotopy-family producer remain open.

## Ambient isotopy from interval-only input, 2026-09-13

Manifold.exists_contDiff_compact_ambient_isotopy_Icc now accepts joint smoothness
and native embedding slices only on Icc a b. The compact source is boundaryless;
the ambient space is a finite-dimensional real normed space. It constructs
native ambient diffeomorphisms with joint C∞ forward and inverse maps, identity
at a, BOTH exact tracking equations on the closed interval, and ONE compact
spatial support inside the prescribed open neighborhood of the trace. Both
directions fix its complement for all real times. Arbitrary endpoints are
allowed: a reversed interval uses the identity family and empty support.

This is a thin application of the published interval embedding-family extension
and the existing compact velocity/flow engine. All earlier AmbientIsotopy proof
bodies and public signatures are retained. No supplied extension, velocity or
flow is assumed; no ordinary derivative identity for raw interval data at an
endpoint is asserted. The genuinely whole-real extension is what the existing
ODE proof differentiates. Source-boundary/corners, general ambient manifolds and
the actual Schoenflies family producer remain open.

Private request efe400b6 passed in 51.82 seconds with 169 guards and 38 pairs.
Public source1789315199912929650-schoenflies-50b2497e passed in 68.96 seconds,
175 guards and47pairs. Final imported1789315305984021990-schoenflies-096d3a15
passed in136.03seconds,175guards46pairs, all46typesbyte-identical to source.
The changed leaf freshly compiled without diagnostics in1:18.32, maximum
RSS1822700KiB. Stock declaration linters and approved-only axioms pass. New
consumers include arbitrary interval S² families, an actual nonzero translated
sphere truncated to zero outside [0,1], and arbitrary empty-interval input with
empty support forcing identity at every time. All old map/family/velocity,
whole-real ambient and relative fixed-neighborhood consumers replay unchanged.
Root reviewed full source, exact types, actual provider bodies, all guards and
the complete diff. This is a fresh leaf and consumer check, not a full DG build.

## Global extension from a closed halfspace, 2026-09-13

Analysis/Calculus/SmoothExtension/HalfSpace proves
ContDiffOn.exists_contDiff_extension_Ici_prod. A map smooth only within
Ici a times the entire tangential vector space has one globally smooth
extension agreeing on that full closed halfspace. The tangential real normed
space is finite-dimensional; values may be any real Banach space. The normal
threshold is arbitrary and rank-zero tangential spaces are included.

The 41-line proof globalizes the actual existing one-face parametric Borel
extension using Mathlib's smooth convex selection and its partition-of-unity
construction. Root read the full underlying Borel construction previously and
reread its complete one-face seam proof and the actual selection body for this
checkpoint. No dependency download, new Borel series or upstream code copy is
needed. An arbitrary-index family consumer shows that all chosen extensions
have the same entire ambient domain, without exchanging two neighborhood
quantifiers. No regular dependence on that index or extension-operator bound
is claimed. Further probes check nonzero normal motion of a piecewise input
and PUnit as the actual tangential model.

Private f0784e05 passed in4.01seconds with38guards8pairs after explicit interval
membership conversions. Public3873ab63 passed33.74seconds38/8. Final imported
1789315827485508273-schoenflies-5f3b7c4d passed105.90seconds39/8, all8types
byte-identical to source. The new leaf freshly compiled without diagnostics
in1:11.77, maximumRSS1770384KiB. Stock declaration linters and approved-only
transitive axioms pass. Root reviewed exact source, consumers, signatures,
guards, provenance and staged diff. The leaf is registered in the root; this
is not a full DG aggregate build. An extension at a genuine corner still
requires mixed-jet matching and within-set seam gluing. This halfspace result
does not itself remove the native manifold source-boundary restriction.

## Mixed jets and seam gluing at tangential boundaries, 2026-09-13

The existing IteratedFDerivProdMatch and JetGlueParam proofs now handle
parameter sets with unique within derivatives. Turning equality of all normal
jets into equality of all full mixed jets additionally requires the set to lie
in the closure of its interior. Gluing already matching full Taylor jets does
not require that extra density assumption. The actual conditional splice is
smooth within the entire product, including its tangential boundary. The five
old open-set signatures remain verbatim as thin corollaries. No finite
dimension, completeness, compactness or nonempty assumption is introduced.

The proofs are generalized in place. Off the seam, within-neighborhood
transport replaces the use of an ambient derivative. At the seam, the existing
Taylor-series union proof and normal/tangential derivative induction are reused.
No new series construction or imported third-party source is needed. Nonzero
quadrant inputs, their actual splice and derivative, arbitrary tangential
halfspaces, rank-zero parameters and every old interface have consumer checks.

Final MixedJet source 798ca8bc passes in 88.23 seconds with 39 guards and 15
signature/axiom pairs, including unchanged full Borel and jet-gluing sources.
Final JetGlue source 7563da60 passes in 44.84 seconds with 39 guards and 17 pairs.
Imported request 1789317404826458436-schoenflies-65e83222 passes in 298.23 seconds
with 181 guards and 72 pairs. Seven affected modules freshly compile without
diagnostics in 3:55.50, maximum RSS 2018424 KiB. All 46 prior interval/ambient
readbacks and every shared boundary/halfspace readback are byte-identical.
Stock source/declaration linters and standard-only transitive axioms pass.
Root reviewed full sources, consumers, decisive provider proofs and the diff.
Both leaves were already registered in the root. This is not a full DG build.

Actual quadrant extension still needs a Borel realization of the extended
normal jets and two-face assembly. Boundary-source ambient isotopy and the
Schoenflies headline remain open.

## Global smooth extension from a closed quadrant, 2026-09-13

Analysis/Calculus/SmoothExtension/Quadrant proves
ContDiffOn.exists_contDiff_extension_quadrant. A map smooth only within
Ici a × (Ici b × univ) has one globally jointly smooth extension agreeing
on that entire closed quadrant. Both thresholds are arbitrary. The free
real normed coordinates are finite-dimensional; values may be any real
Banach space. Rank-zero free coordinates are included. Local and zero-threshold
construction steps remain private.

Two natural visibility bridges in the existing BorelHalfLineParam expose
joint smoothness of actual within-normal jets on an arbitrary tangential set,
and a single global realization of arbitrary smooth compactly supported jet
coefficients. The latter does not assume a common compact support or finite
dimension of the parameter space. All original 1345 source lines and their
lexical scopes are retained; the old public signatures remain exact.

The proof extends each normal jet through the existing HalfSpace theorem,
multiplies every coefficient and the raw input by the same compact cutoff,
realizes the coefficients using the original Borel series, and applies the
accepted within-set jet gluing. Swapping the two real coordinates permits
HalfSpace to extend the other face. Mathlib's existing convex smooth selection
then globalizes the local extensions; translation handles both thresholds.
No new Borel construction, dependency download or upstream source copy is
introduced. Only the already globally smooth realization uses ordinary normal
derivatives. The raw input is controlled through within derivatives throughout.

Private combined source 0d906aca passes in 86.41 seconds with 51 guards and 20
signature/axiom pairs. Final public source 05b80c03 passes in 72.17 seconds with
45 guards and 20 pairs. Imported request
1789319285915894643-schoenflies-f52f9acd passes in 275.45 seconds with 184 guards
and 84 pairs. All 72 earlier boundary/interval/ambient pairs are byte-identical;
all 17 shared source/import pairs match up to scoped notation. BorelHalfLineParam,
HalfSpace, Quadrant, both interval-extension leaves and AmbientIsotopy freshly
compile without diagnostics in 3:32.51, maximum RSS 2021916 KiB. Stock source
and declaration linters and approved-only transitive axioms pass. Consumers
include arbitrary and singleton tangential sets, nonzero all-order rank-zero
jets, nonzero quadrant data with uncontrolled outside values, mixed free-coordinate
data, and negative thresholds with a nonzero corner value. Root reviewed the
full changed sources, exact statements, provider proofs, consumers and diff.
The new leaf is registered in the flat root; this is not a full DG build.
Native source-boundary isotopy, arbitrary corner depth and Schoenflies remain open.

## Smooth extension along native boundary embeddings, 2026-09-13

Embedding/Extension now proves local and global extension along native
IsSmoothEmbedding maps with standard EuclideanHalfSpace (d+1) source model.
The local primary uses the actual IsImmersionAtOfComplement at one point and
IsInducing, and agrees with the supplied data at every embedded point in its
produced ambient open set. Ambient spaces may be arbitrary real normed spaces;
the extended values are Banach. Global closed-image and compact-support
corollaries require finite ambient dimension for Mathlib's smooth convex
selection. The support-sensitive compact theorem needs only the image of
K intersect tsupport g in the prescribed open set, while extending on all K.
There is no whole-source compactness, extra Hausdorffness or nonemptiness premise.

The written-in-charts calculation adapts the existing SliceChart proof from
TauCeti/Geometry/Manifold/LocallyFlat/Smooth.lean at revision
3358033ba2fd35f321356dceaf2372a0fd6c0bfd. Its original Apache header is retained.
Native domain chart, codomain chart and complement equivalence all come from
the same immersion witness. Existing HalfSpace/Borel extension controls the
actual within-range germ; no smooth boundary retraction is assumed. IsInducing
turns source-local equality into equality on all embedded points of an ambient
neighborhood. No foreign boundary model or dependency is installed.

One private convex-selection engine and one support-cutoff engine now serve
both boundary and boundaryless interfaces. All four earlier embedding-extension
signatures remain exact, including finite regularity and arbitrary normed values.
Calculus/Cutoff supplies the natural within-set cutoff product at any order;
the old whole-space theorem is a thin corollary. CompactCutoff localizes a
within-set smooth function with an ambient equality germ and compact support,
at any finite order or C-infinity, without complete values.

Final source request 1789321985369070517-schoenflies-a81424a9 passes in 38.89
seconds with 46 guards and 30 signature/axiom pairs. All nine earlier source
pairs match baseline 67e158ba exactly. Imported request
1789322127727898034-schoenflies-f3d17a60 passes in 292.20 seconds with 190 guards
and 108 pairs. All 84 previous imported pairs and all 25 shared source/import
pairs are byte-identical. Eight changed or affected leaves freshly compile
without diagnostics in 3:43.91, maximum RSS 1830328 KiB. Stock source and
declaration linters and approved-only transitive axioms pass. Consumers include
nonconstant data on the whole noncompact halfline, compact extension with
boundary value one, zero data with empty allowed support, order-zero arbitrary
normed values, and a localized quadrant function uncontrolled off its domain.
Root reviewed the full proof bodies, exact types, consumers and mathematical diff.
These existing leaves remain registered in the flat root; this is not a full
DG aggregate build. Moving boundary graphs, boundary-source isotopy, arbitrary
corner depth and the Schoenflies headline remain open.
