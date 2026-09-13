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
