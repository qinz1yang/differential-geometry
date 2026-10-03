# Mostow–Prasad rigidity

## Goal contract

The primary goal is finite-volume Mostow–Prasad rigidity in dimension three.
For connected complete hyperbolic three-manifolds with the same negative
sectional-curvature normalization, every given homotopy equivalence must be
homotopic to a unique isometry. Noncompact cusped manifolds and nonorientable
manifolds remain in scope. The actual homotopy class and its induced marking
must be retained throughout the construction.

The eight-hour window starts at 2026-10-03 04:01:23 UTC and ends at
2026-10-03 12:01:23 UTC. If the three-dimensional theorem and all delivery
gates close within that window, continue to the finite-volume theorem in every
dimension at least three. Infrastructure alone does not complete the goal.

At the end of the eight-hour window the three-dimensional headline was still
open. The conditional transition to the general-dimensional Mostow theorem
was not triggered; the active goal remains the three-dimensional theorem.

The initial verified baseline is upstream commit
`777299070a5529e96345e0033979706fd00c7e62`, Lean `v4.35.0-rc3`, and Mathlib
`c55e6e786f49`. Both the default build and `lake build DifferentialGeometry`
passed with 26,860 jobs and no diagnostics before development began.

## Mandatory performance gate

Every newly added Lean module must elaborate from its final source in at most
30 seconds with its dependencies already built. Record fresh compiler wall
time; a cached no-op build is not performance evidence. An over-budget module
cannot be delivered even if its mathematical audit passes.

Avoid broad namespace openings and unconstrained elaborator searches. Make
load-bearing intermediate types, instances, and reusable lemmas explicit.
Refactor only across genuine mathematical interfaces. Do not add resource
budget overrides, linter suppressions, or arbitrary line-count splits.

## Integration rules

Root alone changes tracked source, public APIs, the root aggregate, Git, and
the mutable Lake cache. Root alone performs Lake builds, canonical replay,
commits, and pushes. Workers use immutable dependency snapshots and private
scratch source and output directories. Workers communicate in English and do
not spawn other workers.

Each bounded proof target has one owner and an explicit next declaration.
Reasoning and compiler concurrency are limited separately; at most three
compiler processes run concurrently, with at most one per worker. Existing
builds must be polled before another build of the same target is launched.
Root aggregate builds use an explicit `LEAN_NUM_THREADS` process budget and
monitor actual Lean child processes. With a two-process Root build, only one
worker may compile; a three-process Root build pauses all worker compilation.
The compiler flag `--threads=2` alone does not constrain
Lake's number of concurrent compiler processes.
Searches are scoped to candidate source directories, file types, and names.

One fresh independent reviewer audits each coherent packet. Accepted evidence
is frozen with source hashes. Unchanged signatures, proofs, and dependencies
are not re-audited; subsequent changes receive delta review. Packet states
are `PROVED`, `INTEGRATION-ONLY`, `PROVISIONAL`, or `BLOCKED`. A blocked packet
must identify its exact repair declaration immediately.

The integration queue holds at most two batches. Root builds changed modules
and affected dependents, then runs one aggregate build per dependency-closed
layer. All default declaration linters except `docBlame` and `docBlameThm`
must pass. Native Lean axiom checks must admit only `propext`,
`Classical.choice`, and `Quot.sound`. New proof debt is forbidden.

## Proof route

The three-dimensional reference route is the finite-volume boundary argument
in the supplied `master207A.tex` and `master207B.tex`: controlled marked
quasi-isometries, canonical boundary extension, disk control and directional
regularity, compact-core return times, and the returning-zoom argument.
Their written arguments do not constitute elaborated Lean proofs.

The shared dependency order is:

1. Hyperbolic model, metric, geodesics, isometries, and boundary action.
2. Covering and quotient identifications, with exact equivariant descent.
3. Finite-volume cusp structure and controlled representatives of the actual
   homotopy equivalence.
4. Boundary extension, regularity, and identified returning-orbit limits.
5. Boundary rigidity and triviality of the finite-volume centralizer.
6. Descent to the original manifolds, the original homotopy class, and uniqueness.

The current headline remains open. Root owns canonical integration and the
final headline. The active frontier is:

| Owner | Exact next target |
| --- | --- |
| Root | Integrate dependency-closed layers and close the actual three-dimensional finite-volume headline. |
| `review_hyperboloid_metric` | Prove smooth tensor preservation for the explicit native hyperbolic comparison map into a complete curvature-minus-one manifold. |
| `review_hyperboloid_model` | Construct actual open sheets from radial C1 lifts and native joint lifting continuity. |
| `review_orbit_quotients` | Prove boundary-map composition and invariance under bounded distance, retaining original maps. |
| `review_hyperboloid_interpolation` | Design the finite interval-refinement estimate leading from image-strip control to horizontal absolute continuity. |

The interior returning-orbit extraction is proved with the actual composite
`a ∘ F ∘ b` and one shared subsequence. Boundary convergence, finite-volume
cusp geometry, and the rigidity argument remain open.

## Verified foundation layer

The model coordinate homeomorphism, Lorentz orthogonal-complement inequalities,
and equivariant quotient maps, homeomorphisms, and homotopies have passed
independent review and canonical source builds. The unnecessary action-continuity
assumption in homotopy descent was removed using local compactness of the
parameter interval. Lorentz coercivity exposes its scale-invariant primary
inequality and a normalized corollary.

Fresh module builds took 5.0, 2.7, 2.0, and 1.9 seconds respectively. All 14
applicable declaration linters and native axiom checks passed. The aggregate
build passed with 26,864 jobs and no diagnostics; the existing aggregate module
itself took 37 seconds. Exact source hashes and verification metadata are in
`mostow-foundations.json`.

## Verified hyperboloid layer

The arcosh distance is now a genuine metric with its separation and triangle
inequality proved. Its topology definitionally agrees with the original
ambient-induced topology. The coordinate diffeomorphism gives the analytic
manifold structure, and the actual ambient inclusion is smooth at every order.
Proper model spaces give proper hyperboloids and hence complete metric spaces.
Normalized ambient Lorentz interpolation is jointly continuous and has the
exact specified endpoints.

These four modules have passed independent review, canonical compilation,
all 14 applicable declaration linters, native axiom closure checks, and the
26,868-job aggregate build without diagnostics. Fresh module compilation took
5.9, 2.1, 1.3, and 1.3 seconds. Exact hashes and evidence are in
`mostow-hyperboloid.json`. Curvature and compatibility with the native
Riemannian metric remain separate proof obligations.

## Verified native geometry and orbit compactness

The canonical native smooth metric now has its actual Levi-Civita connection
and full native Rm04 tensor computed. Native sectional curvature is -1 on every
linearly independent tangent plane, with concrete non-origin dimension-three
validation. Complete metric geodesic lines, lines through distinct endpoints,
Lorentz restrictions, explicit boosts, and Klein coordinates are proved.
Shared chart and coordinate-field APIs support the native consumers without
copying private proofs.

For general proper metric spaces, surjective isometries whose basepoint images
lie in a compact set form a compact family in the existing continuous-map
topology. Equivariant returning sequences have one subsequence whose recentered
left/right isometries converge to actual A and B, and whose original composites
converge to exactly A composed with the original F composed with B.

All changed modules pass independent review, canonical builds, 14 applicable
linters, native axiom checks, and the 26,878-job aggregate build. The new modules
freshly compile in at most 5.8 seconds. Exact hashes and timings are recorded in
`mostow-native-geometry.json`. The existing aggregate module took 35 seconds.
Native distance compatibility and Mostow rigidity are still open.

## Verified symmetry and discrete-group layer

Every hyperboloid isometry now has a unique ambient Lorentz extension, with
exact recovery, inverse, and composition laws. Hyperbolic geodesic lines are
smooth and have speed one in the native Riemannian metric. The time coordinate
has its intrinsic manifold derivative computed.

For every seminormed ring, a uniform identity neighborhood in its unit group
satisfies Zassenhaus: the small elements of each discrete subgroup generate a
nilpotent subgroup. The proof uses a coefficient-eight commutator estimate and
a general generator criterion for nilpotence, with no finite-generation or
symmetric-generator hypothesis.

All six changed modules pass independent review, canonical compilation, all 14
applicable linters, and native axiom checks. Fresh compilation takes at most
6.5 seconds; the affected native geometry modules also rebuilt successfully.
The aggregate build passed with 26,883 jobs, zero diagnostics, and a 26-second
root module. Exact hashes and evidence are in `mostow-symmetries.json`.
The Mostow headline and native distance compatibility remain open.

## Verified distance and boundary layer

The native Riemannian extended distance is now proved equal to the original
arcosh metric for arbitrary real inner-product model spaces. The lower bound
uses regularized distance potentials; the upper bound uses the actual
constructor-tied geodesic and its native unit speed. Independent consumers
verify the explicit arcosh expression and a distance of three between two
distinct non-origin points.

Every hyperboloid isometry has a canonical homeomorphism of the unit sphere,
with exact Lorentz normalization, positive denominator, and inverse/composition
laws. A general Lorentz isometry has its canonical continuous linear upgrade.
The four-point inequality holds with additive constant log 32. Explicit
projection to an origin-axis geodesic is the unique nearest point and satisfies
the hyperbolic Pythagorean identity and quantitative contraction bound.

For arbitrary subgroups and native group generators, an infinity-aware bound
on a quotient word ball implies the same ENat bound on the entire coset space.
The result does not require normality or finite generation; infinite-index
and actual nonnormal-subgroup consumers were checked.

All seven changed modules passed independent review, canonical builds, all 14
applicable linters, and native axiom checks. The six new files freshly compile
in 0.989 to 5.2 seconds. The root build passed with 26,889 jobs and zero
diagnostics; the existing aggregate took 30 seconds. Hashes and timings are in
`mostow-boundary-distance.json`. The Mostow headline remains open.

## Verified isometry-group and equivariant-homotopy layer

The native isometry group now has its standard pointwise topology, continuous
joint evaluation and group operations, and an embedding into the compact-open
continuous-map space. This holds for pseudo-extended metric spaces, including
infinite distances and non-separated examples. Proper metric spaces have
compact native families of isometries with bounded basepoint displacement.

Compact displacement gives a uniform finite-index bound for small movers
modulo the subgroup generated inside a supplied identity neighborhood. The
boundary action is faithful in spatial rank at least two; an explicit
one-dimensional boost verifies why that rank condition cannot be dropped.
Actual forward and backward Klein limits of every geodesic line are proved.

Interpolation commutes with all hyperbolic isometries. Its actual homotopy is
equivariant with minimal action hypotheses, and the same homotopy descends to
the original orbit-quotient maps, retaining their original correspondence.

All six changed modules passed independent review, canonical builds, all 14
applicable linters, and native axiom checks. The five new files freshly compile
in at most 4.2 seconds. The aggregate build passed with 26,894 jobs and zero
diagnostics; the existing aggregate took 32 seconds. Exact hashes, declarations,
imports and timings are in `mostow-group-boundary.json`.
The finite-volume Mostow headline remains open.

## Verified Margulis and closed-ball extension layer

The actual hyperbolic Margulis theorem is proved in every finite-dimensional
model, with the same epsilon and index bound chosen before both the discrete
subgroup and the basepoint. Its proof uses a faithful continuous linear
representation, the general linear-action Margulis theorem, and actual boost
conjugation. The output is an actual nilpotent subgroup of the small-mover
subgroup with an infinity-aware index bound. Explicit non-origin dimension-three
and dimension-zero/one consumers pass. No orientation or torsion-free condition
was added.

Every isometry now extends to a homeomorphism of the closed Klein ball,
with exact interior and sphere restriction laws. These laws yield convergence
to the actual boundary image, rather than an unidentified limiting map.
Projection to a geodesic has a proved exponential decay estimate and a checked
finite-step specialization for the upcoming Morse argument. This estimate
alone does not certify Morse stability.

All six changed modules passed independent review, canonical builds, all 14
applicable linters, and native axiom checks. The four new files freshly compile
in at most 1.7 seconds; all changed files compile in at most 5.9 seconds.
The root build passed with 26,898 jobs and zero diagnostics. The existing
aggregate took 35 seconds and is recorded separately from the new-file gate.
Exact hashes, declarations, dependencies and timings are in `mostow-margulis.json`.
The Mostow headline, finite-volume cusp structure and boundary rigidity remain open.

## Verified Morse, convergence and covering layer

The complete quantitative Morse theorem is proved for continuous hyperbolic
quasi-geodesic segments. It bounds native Hausdorff extended distance to the
actual endpoint-defined metric segment, with both directions, repeated endpoints
and singleton intervals covered. Its proof uses finite equal-time chains rather
than a curve-length assumption. The metric segment itself is identified with
the actual geodesic-line interval.

Bounded hyperbolic distance preserves the same ideal Klein endpoint for
arbitrary filters. The Lorentz extension and the closed-ball/sphere actions are
jointly continuous, including the native compact-open map families.

Discrete isometry subgroups of proper metric spaces act properly discontinuously.
Under ordinary torsion-freeness the actual orbit quotient is a native covering
map. The argument uses finite stabilizers and does not substitute the stronger
nonabelian unique-root condition. Empty spaces and compact-set degeneracies are
covered.

All eight changed modules passed independent review, canonical builds, all 14
applicable linters, and native axiom checks. All changed files freshly compile
in at most 5.1 seconds. The root build passed with 26,904 jobs and zero diagnostics;
the existing aggregate took 37 seconds and remains separate from the new-file gate.
Hashes, declarations, imports and timings are in `mostow-morse-covering.json`.

The exact native three-dimensional target interface is recorded in
`mostow-statement.md`; its type and supporting metric/volume/curvature vocabulary
were checked, but its proof remains open. The original universal-cover metric,
completeness, curvature transport and based deck-action chain have approved native
axioms. A global negative-curvature space-form realization is still missing;
the inspected positive-curvature local Cartan and flat global exponential
results do not supply it. Finite-volume cusp geometry and boundary rigidity
also remain open.

## Verified ray and finite-action layer

A continuous quasi-geodesic ray in a finite-dimensional hyperboloid now has
an actual geodesic ray based at its original starting point, uniformly close
at the exact radial parameter. One direction subsequence is selected before
the time variable. The unique ideal endpoint theorem consumes that construction
and preserves the original curve. Perturbed rays, non-origin basepoints,
arbitrary behavior at negative times and the dimension-zero case were checked.

Every finite group acting isometrically on the hyperboloid has a common fixed
point. The construction normalizes its actual future-pointing orbit sum and
uses noncommutative left reindexing. For a free action this proves ordinary
torsion-freeness, without a stronger unique-root assumption. A conjugated
reflection consumer produces a fixed point distinct from the origin.

Both modules passed independent review, canonical builds, all 14 applicable
linters, and native axiom checks. Fresh builds took 6.9 and 6.2 seconds. The root
build passed with 26,906 jobs and zero diagnostics; the existing aggregate took
36 seconds. Exact evidence is in `mostow-rays-fixed-points.json`.

The native metric-bundle norm has also been checked at a genuine non-origin
hyperbolic point: a radial tangent has metric square norm one half, while its
Euclidean coordinate square norm is one. The compatible native construction
preserves the fiber topology and original charts. This permits honest local
Cartan comparison work; it does not supply the missing global space-form theorem.
The finite-volume Mostow headline remains open.

## Verified Cartan and original-map boundary extension layer

Cartan comparison now applies to a shared arbitrary real constant curvature.
The original positive-curvature signatures and Cartan map constructions are
unchanged. Genuine three-dimensional Euclidean and non-origin hyperbolic
consumers verify curvature zero and minus one with the native metric norm.

Every model isometry has its analytic diffeomorphism with the same map and
inverse. The explicit hyperbolic lines satisfy the actual native Levi-Civita
geodesic equation. Two forward rays with the same actual ideal endpoint have
equal-time distance bounded by their initial distance, including distinct
horospheres.

The original continuous quasi-isometric embedding now has a canonical continuous
boundary map. Its exact ray producer and arbitrary-filter extension law are
proved. Continuity comes from uniform visual estimates; it is not supplied as
a hypothesis. Only the target model requires finite dimensionality.

All eight changed modules passed independent review, canonical builds, all 14
applicable linters and native axiom checks. Fresh source builds take at most
6.8 seconds. The required broad dependent and root build passed with 26,909 jobs
and zero diagnostics. Explicit scheduling capped Root at three actual compiler
processes; the final aggregate module took 7.3 seconds. Exact source hashes,
regressions and timing evidence are in `mostow-cartan-boundary.json`.
The full finite-volume Mostow theorem remains open.

## Verified native exponential, continuation and analytic packing layer

The actual native hyperbolic exponential is identified for every initial vector,
including zero, and its global origin homeomorphism has the exact arsinh inverse.
The metric-bundle instances are explicit, with declaration-local norm selection
and outside-import instance preservation checked.

A partial lift through a local Riemannian isometry extends to its finite right
endpoint when the source metric is complete. Its proof controls actual source
distance by target path length and uses only within-interval derivatives. A
consumer with deliberately discontinuous outside data verifies the one-sided
conclusion and distinguishes the limit from the supplied endpoint value.

Actual continuous coarse inverse maps induce a native boundary homeomorphism,
with the original forward and inverse maps retained. A noninjective interior
flattening map verifies that no interior equivalence was assumed.

Finite disjoint disks give a squared endpoint-oscillation bound by the area of
the actual homeomorphic image. Image-area finiteness is proved before conversion
to real values. The final statement has no redundant sign restriction on its
radius-ratio parameter. This is a packing theorem, not yet absolute continuity
or boundary rigidity.

All four new modules passed independent review, canonical builds, all 14
applicable linters and native axiom checks. Fresh builds took 11.0, 2.4, 1.6 and
1.8 seconds. The final root build passed with 26,913 jobs and zero diagnostics;
the existing aggregate took 36 seconds. Exact evidence is in
`mostow-exponential-lifting-packing.json`. All 53 newly added Lean files have
matching current-source hashes and recorded fresh builds below 30 seconds.
The global negative space-form, finite-volume cusp/control and boundary-rigidity
frontiers remain open; the Mostow headline is not complete.

## Verified global lifting, smooth inverse and strip-control layer

The native origin exponential homeomorphism is now a smooth diffeomorphism with
the same forward map and explicit inverse. The inverse smoothness proof uses
the actual signed-curvature bound, native differential nonsingularity and the
local inverse theorem.

Complete local Riemannian isometries have global C1 lifts of prescribed C1 paths
on a closed interval through the prescribed initial point. The proof constructs
compatible initial lifts, uses a genuine supremum and the earlier continuation
engine, and retains interval uniqueness. It does not assume a maximal lift or
a covering map.

The original quasi-isometric embedding's boundary map is equivariant for the
given marking. Cross-model boundary faithfulness recovers an actual isometry
from its boundary action and recovers interior equivariance from its boundary
commutative square. This does not assert the missing existence of a realizing
isometry.

For every plane homeomorphism, almost every horizontal height has a finite
constant controlling the area of its actual image strips at every eligible
radius. The native finite marginal measure may have atoms or a singular part;
no absolute-continuity or null-image preservation assumption was introduced.

All five changed modules passed independent review, canonical builds, all 14
applicable linters and native axiom checks. Fresh source builds take at most
11 seconds. The root build passed with 26,915 jobs and zero diagnostics; the
existing aggregate took 36 seconds. Exact evidence is recorded in
`mostow-global-lifting-strip.json`. The global space-form, finite-volume cusp
and boundary-rigidity steps remain open.
