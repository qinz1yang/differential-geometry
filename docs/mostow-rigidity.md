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
| `review_hyperboloid_metric` | Prove genuine uniform disk distortion for the plane homeomorphism induced by the original controlled boundary equivalence. |
| `hyperboloid_metric` | Prove compactness of the actual projected positive-displacement set from original finite volume. |
| `rigidity_assessment` | Prove that an actual isometry swapping distinct ideal points has an interior fixed point, then exclude swapping in a free action. |

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

## Verified comparison maps and actual sheets

The canonical hyperbolic comparison map is the actual target exponential
composed with the prescribed metric-tangent isometry and the actual model
exponential inverse. It is smooth without a curvature assumption and preserves
the metric tensor under the true curvature-minus-one identity. The target
completeness is its native metric completeness; no unrelated ambient metric or
target exponential injectivity is supplied.

Over an actual star-convex chart, the prescribed initial point now determines
an actual continuous open sheet. Individual C1 lifts and the native joint-lift
continuity theorem supply the parameter dependence, and the center law retains
the prescribed point. Disjointness and exhaustion for the covering assembly
remain the next separate proof obligations.

Boundary maps respect actual composition with internally derived distortion
constants, and maps at bounded distance have the same boundary map. Tests use
a continuous noninjective flattening map, including its actual composite.

All three modules passed independent review, canonical builds, all 14 applicable
linters and native axiom checks. Fresh source builds took 6.0, 4.5 and 3.0
seconds. The root build passed with 26,917 jobs and zero diagnostics; the existing
aggregate took 35 seconds. Exact evidence is in `mostow-comparison-sheets.json`.
The original three-dimensional finite-volume Mostow headline remains open.

## Verified complete coverings and horizontal absolute continuity

The complete local-Riemannian-isometry theorem now produces a native covering
map. It constructs sheets over the same actual chart, proves exhaustion using
reversed lifted radial paths, proves disjointness by lift uniqueness, and
handles empty fibers explicitly. No target completeness, global injectivity
or surjectivity is assumed. The actual hyperbolic comparison is a local
diffeomorphism and its source has native metric completeness.

Uniform round-disk control of the original plane homeomorphism now implies
complex-valued horizontal absolute continuity at almost every height. The
finite-refinement proof bounds the square of the sum of actual endpoint
oscillations, including reversed and zero-length intervals. Its nonlinear
sine-shear consumer proves the actual disk-control hypothesis.

A fixed-radius positive ball-measure lower bound in a finite-measure metric
space now implies boundedness of the supplied center set. Proper-space compact
closure remains a native consequence, not a hidden premise. The actual
hyperbolic quotient local-volume identification remains a separate geometric
obligation.

All five changed modules passed independent review, canonical builds, all 14
applicable linters and native axiom checks. Fresh source builds take at most
9 seconds. The final root build passed with 26,920 jobs and zero diagnostics;
the existing aggregate took 34 seconds. Exact evidence is in
`mostow-covering-ac-packing.json`. The finite-volume Mostow headline remains open.

## Verified normalized space form and directional regularity

A complete simply connected manifold with actual curvature minus one now has
an isometry equivalence with the hyperboloid. Its forward function is exactly
the constructed comparison map, and it sends the model origin to the prescribed
point. The proof uses the genuine covering theorem, simple connectedness, and
native global Riemannian-distance transport. Source and target metrics remain
explicitly distinguished even in the concrete hyperboloid consumer.

Every nonempty open rectangle has a positive-area subset where the original
uniformly disk-controlled plane homeomorphism has a nonzero horizontal
directional derivative. Native measurability, Fubini, vector-valued absolute
continuity and zero-derivative constancy provide the proof. This is horizontal
regularity; the countable rational-direction extension remains a separate target.

Sets with a uniform lower displacement bound are closed after passage to the
actual orbit quotient, including infinite radii and trivial groups. No
exponential injectivity-radius identification is inferred from that result.

All three new modules passed independent review, canonical builds, all 14
applicable linters and native axiom checks. Fresh source builds took 5.5, 6.0
and 1.0 seconds. The root build passed with 26,923 jobs and zero diagnostics;
the existing aggregate took 36 seconds. Exact evidence is in
`mostow-space-form-regularity.json`. All 63 newly added Lean files have current
source-hash-matched fresh compilation evidence below 30 seconds.

The original three-dimensional finite-volume Mostow headline remains open.
Applying the normalized classification to its based universal cover, proving
finite-volume cusp/control producers, and closing boundary rigidity are still
required.

## Verified original-cover and rational-direction layer

The original negatively curved three-manifold's actual based universal cover
now has an isometry equivalence with the hyperboloid. Its metric is exactly
the lift of the original metric scaled by minus its curvature. Exact laws
retain the comparison map, the lifted basepoint and the original projected
basepoint. Genuine curvature-minus-one and curvature-minus-four models at a
non-origin point were checked.

The original disk-controlled plane homeomorphism is differentiable almost
everywhere in each separately fixed direction. Intersecting only countably
many rational directions gives a measurable positive-area good set in every
strict rectangle, retaining a nonzero horizontal derivative. No full derivative
or uncountable interchange of quantifiers is asserted.

A lower displacement bound also proves injectivity of the actual orbit
projection on the corresponding open ball, without freeness or metric
separation assumptions. This does not yet identify quotient ball volumes.

All three changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds took
7.2, 6.7 and 1.0 seconds. The root build passed with 26,924 jobs and zero
diagnostics; the existing aggregate took 36.0 seconds. Exact evidence is
in `mostow-universal-cover-rational.json`. All 64 newly added Lean files have
current source-hash-matched fresh compilation evidence below 30 seconds.

The original three-dimensional finite-volume Mostow headline remains open.
Marked deck and quotient-volume producers, finite-volume cusp/control
geometry, and boundary rigidity remain required.

## Verified marked deck, boundary metric and local-volume layer

The original based fundamental group now has its actual normalized hyperbolic
isometry representation. It is exactly conjugation of the original deck action
by the constructed cover isometry. The native inverse-loop convention,
faithfulness, equivariance and original projection laws are retained. The
actual image subgroup is proved discrete in the inherited isometry topology
and ordinarily torsion-free. No lattice, freeness or discrete topology is
supplied as a premise. A generic covering-preserving subgroup theorem supplies
the reusable discreteness argument, including empty sources.

The fixed north-pole stereographic chart now uses an explicit real isometry
from its orthogonal plane to the complex numbers. Its native factor-two
forward formula and exact inverse are proved. For original hyperbolic
isometries, boundary chord-square distortion has the actual Lorentz time
factors, and the boundary action is Lipschitz with constant the exponential
of origin displacement. A nonorigin boost verifies genuine contraction.

Native Riemannian volume now transports through an injective open domain of a
local isometry. The original map may fail to be smooth or injective outside
that domain. Positive- and negative-domain absolute-value consumers check the
actual image equality, including orientation reversal.

All seven changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds take at
most 5.7 seconds. Required deck-action dependents and the 26,930-job root
build passed without diagnostics; the existing aggregate took 30 seconds.
Exact evidence is in `mostow-marked-deck-boundary.json`. All 70 newly added
Lean files have current source-hash-matched fresh compilation evidence below
30 seconds. The actual quotient homeomorphism, original covering ball-volume
identification, uniform boundary-map disk control, finite-volume cusp geometry
and the final Mostow rigidity argument remain open.

## Verified actual quotient, covering balls and stereographic distances

The actual normalized deck-image orbit quotient is now homeomorphic to the
original manifold. Its representative equation is exactly the original cover
projection after the constructed hyperbolic isometry, retaining the chosen
basepoint. Fiber transitivity and surjectivity are proved from native based
paths and deck actions. This is a topological identification; no metric or
volume identification is inferred from a homeomorphism alone.

A native Riemannian covering maps every open source ball exactly onto the
corresponding target ball. Completeness and global injectivity are unnecessary;
the actual real-to-circle covering verifies this distinction. All real radii
are included. General stereographic chord-square formulas now precede their
complex-coordinate corollaries, with the exact native factor-two normalization
and no finite-dimensionality or completeness assumption.

All four changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds took
9.2, 6.5, 1.6 and 6.6 seconds. The 26,933-job root build passed without
diagnostics; the existing aggregate took 35 seconds. Exact evidence is in
`mostow-quotient-stereographic.json`. All 73 newly added Lean files have
current source-hash-matched fresh compilation evidence below 30 seconds.
The three-dimensional finite-volume Mostow headline remains open.

## Verified uniform boundary estimate and covering small-ball volume

The original continuous quasi-isometric embedding now has a uniform boundary
half-chord Hölder estimate with exponent one over twice its coarse multiplicative
constant. Its bound is chosen before the original map and endpoints, from the
fixed coarse constants and actual origin displacement bound. Normalization uses
the actual boost and boundary-map composition. Nonisometric sine perturbations
and their nonorigin boosted versions verify that the original map is retained.
A single existing quantitative ray-error declaration was made public without
changing its statement or proof; that visibility change is integration only.

An actual Riemannian covering injective on its source open ball now preserves
the native volume of that ball and its corresponding target ball. All real
radii are permitted; neither global injectivity nor completeness is assumed.
Actual quarter-period and half-period balls for the real-to-circle covering
verify the local injectivity, exact metric pullback and native volume equality.

All three changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds took
6.0, 2.8 and 4.0 seconds; the affected boundary-equivalence module also passed.
The 26,935-job root build passed without diagnostics; the existing aggregate
took 36 seconds. Exact evidence is in `mostow-holder-covering-volume.json`.
All 75 newly added Lean files have current source-hash-matched fresh
compilation evidence below 30 seconds.

The uniform fixed-boundary-triple basepoint bound, complete-line two-sided
tracking and the actual disk-control producer remain open. Finite-volume
cusp geometry and the final three-dimensional Mostow rigidity theorem are
still unproved; no headline completion is claimed by these layers.

## Verified boundary fixed points, Klein chords and original-cover volume

A hyperbolic isometry with no interior fixed point now has at most two fixed
boundary points, with nonemptiness proved in finite dimension by the native
unconditional Brouwer theorem. The cardinal bound is dimension free and uses
extended cardinality. An actual one-dimensional boost verifies sharpness;
no orientation restriction is present.

Native metric segments have exactly their closed Klein chords. Each distinct
ideal endpoint pair constructs an actual oriented geodesic whose Klein image
is precisely the open chord. Equal finite endpoints, dimension zero, and
non-antipodal ideal endpoints were checked. These are the geometric inputs
for complete-line Morse tracking, whose separate proof is still under review.

The actual original universal-cover deck displacement bound now implies
small-ball volume equality for the original projection. The native triangle
inequality and actual fiber transitivity derive injectivity; the exact lifted
metric and projection derivative derive the pullback identity. Changed
basepoint and nonpositive-radius consumers preserve the original objects.

All three new modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds took
8.8, 2.2 and 4.0 seconds. The 26,938-job root build passed without diagnostics;
the existing aggregate took 31 seconds. Exact evidence is in
`mostow-fixedpoint-klein-volume.json`. All 78 newly added Lean files have
current source-hash-matched fresh compilation evidence below 30 seconds.
The full three-dimensional finite-volume Mostow theorem remains open.

## Verified complete lines, ideal triangles and native model volume

The complete-line Morse theorem now chooses one bound before the original
curve and returns its actual distinct negative and positive ideal limits.
The constructed native geodesic has those oriented endpoints, and both
Hausdorff directions are proved separately. Nonlinear nonorigin curves and
reversed-time consumers verify the two-sided statement.

Every native complete geodesic has exactly its open Klein chord. Intersections
of fixed-radius tubes around the three actual sides of an ideal triangle are
compact: an escaping sequence would force one boundary limit into all three
endpoint pairs. No boundedness or compact-core premise is supplied.

A nilpotent subgroup acting freely on a finite-dimensional nontrivial model
has an actual boundary orbit of at most two points. The subgroup itself may
be trivial. Actual hyperbolic isometries preserve the native Riemannian tensor,
proved by differentiating their exact Lorentz extension. Consequently native
model ball volumes are center independent and positive for positive radii,
including the zero-dimensional model.

All six changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Final-source compilation took
at most 5.1 seconds in this batch; the 26,943-job root build passed without
diagnostics. The existing aggregate took 36 seconds. Exact hashes and evidence
are in `mostow-morse-triangle-model-volume.json`. All 83 newly added Lean files
have current source-hash-matched fresh compilation evidence below 30 seconds.

Root accidentally duplicated two reviewer assignments. One nilpotent review
directory was shared and report metadata overwritten; the sole review's
independent linter, axiom and consumer run evidence survived and was reconciled
in a new exclusive directory. A copied Riemannian-isometry audit driver also
overwrote an owner diagnostic output; its replacement status is explicitly
recorded. Mathematical source and shared caches were unchanged. The evidence
file records original and replacement provenance without asserting unknown
historical artifact hashes. Future reviewer directories require exclusive
creation, and all driver output paths must remain inside their owner directory.

The three-dimensional finite-volume Mostow theorem is still open. Uniform
fixed-triple normalization, actual plane disk control, finite-volume cusp
geometry, the controlled given homotopy equivalence, and boundary rigidity
remain required.

## Verified fixed-triple normalization and actual translation

When the original boundary map fixes a given distinct ideal triple, its
original coarse map now has a uniformly bounded origin displacement. The
bound is chosen before the map, using the fixed ideal sides, complete-line
Morse theorem, and compact intersection of their fixed-radius tubes. No
supplied basepoint bound, compact core or coarse inverse is used.

An actual three-dimensional Lorentz isometry now induces complex translation
in the fixed stereographic chart. The coordinate, pole-fixing and forward
and inverse chart laws retain the original isometry. Concrete nonidentity
and factor-two tests distinguish translation by b from translation by 2b.
Multiplication similarities remain a separate next producer.

Native comparison maps preserve the exact ball volume between the hyperbolic
model and the supplied complete simply connected curvature-minus-one metric.
The original basepoint, metric tangent isometry and comparison map are fixed
in the conclusion. A generic finite-index theorem also transfers finiteness
of an actual subgroup orbit to the actual group orbit, without normality;
a nonnormal S3 stabilizer consumer verifies this scope.

All four new modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. Fresh source builds took
6.6, 2.4, 5.3 and 0.842 seconds. The 26,947-job root build passed without
diagnostics; the existing aggregate took 36 seconds. Exact evidence is in
`mostow-normalization-translation-comparison.json`. All 87 newly added Lean
files have current source-hash-matched fresh compilation evidence below
30 seconds. The finite-volume Mostow headline remains open.

## Verified original plane similarities and normalized local mass

The original controlled coarse-inverse pair now induces an actual complex
plane homeomorphism through the native stereographic chart. Exact forward,
inverse, and swapped-pair laws retain the original boundary maps. Genuine
Lorentz isometries realize every nonzero complex multiplication with the
correct scaling, rotation and factor-two chart normalization.

The original negatively curved three-manifold's normalized downstairs balls
now have exactly the H3 origin-ball volume whenever their actual based-cover
deck displacement is large enough. No free basis, normalized curvature
premise, replacement cover or volume equality is supplied. The original
metric 4gH3 with curvature minus one quarter and a nonorigin basepoint verifies
the scaling and producer chain for every real radius.

Finite-index nilpotent subgroups produce actual finite boundary orbits with
freeness required only on that subgroup. The original uniform Margulis
construction supplies its actual small-displacement subgroup and finite-index
hypothesis from the true finite quotient bound. Separately, the same supplied
finite boundary orbit of any freely acting group has at most two points,
without a finite-dimensionality assumption.

All seven changed modules passed independent review, canonical builds, all
14 applicable linters and native axiom checks. All affected descendants of
the two visibility-only promotions were rebuilt. Fresh source builds took
at most 8.5 seconds; the 26,952-job root build passed without diagnostics and
the existing aggregate took 26 seconds. Exact evidence and the disclosed
read-only worker Git exception are recorded in
`mostow-plane-similarity-local-volume.json`. All 92 newly added Lean files
have current source-hash-matched fresh compilation evidence below 30 seconds.
The actual disk-control proof and finite-volume thick-part compactness are
active; cusp geometry, controlled homotopy representatives and final rigidity
remain open.
