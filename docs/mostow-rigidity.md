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
compiler processes run concurrently, with at most one per owner. Existing
builds must be polled before another build of the same target is launched.
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
| Root | Integrate reviewed Morse, boundary-continuity and quotient-action packets. |
| `review_orbit_quotients` | Prove the quantitative tube bound for continuous quasi-geodesic segments. |
| `review_hyperboloid_model` | Identify the intrinsic metric segment with the actual geodesic-line interval. |
| `rigidity_assessment` | Prove joint continuity of the actual closed-ball and sphere actions. |
| `review_hyperboloid_metric` | Prove properly discontinuous action of discrete isometry subgroups. |
| `equivariant_descent` | Audit the exact native finite-volume three-dimensional Mostow headline type. |

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
