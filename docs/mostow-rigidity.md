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
| Root | Integrate the accepted full Lorentz-extension classification and derivative interfaces. |
| `review_hyperboloid_model` | Identify the native Riemannian distance with the arcosh metric. |
| `equivariant_descent` | Prove the existing-unit inverse estimate used by Zassenhaus. |
| `rigidity_assessment` | Supply the canonical Lorentz extension interface for boundary actions. |

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
