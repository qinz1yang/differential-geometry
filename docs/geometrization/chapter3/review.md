# Independent mathematical review of the first Chapter 3 proof batch

Review date: 2026-09-28. Target: Lean 4.35.0-rc3, mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`. This is an independent review of
other contributors' declarations and proof bodies, not a review of the
reviewer's own envelope, open/KL approximation, or pointed precompactness
implementations. The latter receive separate review by the integrating agent.

## Result and scope

No incorrect mathematical contract was found in the declarations reviewed
below. This does **not** mean that every natural-language claim of Chapter 3
has a corresponding declaration. Remaining coverage boundaries are listed
explicitly below. Formal kernel checking and mathematical source comparison
are distinct checks.

The review read the complete bodies of `PointedIsometry`,
`PointedConvergence`, `KleinerLottConvergence`, `MidpointTransfer`,
`CompactComparison`, `ProductCollapse`, `GeodesicMidpoint`, `CurveMidpoint`,
`CurveVariation`, `GromovHausdorffCompactness`, and the supporting
`EventualDiagonal`. It subsequently read the completed `ApproximateMidpoint`,
`ClosedBallConvergence`, `LipschitzCompactness`, and the general complete-limit
curve closure added to `MidpointTransfer`.

## Mathematical checks

- **MC24: actual pointed isometry.** `PointedIsometry` produces an isometry
  equivalence, not just an embedding. One ultrafilter is used for all source
  points. Surjectivity is separately established from coverage witnesses and
  compactness of a bounded set of preimages. Both limits are proper. The
  common approximating source sequence need not be proper. The two
  approximations are selected at the same sufficiently late index before
  inversion and composition. Uniqueness means existence of a pointed
  isometry between limits, not uniqueness of that isometry as a function.
- **MC22: completeness really suffices.** `ApproximateMidpoint` uses coherent
  dyadic refinement and a summable displacement bound; it does not silently
  use properness. Its error recurrence is
  `delta(n+1) = delta(n)/2 + epsilon(n)`, with
  `epsilon(n) = tau/8 * (1/2)^(2*n)`. The resulting curves have Lipschitz
  constant `dist(a,b)+tau/2` and variation strictly below `dist(a,b)+tau`.
  The zero-distance case requires no division by the endpoint distance.
- **MC23: proper geodesic conclusion.** `GeodesicMidpoint` uses compact balls
  to produce exact midpoints and exact metric segments. Its sampled step
  maps need not be continuous; their approximate Lipschitz inequalities pass
  to the common ultrafilter limit. The proof is valid also when the endpoint
  distance is zero. Properness here is explicit and is not conflated with
  the weaker completeness assumption in MC22.
- **MC01/MC21/MC14: actual curve length and its consumers.** `eVariationOn` is
  mathlib's supremum of sums of consecutive distances over finite monotone
  chains. The review inspected that definition and its strict-partition
  formulation. The curve results use this actual variation, including its
  possible value infinity. The Lipschitz upper bound, pointwise lower
  semicontinuity, intermediate-value midpoint argument, and compact-target
  Arzela--Ascoli specialization have their stated hypotheses. Midpoint
  transfer uses actual coverage witnesses, with explicit radius and error
  losses. The completed `arbitrarily_short_curves` composition requires only
  completeness of the limit, obtained from `PointedGHConverges`. Its stronger
  exact-segment counterpart explicitly requires a proper limit.
- **MC11 and convergence quantifiers.** The project's convergence predicate
  supplies eventual maps separately for every fixed radius and positive
  accuracy. It does not assert a single map working for all accuracies.
  The open/closed equivalence uses slack in both radius and accuracy.
  Reverse approximations are not asserted with the same error constant.
  KL convergence uses whole maps and the genuine infimum-distance clause;
  the diagonal lemma permits its chosen scale index to tend to infinity
  without being monotone. KL approximations are required only eventually,
  so exceptional prefixes do not create a hidden obligation. Their scale
  parameters are positive; no use is made of Lean's inverse at zero.
- **MC12 and compact comparison.** Uniform covering cardinalities and a
  uniform diameter bound are actual hypotheses of compact extraction.
  The canonical GHSpace representatives are related to the input spaces by
  actual isometries. The `epsilon/2` net input supplies the strict open-ball
  cover required by mathlib's `GromovHausdorff.totallyBounded`, whose signature
  and proof route were inspected. `ghDist_le_of_map` needs no continuity of
  the map. Its non-strict zero-error endpoint is legitimate: nonempty spaces
  and zero distortion/coverage give an onto isometry. A negative error makes
  its hypotheses impossible. Pointed-to-compact convergence retains the
  uniform diameter bound; it is not asserted for arbitrary compact pointed
  sequences with unbounded diameter.
- **MC15: closed balls.** `ClosedBallConvergence` trims in the target using
  actual metric segments, both for image points and boundary coverage.
  Distances on the ball carriers are the restricted ambient distances.
  It does not replace them by an intrinsic path metric. Properness of source
  and target makes these carriers compact. The convergence theorem is stated
  for positive radius. The radius-zero singleton case is harmless but not
  separately packaged in this declaration.
- **MC16: the product convention.** `ProductCollapse` uses `WithLp 2`, with
  an explicitly proved Pythagorean distance formula. It proves the sharp
  bound `dGH(X times Y, X) <= diam(Y)/2` and convergence for shrinking
  compact-factor diameters. The pointed construction also allows a
  noncompact complete base. A fixed factor with an explicitly rescaled
  metric is a further adapter, not an implicit feature of these theorems.

Basepoints ensure nonempty spaces in pointed results. Unpointed compact GH
results state nonemptiness explicitly. Empty spaces are therefore not
silently passed to mathlib's nonempty compact GH space. Universes may differ
between source and limit; all comparisons retain the same specified source
carrier and metric at a chosen index. Positive errors, strict coverage, and
lost-radius conditions remain visible in the approximation constructors.

## Remaining coverage boundaries

These are boundaries of this reviewed batch, not claims that the underlying
mathematical results are unknown or unavailable elsewhere in mathlib.

Integration update: subsequent additions completed the correspondence formula
and all global inverse estimates, the actual rescaled product, generic metric
Hopf--Rinow, BBI's strict-supremum adapters, and the escaping-point example.
Their separate independent reviews are in `final_metric_review.md` and
`hopf_rinow_review.md`. The numbered observations below retain the scope of
this earlier review; `node_coverage.md` records the current coverage.

1. The full MC04 correspondence-distortion characterization and every
   direction of MC05's global inverse-map package are not supplied by
   `CompactComparison`. It supplies a forward map-to-GH estimate and the
   required compact convergence consumer. Existing mathlib GH results are
   reused; their presence should not be confused with a completed binding
   of every blueprint statement.
2. The literal fixed-factor `t`-scaled product metric and the displayed flat
   torus example in MC16 are not constructed in the reviewed
   `ProductCollapse` file. After the independent review, the reviewer wrote
   `Scaling/Rescale` and `Approximation/ScaledProductCollapse`, supplying the
   actual scalar metric, weighted-product formula, sharp GH bound, and
   compact/pointed convergence. Those additions require the integrating
   agent's separate review; see `scaled_product.md`. The smooth flat-torus
   interpretation remains outside these metric-only modules.
3. After this review, the reviewer implemented MC01's complete + locally
   compact + near-short-curves properness theorem and its exact-segment
   consequence in `Topology/MetricSpace/HopfRinow`. The actual compact-ball
   supremum/enlargement proof compiles, and a different contributor is
   reviewing it; see `hopf_rinow.md`. A general reparameterization theorem
   for arbitrary rectifiable curves is still not supplied, but the chosen
   route obtains exact segments through the proved midpoint construction
   and therefore does not depend on that theorem.
4. The full BBI source-convention binding, especially its separate
   strict-supremum formulation, is not represented by a declaration merely
   because the project's pointwise open/closed approximation predicates are
   equivalent. KL's actual infimum clause has its own explicit adapters.
5. Smooth convergence bindings and the geometric producers of covering
   bounds, Alexandrov curvature, and dimension remain outside this metric
   batch. MC18 belongs to the Chapter 4 comparison input. Nothing here
   establishes compatibility with a future migrated PC manifold foundation
   beyond the deliberately independent metric interfaces.

In particular, the initially observed complete-only MC22/MC14 gap was closed
during this review by the coherent-refinement proof and its downstream
composition; it is **not** a remaining hole in this batch.

## Source and verification evidence

The natural-language comparison used `master207A.tex`, Chapter 3, especially
MC01 (lines 660--788), MC04--MC05 (916 onward), MC11--MC16, and MC21--MC24
(1534--1739 for the midpoint/limit consumers). Previously checked source
records `reference_checks_revision58.md`, `revision59`, `revision60`,
`revision61`, and `revision68` were reused for unchanged source claims.
No new assertion is made that all references or errata were reread. The
source-specific leaf notes retain exact printed/PDF-page locators.

An independent combined `lake build` of nine principal leaves completed
successfully (2190 jobs), including MC22, MC24, KL convergence, midpoint
transfer, closed-ball convergence, product collapse, compact GH extraction,
and Lipschitz compactness. The only reported warning was a style suggestion
about `letI` in the then-current `MidpointTransfer` proof.

An independent `#print axioms` check of ten principal conclusions completed
successfully: proper pointed uniqueness, KL convergence equivalence,
complete-limit curve closure, complete approximate-midpoint curves, proper
metric segments, closed-ball convergence from short curves, Lipschitz curve
compactness, compact GH extraction, the product diameter estimate, and
pointed product convergence. Every result depended only on `propext`,
`Classical.choice`, and `Quot.sound`; none depended on `sorryAx` or a new
mathematical axiom. This is not a claim that the entire PC or geometrization
library was rebuilt by the reviewer.
