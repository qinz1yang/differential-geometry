# CenterOfMass.lean - Step C center-of-mass energy

## 2026-06-23

Started the reusable Riemannian center-of-mass layer for MSM135 Chapter 4 Step C.

What landed:

- `CenterOfMass.StrictMidConvexOn` and `CenterOfMass.min_unique_of_mid`: the
  small abstract uniqueness assembly from midpoint-strict convexity.
- `CenterOfMass.StrictMidJensenOn`: the midpoint Jensen predicate expected from
  the Hessian-comparison producer for each `1/2 d^2` summand.
- `CenterOfMass.metricEnergy` and `CenterOfMass.metricEnergy_lt_far`: the pure
  metric energy and the book estimate that points outside the `2r` ball have
  strictly larger energy than the center `p`, assuming nonnegative weights and
  at least one positive weight.
- `CenterOfMass.halfSqDist`, `CenterOfMass.metricEnergy_half`, and
  `CenterOfMass.metricEnergy_strict`: the finite-sum assembly showing that
  nonnegative weighted sums of per-summand strict midpoint Jensen functions are
  strictly midpoint convex when some weight is positive.
- `CenterOfMass.centerEnergy`: the finite weighted squared-distance energy for
  an explicit smooth Riemannian metric.
- `CenterOfMass.centerEnergy_cont`: continuity of that energy, using the
  project finite-locus `toReal` distance-continuity bridge and Hopf--Rinow
  finiteness.
- `CenterOfMass.exists_minOn_compact` and `CenterOfMass.exists_minOn_ball`:
  compact-set and closed-ball minimizer existence.
- `CenterOfMass.centerEnergy_eq_dist` and `CenterOfMass.centerEnergy_lt_far`:
  the Riemannian metric-realization bridge and the Riemannian outside-ball
  estimate.
- `CenterOfMass.centerEnergy_strict`: the Riemannian strict-convexity consumer
  from per-summand strict Jensen inputs.
- `CenterOfMass.jensen_of_strict`: the bridge from the native along-curve
  `StrictConvexOn ℝ unitInterval` shape to the midpoint Jensen input used by
  the finite-sum uniqueness assembly.
- `CenterOfMass.exists_global_min`: the C1 existence half; a global minimizer
  exists and lies in the closed `2r` ball.
- `CenterOfMass.exists_unique_min`: the conditional C1 uniqueness package,
  assuming strict midpoint convexity of the weighted energy on the closed
  `2r` ball.
- `CenterOfMass.exists_unique_jensen`: the C1 uniqueness package in the natural
  input shape, assuming each `1/2 d^2(., pts i)` summand satisfies
  `StrictMidJensenOn` on the closed `2r` ball.
- `CenterOfMass.exists_unique_curve`: the same C1 package stated in the
  Hessian-comparison-friendly form: every summand is strictly convex along the
  chosen joining curve on `unitInterval`, with endpoint and midpoint-membership
  data for the join.

Plan assessment:

- The continuity and existence side of C1 is proved.
- The uniqueness assembly is now available both from the internal
  `StrictMidJensenOn` input and from the native along-curve
  `StrictConvexOn ℝ unitInterval` shape. Producing that strict along-curve
  input from the Hessian-comparison `d^2` theorem remains the real geometric
  frontier; the current `ConvexBalls.lean` API only provides set convexity of
  small balls from a non-strict along-curve `ConvexOn` input.
- The gradient characterization still needs a named distance-squared gradient
  theorem for one `1/2 d^2` summand. The finite weighted-sum gradient algebra
  now lives in `Geometry/Operator/Operators.lean`.
- Consequently C2 smoothness and C3 averaging should wait for the strict
  convexity/nondegenerate Hessian and gradient producers rather than adding
  consumer-side assumptions.

Verification status: passed for the focused Lean check and targeted module
build. Axiom print for the new public endpoints, including
`metricEnergy_strict`, `centerEnergy_strict`, `exists_unique_jensen`,
`jensen_of_strict`, and `exists_unique_curve`, is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by these
declarations. The targeted build replayed existing upstream warnings outside
this file.

## 2026-06-24

Added the finite-gradient side of the C1/C2 interface.

What landed:

- `CenterOfMass.grad_centerEnergy`: under the Hopf--Rinow metric-space
  realization, the gradient of the finite weighted center energy is the finite
  weighted sum of the gradients of the one-point `halfSqDist` summands. The
  theorem is stated for `{kappa : Type}` rather than `{kappa : Type*}` because
  the current reusable `gradientFun_sum_smul` operator lemma is universe-0.
  This is enough for the intended finite Step C cover indices.
- `CenterOfMass.sum_grad_eq_zero`: at a differentiable global minimizer of the
  center energy, the finite weighted sum of the one-point summand gradients is
  zero. This uses the lower operator lemma
  `gradientFun_eq_zero_of_isLocalMin` and then rewrites by
  `grad_centerEnergy`.
- `CenterOfMass.sum_expInv_eq_zero`: the conditional book-form equation. If
  each one-point gradient is identified with the negative normal-coordinate
  inverse vector, then a differentiable global minimizer satisfies the weighted
  equation `sum_i mu_i * exp_q^{-1}(pts_i) = 0`.
- `CenterOfMass.grad_halfSqDist_of_flat`: the musical-map reduction from the
  first-variation covector identity for one `halfSqDist` summand to the
  corresponding gradient identity.
- `CenterOfMass.sum_expInv_of_flat`: the book-form center-of-mass equation
  directly from the first-variation covector identity for every summand.
- `CenterOfMass.metricEnergy_min_dist_le`: a pure metric stability estimate.
  If all input points are within `epsilon` of `qstar`, the weights are
  nonnegative with at least one positive weight, and `q` is a global minimizer
  of the weighted metric energy, then `dist q qstar <= 2 * epsilon`.
- `CenterOfMass.centerEnergy_min_dist_le`: the same estimate for the
  Riemannian `centerEnergy` after rewriting through `centerEnergy_eq_dist`.
- `CenterOfMass.exists_global_min_dist_le`: the existence package now can
  return a global minimizer in the closed `2r` ball together with the `2epsilon`
  stability bound when the input points are all within `epsilon` of `qstar`.
- `CenterOfMass.exists_unique_min_dist_le`: the strict-convexity uniqueness
  package now returns the unique global minimizer together with the same
  stability bound.
- `CenterOfMass.exists_unique_jensen_dist_le` and
  `CenterOfMass.exists_unique_curve_dist_le`: the natural per-summand Jensen
  and along-curve strict-convexity C1 entrypoints now also return the `2epsilon`
  stability bound.

Current frontier:

- The full book gradient characterization is now reduced to the single
  one-summand first-variation covector theorem
  `(mfderiv (halfSqDist pt) q).toLinearMap =
    metricFlatEquiv g q (-(normalChartAt g q pt))`,
  with the right normal-chart/source or cut-locus hypotheses. No such named
  theorem was found. The fixed-center `normalChartAt` smoothness and
  transition-map smoothness APIs are not enough: the missing bridge is
  first-variation control of the moving-base map
  `q |-> normalChartAt g q pt`.
- The strict along-curve convexity/Hessian positivity producer for each
  `1/2 d^2` summand is still the uniqueness/C2 input frontier. The current
  file only consumes that input.
- The book continuity clause `cm(q_i) -> qstar` has a checked metric core for
  any selected global minimizer, and the existing C1 existence/uniqueness
  packages now have checked stability variants. Turning this into continuity of
  a named center-of-mass map still needs uniqueness (or another canonical
  selector), so it remains downstream of the strict convexity input rather than
  a new analytic frontier.

Verification status: the focused Lean check passed for the edited file, and
the targeted module refresh completed with a current `CenterOfMass.olean`.
Axiom print for `grad_centerEnergy`, `sum_grad_eq_zero`,
`sum_expInv_eq_zero`, `grad_halfSqDist_of_flat`, `sum_expInv_of_flat`,
`metricEnergy_min_dist_le`, `centerEnergy_min_dist_le`,
`exists_global_min_dist_le`, `exists_unique_min_dist_le`,
`exists_unique_jensen_dist_le`, and `exists_unique_curve_dist_le` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by these
declarations. The later minimizer-stability edits also passed focused checking
and the targeted `CenterOfMass` module build; the build replayed only existing
upstream warnings.

Additional audit for the one-summand gradient theorem:

- `Variation.FirstVariation.first_variation_geodesic_fixed_end` now supplies
  the moving-start/fixed-endpoint first-variation boundary term for a
  unit-speed geodesic variation. This is the correct analytic core for
  `grad (1/2 d(., pt)^2) = - exp_q^{-1}(pt)`.
- The full `lbl411` theorem is not a direct consumer yet. The missing layer is
  not the fixed-base radial Gauss identity; it is a moving-base construction:
  for a base curve through `q` and fixed endpoint `pt`, build a smooth family of
  minimizing geodesics, show its arc length is locally the Riemannian distance,
  and identify the initial unit velocity with the normalized
  `normalChartAt g q pt` vector. Existing public radial-distance theorems are
  fixed-center statements and do not package this family.
- Therefore `sum_expInv_of_flat` remains the honest center-of-mass consumer.
  C2/C3 should still wait for the one-summand gradient theorem and the strict
  Hessian/nondegeneracy producer rather than starting from extra assumptions.

Verification status for this audit step: the new first-variation producer
passed focused checking, targeted module refresh, and an axiom print with the
usual project axioms.

The variation layer now also has two checked adapters:
`Variation.dist_deriv_of_length` and `Variation.halfSq_deriv_length`. They
consume the still-missing local hypothesis that a moving-start/fixed-end
geodesic variation realizes distance by arc length near the central curve, and
produce the derivatives of `dist` and `1/2 * d^2`. This moves the
one-summand gradient theorem one layer closer, but it does not yet remove the
`hflat` hypothesis from `sum_expInv_of_flat`: the remaining producer is still
the construction of that length-realizing variation and the conversion of the
resulting curve-derivative formula into the manifold `mfderiv` covector
identity.

Audit of the exponential-variation layer: `Geometry/Exponential/ExpVariationSmooth.lean`
already supplies joint smoothness of
`(r, s) |-> expMapIntrinsic g hEnorm (beta s) (r • W s)` when `beta` is a
smooth base curve and `s |-> (beta s, W s)` is a smooth tangent-bundle section,
subject to the existing local smallness/phase-ball hypotheses. Thus the
smoothness of the resulting geodesic variation is not the missing analytic
theorem. The remaining missing producer is the smooth launch field itself:
locally choose `W s = exp_{beta s}^{-1}(pt)`, prove this total-space field is
smooth, prove `expMapIntrinsic (beta s) (W s) = pt`, and keep it in the normal
radius where the local length-minimizing/distance-equality facts apply.

## 2026-06-24 - CenterOfMass-facing first-variation adapter

Added `CenterOfMass.halfSqDist_deriv_of_lengthVariation`.

This theorem rewrites the checked fixed-end variation derivative into the
actual one-point summand used by center-of-mass energy:
`s |-> halfSqDist pt (beta s)`. Its hypotheses deliberately keep the honest
geometric input visible: a smooth variation is supplied, its final endpoint is
the fixed target `pt`, and its arc length locally realizes distance from the
moving initial point.

This closes the notation/API gap between `Variation.halfSq_deriv_length` and
the CenterOfMass energy layer. It does not close the full book gradient theorem;
the remaining producer is still the moving-base inverse-exponential section
and the conversion from this curve-level derivative to the manifold covector
identity consumed by `grad_halfSqDist_of_flat`.

Verification status: the focused Lean check passed, and an axiom probe for the
new theorem reported `[propext, Classical.choice, Quot.sound]`. The targeted
module build was not completed in this pass because the Lake build process
orphaned after a tool timeout.

## 2026-06-24 - moving-base inverse-exponential audit

The variation-constructor part of the one-summand gradient route is now
available in `Variation.exists_expVar_fixEnd`: once a smooth launch field
along a curve vanishes at the final parameter, it produces the required
moving-start/fixed-final smooth variation.

The remaining blocker is lower than `halfSqDist` notation but higher than
fixed-base normal-chart smoothness. Existing infrastructure gives:

- fixed-base local diffeomorphism of `expMap g p` near `0`;
- fixed-base `normalChartAt g p` smoothness on its normal ball.

What is still missing is the moving-base inverse section: a local smooth field
`s |-> exp_{beta s}^{-1}(pt)` (or equivalently a local diffeomorphism for the
diagonal exponential map `(p, v) |-> (p, exp_p v)`). This is the theorem needed
to turn `halfSqDist_deriv_of_lengthVariation` into the full covector identity
consumed by `grad_halfSqDist_of_flat`.

Follow-up progress in the variation layer: `Variation.exists_sqDeriv_field`
now wires the smooth launch-field variation constructor into the derivative of
`1/2 * d^2`, rewriting the initial variation vector to the supplied field value
`V 0`. Thus the center-of-mass gradient route is reduced further to producing
the specific smooth moving-base inverse-exponential field and proving its local
distance-realization property.

## 2026-07-15 - zero-weight energy congruence

Added `CenterOfMass.centerEnergy_congr`.  It states at the canonical energy
layer that two finite point families give the same center energy when they
agree at every nonzero-weight slot.  This is the proof-independent bridge used
to replace inactive stage targets without changing the global minimizer.

Focused verification and the exact module refresh passed.  This helper is
complete; it does not by itself construct a smooth inactive-slot filler or a
Step-B1 comparison map.
