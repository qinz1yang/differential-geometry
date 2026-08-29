# Regularized L-ray speed control

## Result

`lRegSpeedSq` fully pairs the regularized velocity against the moving metric,
so downstream estimates remain scalar even though tangent fibers move with the
curve.  `lRegSpeedSq_nonneg` records its sign, and `lRegSpeedSq_deriv` proves
the exact Morgan--Tian speed-square evolution along every `IsLRegCurveOn`
witness.

`lRegSpeed_gron` consumes precisely the along-ray bounds for the scalar-gradient
pairing and Ricci quadratic form and gives a two-sided-time scalar Gronwall
comparison.  The deliberately coarse positive affine constants avoid a false
division by a possibly zero curvature bound.

`lRegInit_bdd` is the initial-vector compactness input.  For square-root time
`B` in a fixed positive interval `eps <= B <= R`, it turns a uniform kinetic
budget into an explicit bound for `g(T)(Z,Z)`.  It does not compare tangent
bundle or Hom objects, and it does not assume minimizing behavior: a minimizing
ray enters only through the action/kinetic budget, exactly as in the
Morgan--Tian corollary.

## Verification and frontier

Focused verification passes without warnings or placeholders.  No
reference-tree module is imported.

The remaining consumer assembly is not another differential inequality.
`lScalar_lower` and the defining split of `lRegLag` already turn a uniform
full-action upper bound into the kinetic budget consumed by `lRegInit_bdd`.
For the differential-equation constant,
`compactUnitTimeSlab_absBound` supplies the Ricci quadratic estimate once the
existing Ricci continuity witness is installed.

The smallest missing native producer is the one-form analogue for scalar
curvature: on a compact regular time slab, it should bound

`|g_t (gradient R_t) v| <= C * sqrt (g_t v v)`

uniformly in `t`, `x`, and `v`.  The current `chartScalCov_smooth` proves joint
smoothness of the spatial scalar differential in each fixed chart, but no
exported theorem yet packages those local covectors into this intrinsic
unit-tangent compact-slab bound.  Direct native search found no existing
scalar-gradient slab theorem; the tensor quadratic slab API covers Ricci but
not one-forms; and deriving the estimate indirectly from the regularized
phase-field acceleration would require new tangent-slab realization plumbing.
Thus automatic action/compact-slab packaging stops exactly at this missing
producer rather than adding a consumer assumption.

Minimizing-vector stability under a convergent initial-tangent sequence is a
separate theorem after this boundedness input.
