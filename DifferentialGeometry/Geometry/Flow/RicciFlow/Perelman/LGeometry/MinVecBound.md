# MinVecBound

## Result

`lRegInit_bound` proves that a sequence of initial tangents is bounded in the
canonical model norm when all corresponding regularized L-rays exist on one
fixed positive square-root-time interval, that interval stays in a regular
backward-time slab, and their regularized L-actions have a common upper bound.
No minimizing hypothesis is needed.

The proof is split into three narrow steps:

- `lRayAction_int` obtains the kinetic and Lagrangian integrability needed by
  `lRegKinetic_bound` from regularity of the ray on the compact interval.
- `lRayMetric_bdd` combines the action-to-kinetic estimate with `lGrad_bound`,
  `lRicci_bound`, and `lRegInit_bdd` to bound the initial moving-metric energy.
- `initNorm_bdd` uses `gpCoerciveConst_pos` and `gpCoerciveConst_le` to turn
  the common metric-energy bound into `Bornology.IsBounded (Set.range Z)`.

## Verification and boundary

Focused verification passed without warnings or placeholders. The initial
attempt exposed a performance issue rather than a mathematical obstruction:
disabling the canonical tangent model-norm instances around the final
bornological conclusion left its norm and metric structure unavailable and
made typeclass search diverge. The final scope retains those instances for
`initNorm_bdd` and the public theorem and disables them only inside the private
moving-metric helpers.

This finishes the action-to-initial-vector boundedness producer for the compact
initial-vector stage. It does not itself choose a convergent subsequence or
prove that a limiting ray remains minimizing; those are downstream compactness
and stability steps. The dedicated boundedness brick is complete (100%). The
reduced-volume monotonicity theorem `redVolume_anti` remains unproved (0%);
generic compactness and coercivity infrastructure is reused rather than added
here.
