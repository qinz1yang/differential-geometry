# `ActionMinAccel.lean`

## Result

`lChart_min_accel` proves that every positive fixed-chart local minimizer of
the genuine regularized L-action satisfies the intrinsic regularized
L-geodesic acceleration equation at every interior parameter time.

The chart representative uses local parameter `r`, while the geometric
square-root time is `a + r`.  The theorem therefore reconstructs the shifted
manifold curve

```text
alpha(s) = (extChartAt I p).symm (u.toFun (s - a))
```

and states the equation at the global time `a + r`.  This avoids the incorrect
time `T - r^2` that would result from applying the phase theorem directly to
the unshifted local chart path.

## Proof route

The proof obtains the continuous velocity and `C1` momentum from
`lChart_mom_c1`, upgrades the same velocity to `C1` with `lChartVel_c1`, and
differentiates the pointwise momentum identity on the open interval.  After
cancelling its factor `2`, `lChartEuler_iff` gives the second phase equation.
The shifted position and velocity derivatives combine into a phase derivative
at `a + r`; `lPhase_accel` then gives the intrinsic equation for the phase
velocity.  Finally, `lPhase_velocity` on a neighborhood and
`covDerivAlong_congr_of_eventuallyEq` replace that auxiliary field by the
actual `lVelocity` of `alpha`.

No Euler equation, acceleration equation, regularity conclusion, reference
module, new class, or frontier wrapper is assumed.

## Verification and progress

Focused verification passed without warnings or placeholders.  The theorem
is 100% complete.  It closes the fixed-chart minimizer-to-classical-equation
consumer; finite-piece transport to the global attained minimizer remains the
next L-geometry assembly step.  The terminal `exists_lMinimizer` and
`redVolume_anti` remain 0%; dedicated L-geometry machinery is approximately
97--98%, reused generic infrastructure is 100%, P2 remains below 1%, and the
whole Poincare program remains approximately 3--5%.
