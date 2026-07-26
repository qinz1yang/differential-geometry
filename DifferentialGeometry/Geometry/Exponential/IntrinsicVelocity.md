# IntrinsicVelocity status

## 2026-07-23 component-local API

- Removed the accidental file-wide `ConnectedSpace M` assumption.  The file
  contains no connectedness argument: each construction follows one complete
  intrinsic geodesic inside the component of its initial point.
- The complete source file remains focused GREEN, and its exact artifact is
  current (`3796/3796`).
- This makes `intrinsicVelocityLift`, `intrinsicExp_smooth`,
  `intrinsicFiber_smooth`, and `intrinsicVar_smooth` usable by the pointwise
  Route B-prime Calabi construction without adding connectedness to the
  complete-Shi theorem.

## 2026-07-18

- `intrinsicVelocityLift` is the true tangent-bundle velocity lift of the
  complete intrinsic geodesic.
- `velocityLift_zero` identifies its initial value with the supplied tangent
  vector.
- `lift_isIntegral` proves that the lift is a global integral curve of the
  basepoint-free geodesic spray.
- `velocityLift_one` applies the compact-trajectory smooth-slice theorem on
  `TM` and proves global smooth dependence of the time-one velocity lift.
- `intrinsicExp_smooth` projects that lift and proves global smoothness of the
  complete intrinsic exponential on the full tangent bundle.
- `intrinsicFiber_smooth` restricts the joint intrinsic exponential to one
  tangent fibre and proves global smoothness in the launch vector.
- `intrinsicVar_smooth` proves global joint smoothness of the fixed-base
  variation `(s,t) ↦ intrinsicGeodesic p (x + s • w) t`.
- The proof uses the existing pointwise chart-centered lift, identifies its
  fibre with the manifold derivative of the projected intrinsic geodesic, and
  then uses `geodesicVectorFieldChart_eq_geodesicVectorField`.
- The velocity-lift, time-one endpoint, fixed-fibre, and affine-variation
  exports are all focused- and exact-green.

## Boundary

This file supplies the exact trajectory family required by the generic
compact-trajectory smooth-dependence theorem. It does not itself construct a
normal-coordinate radius or `NormalRadiusProfile`.

## Progress

- Intrinsic velocity-lift definition/initial value/integral-curve theorem:
  100% implemented, focused-green, and exact-green.
- Smooth time-one intrinsic geodesic flow and intrinsic exponential: 100%
  implemented, focused-green, and exact-green.
- Fixed-fibre and affine two-parameter smoothness: 100% implemented,
  focused-green, and exact-green.
- Native `NormalRadiusProfile.le_exp_radius`: 0%; dedicated zero-order
  machinery is about 99% complete. The natural intrinsic Jacobi/differential
  identity is proved; the remaining independent gate is agreement with the
  ordinary exponential on the sub-injectivity ball and canonical branch
  construction.
- Whole HCG compactness machinery remains about 60%; the unconditional
  textbook compactness endpoint remains 0%.

## Next target

Use the now-proved intrinsic Jacobi endpoint differential identity to establish
ordinary/intrinsic exponential agreement on the sub-injectivity ball, then
construct the canonical injective partial diffeomorphism.
