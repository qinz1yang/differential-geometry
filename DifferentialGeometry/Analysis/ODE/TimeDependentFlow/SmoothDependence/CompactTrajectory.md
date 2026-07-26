# CompactTrajectory status

## 2026-07-18

- `exists_flow_compact` constructs one positive restart width over an arbitrary
  compact set from the existing pointwise manifold local-flow theorem.
- `flow_slice_smooth` proves that an already-selected family of exact
  trajectories of a globally smooth autonomous manifold field depends
  smoothly on its initial point at every interior time.
- The construction uses compactness only for the reference orbit through the
  point under consideration. It does not assume `CompactSpace` for the ambient
  manifold.
- Both declarations are now canonical focused- and exact-green. The exact
  refresh completed all 2782 jobs.

## H6 role

Applied on `TM` to the smooth basepoint-free geodesic spray, this removes the
need to upgrade the long finite chart-chain continuity proof. The canonical
intrinsic velocity lift now supplies the exact trajectory family, and the
time-one application is focused-green in `IntrinsicVelocity.lean`.

## Progress

- Compact-restart producer: 100%, focused- and exact-green.
- Manifold smooth-slice theorem: 100%, focused- and exact-green.
- Native `NormalRadiusProfile.le_exp_radius`: 0%; this file is dedicated
  machinery, not the H6 endpoint itself.
- Whole HCG compactness machinery remains about 60%; the unconditional
  textbook compactness endpoint remains 0%.

## Next target

The generic ODE brick is complete. Its H6 consumer is
`Exponential.velocityLift_one`; the next independent geometric target is the
Jacobi/differential identity for the intrinsic exponential on its natural
domain.
