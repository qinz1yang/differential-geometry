# Joint scalar-curvature regularity

## Goal

Prove joint spacetime smoothness of the genuine scalar curvature of a
`SolutionOn` on `D.regular ×ˢ univ`, with no chart-selector hypothesis and no
new consumer-side regularity package.

## Route

`scalar_joint` works pointwise.  At `(t, x)` it uses the actual local coordinate
frame centered at `x` and only reasons on
`D.regular ×ˢ coordinateFrameSet x`.  `coordMetricSmooth` supplies joint
smoothness of metric components, while `timeDeriv_smoothAt` preserves joint
smoothness after taking the time derivative.  The Ricci-flow equation identifies
each Ricci component with `-1/2` times that derivative.  Smooth inverse-metric
components from `coordInvSmoothAt` and the finite trace formula then recover the
scalar curvature.

This avoids a globally selected frame, a varying-fiber tensor-valued continuity
statement, and a coordinate expansion of the curvature tensor.

## Verification status

The proof has elaborated through all geometric and component APIs.  The last
definitional equality between the stored Ricci tensor and the solution-family
Ricci tensor has been discharged, but the final focused verification is pending
because concurrent dependency builds are currently making imported `.olean`
files disappear and reappear.  This is a verification/tooling blocker, not a
remaining proof obligation.

## Progress accounting

- `scalar_joint`: theorem body present; count as 0% verified until the final
  focused check is green.
- Joint scalar-coefficient producer machinery: about 95%; only final verification
  remains.
- Moving-metric conjugate-heat existence: theorem 0%; its dedicated machinery is
  still separate from this producer.
- Perelman no-local-collapsing: theorem 0%.
