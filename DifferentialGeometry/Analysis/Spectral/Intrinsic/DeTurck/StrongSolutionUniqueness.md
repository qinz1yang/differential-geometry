# StrongSolutionUniqueness

## Source status

Source implementation complete; focused Lean verification is deferred while a
shared named dependency build remains active.

## Why this producer is needed

The total Ricci--DeTurck Sobolev nonlinearity generally does not satisfy the
globally small Lipschitz hypothesis `2 * L < 1`.  The live concrete solver in
`DeTurckQuasilinearExistence.lean` instead contracts
`nemytskiiMixedForcingMap` on a small forcing ball.  Its contraction modulus is

`C1 * sqrt (1 + T) * rho * (1 + T) + C2 * (2 * sqrt T)`.

Thus the small force radius controls the critical two-derivative arm and the
small time controls the lower-order arm.

## Proved source facts

- `mixForce_unique`: two fixed points of the concrete mixed forcing map in the
  same radius-`rho` ball coincide when the displayed modulus is less than one.
- `deTurckStrong_unique`: two independently supplied zero-trace strong pairs
  satisfying the same genuine Nemytskii equation and the same forcing-ball
  budget coincide.  Reverse Duhamel realization is used first; the mixed-map
  uniqueness then identifies the forces, fields, and `timeH1` carriers.

No Duhamel representation is assumed for the input strong pairs.  No
`sorry`, axiom, opaque producer, harmonic-map-flow assumption, or strengthened
global-small-Lipschitz hypothesis is introduced.

## Remaining geometric bridge

For an arbitrary smooth geometric Ricci--DeTurck solution on a short translated
window, the geometric layer must still produce the spectral perturbation pair,
its cross-scale link and strong equation, identify the genuine remainder with
the total Sobolev Nemytskii map while the perturbation stays in the realizability
ball, and bound its forcing by the solver radius.  The common DeTurck gauge for
two arbitrary Ricci flows remains a separate geometric construction.

## Honest progress

- Exact `ricci_flow_forward_unique`: 0% until its existing theorem is proved and
  checked.
- Concrete mixed-map arbitrary-strong-pair uniqueness machinery: 90%; source is
  present, with 10% reserved for focused elaboration and repair.
