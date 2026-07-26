# HeatDuhamelLower

## Producer

This module supplies the dimension-generic lower spatial jets of the
Euclidean heat potential for a general time-dependent bounded forcing path.

- `heatDuh` is the value potential.  `heatDuh_norm` gives its exact
  `t * K` estimate, and `heatDuh_sqrt` places it under the common
  `sqrt t * K` bound on horizons at most one.
- `heatD1Duh` is the first spatial derivative potential.
  `heatD1Duh_norm` gives the explicit
  `2 * d1DuhConst * sqrt t` estimate.
- The two `_int` theorems derive interval integrability from strong
  measurability and the same uniform forcing bound.  No derivative of the
  forcing is assumed.

The proof uses the already proved pointwise heat contraction, the
first-derivative heat-kernel `L1` estimate, and the exact identity

`integral_0^t (t-s)^(-1/2) ds = 2 sqrt(t)`.

## Role in uniform short-time existence

This is the concrete small-time analytic factor for the first/zero-order
parametrix error `B10`: its value part gains `t`, and its gradient part gains
`sqrt t`.  Those gains depend only on the forcing-size bound and fixed
Euclidean heat constant, so a later finite-chart assembly can choose one
positive horizon before the member of the metric family.

It does not claim the principal `D2` Schauder estimate.  That estimate uses
the cancellation in `HeatKernelDuhamel` and still needs spatial and temporal
Holder output estimates before a complete `FinHolderBall` self-map exists.

## Verification

The source is written without `sorry`, `admit`, axiom, opaque declaration,
new instance, or high-Sobolev input.  Per parent instruction this lane did not
run Lean or Lake; focused verification is pending.  The exact theorem
`ricci_flow_unif_existence` therefore remains 0%.
