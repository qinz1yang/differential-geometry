# MetricKoszul

## Role

This module records the model-space coordinate Koszul covector determined by
the first derivative of a metric-valued map, raises it using the coercive
metric sharp operator, and supplies explicit operator-norm bounds.  It is the
algebraic producer needed before proving a normal-coordinate geodesic-flow
estimate; it is not itself a second definition of geometric Christoffel data.

## Current state

- `koszulCov` is the structural three-term coordinate Koszul expression.
- `koszulCov_sub` records its subtractivity in the metric derivative.
- `koszulCov_norm_le` turns a pointwise trilinear constant `C` into the sharp
  `(3/2) * C` covector bound without component enumeration.
- `koszulCovCLM` packages the Koszul covector construction as a bounded linear
  map in the metric derivative, with application and operator-norm lemmas.  This
  is the proof-independent operator used by the H6 all-order recurrence.
- `koszulVec` raises that covector using `IsCoercive.sharp`.
- `koszulVec_norm_le` combines a coercivity constant with the covector bound.
- `koszulCov_diag_sub` expands diagonal velocity variation into the two
  bilinear slot differences.
- `koszulVec_diag_le` raises that identity and bounds
  `K(v,v) - K(w,w)` by a constant times
  `(‖v‖ + ‖w‖) * ‖v - w‖`.
- `koszulVec_sub_le` combines derivative variation with the sharp resolvent
  estimate, giving one explicit bound when both the metric and its first jet
  vary.

Focused verification and the targeted module build passed without proof or
style warnings.

## Frontier

The global model-space Levi--Civita realization is now available in the
connection layer.  The remaining geometric bridge is its localization to a
normal-coordinate ball and then the identification with the intrinsic
geodesic flow.  This file deliberately does not encode either bridge as an
assumption.
