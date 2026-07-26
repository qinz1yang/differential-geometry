# CorrectionContraction

## Role

This is the low-layer bridge between the `christoffelCorrection` used by the
chart-local Levi--Civita construction and the `chartChristoffelContraction`
used by the geodesic phase-space ODE.

## Current state

- `correction_eq_contr` exposes the equality formerly available only as a
  private helper in the variation layer.
- `const_cov_eq_contr` specializes the canonical Levi--Civita derivative to a
  literal constant field on a self-model vector space and identifies it with
  `chartChristoffelContraction`.  The proof passes through the project-native
  chart-constant field so it does not depend on fragile tangent-bundle
  definitional equality.

Focused verification and the targeted module build passed without local proof
or style warnings.

## Frontier

The low-layer bridge is complete.  Its first consumer is the equality between
the `normalTotal` chart phase vector field and `PhaseFlow.phaseField
normalAccel`; after that the remaining frontier is trajectory confinement and
geodesic endpoint realization, not Christoffel-coordinate algebra.
