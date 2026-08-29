# CurveEnergy

## Purpose

This module supplies the fixed-metric energy-to-distance estimate needed before
the compactness step in a direct method for Perelman curves.  It is deliberately
independent of the moving-metric and `L`-geometry layers.

## Public API

- `curveEnergy` is the oriented interval integral of the fully evaluated scalar
  `g.inner` square of `mfderiv`.
- `curveEnergy_mono` shows that this energy decreases on nested positively
  oriented subintervals, using integrability only on the outer interval.
- `arcLength_le_energy` proves the interval Cauchy–Schwarz bound
  `length ≤ √(b-a) * √(energy)` from `a ≤ b` and honest integrability of
  the scalar energy.
- `edistOf_le_energy` combines that bound with the native
  `riemannianEDist_le_arcLength` bridge for a `C¹` curve.
- `edistOf_le_budget` replaces the subinterval energy by any upper budget `C`,
  which is the direct `1 / 2`-Hölder estimate used by compactness arguments.

Metric-square nonnegativity is proved pointwise from positive definiteness; it
is not added as a consumer hypothesis.  The implementation reuses the native
`arcLength`, `riemannianEDistOf`, tangent-norm bridge, and Mathlib Hölder
inequality rather than introducing a second path-length API.

## Verification and frontier

Focused verification passes without `sorry` or linter warnings.  This routine
fixed-metric brick is complete.  It does not provide the genuinely separate
frontier needed by the full direct method: a project-native compactness and
lower-semicontinuity package for absolutely continuous manifold-valued curves.
