# Metric.lean

## 2026-06-13

Updated metric-curvature callers after Levi-Civita curvature symmetry wrappers
stopped taking explicit local smoothness arguments.

Verification: focused check passed.  No new `sorry` or `admit`.

## 2026-07-14

Added `metricCov_congr_nhds`, the canonical field-germ locality projection for
the metric Levi--Civita derivative.  It reuses the existing covariant-
derivative locality theorem and introduces no new connection structure.  The
first attempt used an unavailable neighborhood notation in this module; the
explicit `nhds` form is focused-green without local warnings.

## 2026-07-16 Ricci derivative symmetry

Added `metricNablaSymm`, the invariant symmetry of the total covariant
derivative of the canonical Ricci tensor in its two Ricci slots.  The proof
uses the native coordinate-component symmetry bridge and evaluates only at a
single fiber; it does not introduce a global frame or a whole-bundle equality.
Focused verification passed without a new `sorry`.
