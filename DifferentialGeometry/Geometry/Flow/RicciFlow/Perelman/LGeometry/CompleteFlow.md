# CompleteFlow

## Purpose

This module is the first producer in the complete bounded-curvature L8 lane.
It formalizes the coercive part of Morgan--Tian's minimizing-sequence argument:
a scalar-potential lower bound and uniform comparison with one complete
reference metric turn an L-action budget into a fixed-metric energy budget;
the energy--distance estimate then confines the whole curve to one compact
intrinsic ball by the native Hopf--Rinow properness theorem.

The reference-metric comparison and scalar lower bound are the exact two
consequences supplied by a spacetime curvature bound.  They remain explicit
here so this first producer has the weakest hypotheses and does not introduce
a new bounded-flow class or duplicate curvature-bound hierarchy.

## Public API

- `lRegEnergy_le` bounds fixed-reference-metric curve energy by the regularized
  L-action budget.
- `lRegRange_compact` returns a compact set containing the entire image of the
  curve on the prescribed interval.  It assumes completeness of the reference
  metric, not compactness of the manifold.
- `lRegRanges_compact` uses one common start and action budget to place an
  entire sequence of curves in the same compact reference-metric ball. This is
  the common-range input needed by complete-flow local-cost arguments.

Both results reuse `lRegKinetic_le`, `edistOf_le_budget`, and
`RiemannianMetricComplete.closedEBall_isCompact`.

## Verification and frontier

Focused verification passes without `sorry` or linter warnings, and the
targeted module artifact has been refreshed successfully, including the family
producer.

The complete noncompact minimizer theorem is now proved downstream; this module
is its lowest coercivity layer. The new family theorem advances the separate
common-range stage for a complete-flow local-cost theorem, but does not by
itself provide local vector bounds or Lipschitz continuity. L8 as a whole is
roughly **30--35%**, while the complete-flow local-cost extension itself remains
unstated (**0%**); its dedicated common-range machinery is now verified.
