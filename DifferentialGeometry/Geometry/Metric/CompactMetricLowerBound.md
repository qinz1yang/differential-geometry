# CompactMetricLowerBound

## Compact-set lower bound

`metric_lower_on` gives a positive comparison lower bound between two smooth
Riemannian metrics on any compact base set.  It minimizes the target quadratic
form on `metricUnitOn_compact` and keeps the zero-dimensional/empty-unit-fiber
case explicit.  The existing `metric_lower_bound_of_compact` remains the
whole-manifold corollary.

Focused verification and the exact module refresh pass.  A local mechanical
style warning was removed without changing the statement or proof route.
