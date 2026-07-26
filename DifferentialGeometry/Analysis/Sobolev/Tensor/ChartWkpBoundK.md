# `ChartWkpBoundK.lean`

## Proved source facts

- `coeffMulJointK` gives the fixed smooth transition-coefficient multiplier
  estimate in `W^{k,p}` for arbitrary finite `k`.
- `secTermJointK` combines that estimate with the canonical arbitrary-order
  cross-chart bound.
- `secTermJointOn` is the required strict-localization variant: its source
  support may lie in the coordinate image of any fixed compact subset of the
  source chart. This is what permits fine-chart middle cutoffs after a local
  heat evolution; no containment in the canonical POU support is assumed.
- Every constant depends only on the fixed background/chart data, tensor
  indices, `k`, and `p`; it is independent of the evolving metric and time
  horizon.

## Verification state

Source written and statically checked.  Lean verification is pending because
the shared named build currently owns the build lane.  No endpoint theorem is
credited from this file until its focused check passes.
