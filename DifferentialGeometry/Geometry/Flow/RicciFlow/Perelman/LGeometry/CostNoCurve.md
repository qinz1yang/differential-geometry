# CostNoCurve

## Goal

Handle the disconnected endpoint branch for chart-local L-cost estimates: if
the chart center cannot be reached by a global regularized `C¹` curve, then a
small convex chart ball is also unreachable, the raw L-cost is the empty
infimum `0`, and the chart-coordinate cost is Lipschitz there with constant
zero.

## Route

- Join two intervalwise `C¹` pieces through the existing finite-chart H1
  realization and action-density machinery.
- Compress a global competitor into the first half of the interval and use an
  inverse-chart affine segment on the second half to move its endpoint inside
  a convex chart set.
- Apply the move construction contrapositively on a chart ball.
- Identify the empty raw competitor set and use `Real.sInf_empty`.

No reference-tree result or parallel endpoint-comparison wrapper is used.

## Verified result

Focused verification passed without warnings, and the targeted module artifact
was refreshed successfully.  Static inspection found no `sorry`, `admit`,
axiom, frontier hypothesis, reference-tree dependency, or import cycle through
`CostChartLip`.

The checked public chain is:

- `exists_lC1_join`: globalizes two intervalwise `C¹` pieces while preserving
  the outer endpoints;
- `exists_lC1_move`: moves a reachable endpoint inside a convex canonical-chart
  set;
- `lCost_zero_no_curve`: evaluates the empty raw competitor infimum;
- `lNoCurve_nhds`: propagates non-reachability to a small chart ball;
- `lCost_zero_lip`: gives the zero Lipschitz constant on that ball.

## Progress and scope

This disconnected-branch theorem family: 100%; its dedicated join/move and
empty-infimum machinery: 100%.  The downstream `CostChartLip` assembly theorem
remains outside this file and is 0% here because that file is owned by another
lane.  This closes roughly 5% of fixed-manifold L-cost chart regularity and
remains below 1% of the full Perelman reduced-geometry program.
