# NoncollapseInjectivity

## State — 2026-07-09

The canonical HCG bridge now separates data from proofs:

- `FlowBaseVolData` stores time-zero membership, a positive `kappa`, and a
  positive radius;
- `IsFlowBaseVolBound` proves that the actual basepoint flow balls have
  backward-parabolic curvature control and genuine Riemannian-volume lower
  bounds;
- `flowInj_of_vol` produces the `FlowBaseInjBound` consumed by Hamilton
  compactness.

The ball constructor and both input packages check.  `flowInj_of_vol` is the
single remaining `sorry`: it is the genuine Cheeger–Gromov–Taylor
volume-plus-curvature-to-injectivity theorem, not local record plumbing.

Dedicated data/realization machinery is about 20%; the bridge theorem itself is
0%.  The next prerequisite is an actual Hamilton rescaled `PointedFlowSeq`, not
another numeric compatibility record.

Hamilton's local Section 12 package now constructs genuine `paraSolution`
rescalings and genuine time-zero `FlowMetricBall`s.  What remains is to collect
that sequence on a common time window and realize it as the `PointedFlowSeq`
consumed here.  Including that Hamilton-side migration, the dedicated
noncollapse data/realization machinery is about 40%; `flowInj_of_vol` remains
0%.
