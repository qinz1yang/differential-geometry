# Intrinsic metric-jet control

## Current result

- `metricJet2_intrinsic` now controls the chart metric 2-jet difference by the
  intrinsic background-covariant tensor jet through order 2. This is the
  correct input for the zero-order Ricci--DeTurck RHS difference.
- The private Gram-component estimates were parameterized by the requested jet
  order. The existing public 3-jet theorem and its hypotheses are unchanged.
- Focused verification passes without local warnings or sorries.

## Route and frontier

The lower-order theorem reuses the existing Gram-to-raw-chart,
raw-chart-to-Euclidean, and Euclidean-to-fiber bridges at order 2. No new
analytic assumption is introduced.

The next frontier is not another metric-jet bridge. It is the first covariant
derivative of the Ricci--DeTurck remainder after exact cancellation of the
fixed background connection Laplacian: its top third-jet term must carry the
small H2 principal-coefficient deviation, while the remaining terms may use
the uniform C3 `LowRegCoeff` bound.

## Honest accounting

- `metricJet2_intrinsic`: theorem 100%.
- Mixed H3-to-H1 remainder theorem: not yet stated/proved, 0%; dedicated
  coefficient and product machinery is approximately 55%.
- Uniform low-regularity Ricci--DeTurck existence theorem: not yet stated/proved,
  0%.
- Whole HCG compactness machinery remains approximately 57%; its endpoint
  compactness theorems remain 0% until stated and proved.
