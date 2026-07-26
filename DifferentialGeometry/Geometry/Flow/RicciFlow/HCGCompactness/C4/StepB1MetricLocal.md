# StepB1MetricLocal status

## 2026-07-18: canonical framed-coordinate source migration

Status: source migration, focused Lean verification, and the exact module
refresh are complete on the canonical framed chain.

- Every fixed-center chart in `source_stay`, `pb_buf_tail`, and
  `pb_local_tail` now uses `framedChartAt`.
- The source-target entry proof in `source_stay` now consumes the intrinsic
  `expRadiusGp` ball supplied by `HasSuppConvData.geom_on` and enters the
  framed exponential source using `framedExp_source`, `normalFrame_sqrt`, and
  the existing intrinsic-to-raw kernel bridge.  No raw-radius hypothesis or
  endpoint radius input was added.
- Public theorem names and assumptions are unchanged.  The remaining
  `expMapC2Radius` spelling occurs only inside the established low-level bridge
  theorem that proves membership in the raw exponential kernel after applying
  the orthonormal frame; it is not a public radius seam.

Focused verification exposed only three missing namespace qualifications in
the local source-membership bridge.  Qualifying `framedExpDiffeo`,
`framedExp_source`, and `normalFrame_sqrt` through `NormalCoordinates` closed
the file without changing any theorem statement or geometric argument.

## 2026-07-16: buffered moving-source coefficient tail

Status: focused verification passed, with no `sorry`, `admit`, or warnings.

This file closes the moving-source localization layer between
`StepB1MetricBridge` and the later intrinsic metric-error bridge.

- `HasSuppConvData.source_stay` converts a convergent sequence of coordinate
  centers with one fixed closed-ball buffer and source membership at radius
  `R` into fixed neighborhoods `V ⊂⊂ W ⊂ interior C0`.  The corresponding
  inverse normal charts eventually map `W` into every prescribed larger
  source ball of radius `S`, for `R < S`.
- `HasStageJetData.pb_buf_tail` uses a bad-sequence argument, compactness of
  `C0`, `source_stay`, and `HasStageJetData.pb_conv`.  For one fixed live source
  chart and positive buffer radius, it gives a single rectangular `(k,l)` tail
  for all derivative orders `j ≤ p`.  Its conclusion compares the actual
  target-stage normal metric pulled back by the actual stage comparison map
  directly with the source-stage normal metric.
- `HasStageJetData.pb_local_tail` consumes the producer-owned `buffer_cover`,
  applies `pb_buf_tail` once per live source chart, and takes a finite maximum
  of their thresholds.  Every point of the smaller source ball therefore has a
  buffered source-chart witness satisfying the coefficient estimate on one
  common two-stage tail.

The theorem is intentionally not stated for every arbitrary point of
`interior C0`.  A bad sequence of such points may approach the boundary, so
the fixed `V ⊂⊂ W` required by `pb_conv` need not exist.  The retained
closed-ball buffer is exactly the honest premise produced by `buffer_cover`;
no stage-family stay assumption or new compactness-input field was added.

## Remaining frontier and accounting

The canonical framed moving-source coefficient proof is focused- and
exact-green.
The chart-coefficient to intrinsic `tensor02CovDerivNormWith` conversion and
the corresponding exact-local-inverse estimate now have complete live proof
bodies in downstream modules.  They are not new analytic frontiers; their
canonical framed consumer files still require migration and revalidation.

- `exists_b1_raw` has a proof body, but its framed dependency chain has not yet
  been reverified green.  Its source implementation is complete, but it must
  not yet be reported as framed-green.
- Dedicated B1 machinery: approximately 95%.
- Chapter 4 machinery: approximately 87%.
- Whole HCG machinery: approximately 60%.
- Textbook B1 and unconditional compactness endpoints: 0%.
