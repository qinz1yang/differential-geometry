# CompactChartJetBound

## 2026-07-16: generic compact raw-component jet bound

Added `rawPullR_jet_le`.  On any compact subset of a chart target it bounds a
fixed raw chart-component jet by one sufficiently high intrinsic `toHs` norm,
uniformly in the smooth tensor and with arbitrary tensor valence.

The successful route was compact reverse order-peeling, a compact uniform
raw-component-to-fibre comparison, and the unconditional pointwise Sobolev
embedding.  Keeping the conclusion fully applied avoids Hom-bundle model
equalities and the associated normalization cost.

Focused verification passed.  The two pre-existing unused-section-variable
warnings in this file were removed mechanically.  This producer is complete
(theorem 100%, dedicated machinery 100%).  Its current consumer frontier is
the scalar eigensection chart-jet estimate.

