# Metric covariant-derivative arity bridge

## 2026-07-09

Added `diffNorm_zero_change`, the order-zero reference-metric comparison for
`metricDerivNorm`. It is the direct covariant two-tensor specialization of
`Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv` and introduces no new geometric assumptions.

Focused verification and the targeted producer build passed without warnings or new `sorry`.
