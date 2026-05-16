# MetricCompatibility

## 2026-05-16 metric-compatible inverse components

- Added a RicciFlow-independent local-frame component layer for metric
  compatibility.
- Worked: exposed `metricCompForMetricInFrame_extDerivFun_eq_christoffel` and
  `inverseMetricCovDerivForMetricCompInFrame_eq_zero`, the arbitrary-smooth-
  metric version of `nabla gInv = 0`.
- This is the reusable component API needed to compute derivatives of
  inverse-metric contractions such as the `(0,2)` tensor inner product.
- Verification passed for the time-free component setting.

## 2026-05-16 along-direction inverse metric compatibility

- Added `inverseMetricCovDerivForMetricCompAlongInFrame` and proved
  `inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero` for an arbitrary
  smooth direction section.
- The proof repeats the inverse-metric differentiation argument directly with
  `christoffelAlongInFrame`, avoiding a separate linearity frontier for
  expanding the direction in a frame.
- This is now the preferred reusable component API for differentiating
  inverse-metric contractions along non-frame directions.

## 2026-05-16 fixed-chart inverse metric API

- Added the fixed-chart metric flat map and inverse-metric component API:
  `metricFlatModelInChart`, `inverseMetricFlatModelInChart_component`, their
  center identities, smoothness of the inverse components, center symmetry, and
  the center `MetricInverseInBasis` theorem.
- Verification passed for this coordinate metric layer.
- The next tensor theorem still needs a localized version of inverse-metric
  compatibility on the coordinate-frame base set. The current
  `inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero` assumes the inverse
  relation globally in `M -> Idx -> Idx -> Real`, while fixed-chart inverse
  metric components only satisfy it on the local frame neighborhood.
