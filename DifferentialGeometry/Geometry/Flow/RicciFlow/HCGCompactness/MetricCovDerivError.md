# MetricCovDerivError

`t02Norm_metricDiff` identifies the positive-order
`tensor02CovDerivNormWith` of a realizing metric tensor field with the
corresponding `metricDerivNorm`.  The proof uses the common `iterCov` norm
readout and metric compatibility of the background metric.

`metricError_eq_zero` identifies the order-zero `metricTensorErrorNorm` with
the same metric-difference seminorm.  Together with `t02Norm_metricDiff`, this
gives the carrier consumer one uniform readout split only by `a = 0` versus
`1 <= a`.

`PreApproxIsoDataOn.of_metric` is the localized carrier constructor needed by
the actual Step-B1 collar argument.  It accepts the pullback formula only on
the controlled set, together with `metricDerivNorm` bounds through order `p`;
it therefore avoids the stronger and false-for-this-use global pullback premise
of `preApproxIsoDataOn_of_bounds`.

`sqrt_norm_le_comp` packages the other generic estimate needed by the B1
consumer: a uniform component bound in an orthonormal basis for a reference
metric, followed by pointwise metric equivalence, controls the intrinsic
covariant-tensor norm.

This is a generic carrier-side bridge for Step B1.  It does not add a metric
compactness input or complete either of the two remaining raw Step-B1 fields.

Focused verification and the targeted module refresh are green and sorry-free.
These close the generic carrier identities, localized constructor, and
component-to-norm inequality; the live frontier is now the local normal-chart
realization supplying their hypotheses.
