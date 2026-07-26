# Metric-family connection difference

## 2026-07-15 scalar-coordinate route

`connDiff_joint` targets the genuine connection-difference `(1,2)`-tensor for an arbitrary
`RealizedMetricFamilyOn` satisfying `MetricFamilySmoothOn`, against a fixed smooth background
metric.  The proof reuses the public `christ_of_family` chart-Christoffel producer.

The Hom-bundle statement is reconstructed with
`contMDiffOn_clm_section_of_pointwise_jointMR`, but no equality of whole Hom models is used.
After applying the Hom to a smooth covector, the rank-two output is reconstructed from scalar
chart coordinates.  Each scalar coordinate is a finite sum of moving-minus-fixed Christoffel
components paired with the covector on one chart-basis vector.  The connection-difference chart
formula is rewritten only after all tensor inputs have been supplied.

No global frame, chart selector, `HasLocallyConstantChartAt`, or new consumer assumption is
introduced.  After the upstream family producers were exported, the source passed focused
verification without warnings and its module export also passed.  `connDiff_joint` is
theorem-level 100% complete, and its
dedicated scalar-coordinate reconstruction machinery is 100% complete.

This producer is one connection arm of the finite coefficient-jet smallness step.  The all-scale
moving-Laplacian continuity theorem remains unstated and therefore theorem-level 0%; its broader
dedicated machinery is about 70%.  The Perelman noncollapsing endpoint remains theorem-level 0%.
