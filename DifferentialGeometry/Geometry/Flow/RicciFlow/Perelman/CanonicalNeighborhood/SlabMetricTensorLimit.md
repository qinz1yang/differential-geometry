# SlabMetricTensorLimit

FINAL ACCEPTANCE 2026-09-10 00:40UTC: landed in scoped local commit82d2a5ff7.
Saved EMPTY check, named lint build and fresh standard-only public axiom audit
all passed for the current source. The ordinary source claim is released.
Reproducible hashes and receipts: E:/lean-tools/chapter25-terminal-local-20260909/slab-equation-completion.json.
The dated notes below retain the proof route and iteration evidence.

2026-09-10 00:24UTC: independent saved-file check115 passed with empty compiler
diagnostics (24.47s); named refresh115 passed (31.77s), replaying only the two
known Chapter25Convergence warnings. Fresh stable-batch public axiom audit is
still pending. Ordinary claim 5c59823c retained in the granted Chapter25 window.

Target: the actual `MetricFamilySmoothOn.metricTensor_cont` field, including the
whole closed time window. Fixed-point coefficient continuity alone does not
imply this joint bundle-section statement.

Use native PartialDiffeomorph.continuous_mfderiv_apply and the source flow's
metricTensor_cont.eval_continuous to prove continuity of actual mapped quadratic
coefficients on a compact space-time product. One fixed approximant at tolerance
1/2 bounds the limit on that product; arbitrarily small comparisons give uniform
convergence. Polarization handles two local smooth vector fields. Native
metricTensorCont_of_chartGram reconstructs the bundle section from chart-frame
components using compact neighborhoods inside the chart's actual base set.

No limit metric time regularity is assumed. This does not prove joint higher
spatial jets or full smoothness, nor scalarTime or curvature tensor continuity.
Do not import an IsSolutionOn consumer to construct those missing fields.

Elaboration lesson: the final ContinuousOn.comp with an untyped source set
unfolded the metric inner product about494000 times and exhausted200000
heartbeats. An explicitly typed restriction map, ContinuousOn domain and MapsTo
proof resolve it under the default limit. The compact Gram bridge is simply
`exact hc`, since chartGramMatrix_apply is definitional. Use the fully qualified
DifferentialGeometry.PartialDiffeomorph.continuous_mfderiv_apply; field notation
does not find this namespace. For dependent source metric evaluation use the
ground metricTensorField_apply equality via Continuous.congr, not broad simp.
