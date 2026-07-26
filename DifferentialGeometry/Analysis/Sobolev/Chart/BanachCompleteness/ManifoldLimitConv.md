# ManifoldLimitConv

## 2026-07-19: finite cross-chart convergence and completeness

### Source implementation

- `chartErr` is the difference between the chart-pushed iterate and the chosen
  Euclidean chart limit.
- `chartErr_mem` and `chartErr_ae_zero` give exactly the Sobolev membership and
  fixed a.e.-compact-support hypotheses consumed by `crossChartAeJoint`.
- `limitFun_decomp` rewrites the manifold error as a finite sum of pulled-back
  source-chart errors.
- `limitFun_tendsto` chooses one fixed constant for every source/target chart
  pair, bounds the global chart norm by a finite double sum, and proves that
  sum tends to zero using `chartLimit_tendsto`.
- `wkpChart_complete` returns a `CompleteSpace (WkpChart ...)` structure as an
  ordinary theorem value.  `wkpQuot_complete` transports it to
  `WkpChartQuot`.  Neither declaration installs a global instance.
- No global class, instance, or notation, axiom, `sorry`, or `admit` was
  introduced; `EuclN` is only a file-local notation.

### Canonical APIs reused

- `wkpChartFun_eq_finset_sum_pullback` for the per-iterate POU decomposition;
- `wkpNormChart_finset_sum_le` and `wkpNormChart_eq_finset_sum` for the two
  finite-sum norm reductions;
- `crossChartAeJoint` for arbitrary-order pairwise membership and norm bounds;
- `chartLimit_tendsto` for each source-chart error;
- `Metric.complete_of_cauchySeq_tendsto` and
  `SeparationQuotient.completeSpace_iff` for non-instance packaging.

### Verification and project state

- Source implementation: complete; the Lean file is below 500 lines.
- Focused Lean verification: pending because this lane remains explicitly
  source-only while another named build owns the shared verification slot.
- Static elaboration risks are the finite-sum rewrite in `limitFun_decomp`,
  reducibility of the local `S`, `ρ`, and `term` abbreviations in the double
  norm bound, and the final `ENNReal.toReal` conversion in
  `wkpChart_complete`.
- `ricci_flow_unif_existence`: still 0%.  This closes the source-level generic
  spatial `W^{k,p}` completeness route, but does not yet construct the uniform
  maximal-regularity time solver required by the endpoint.
- `ricci_flow_forward_unique`: still 0%; this file does not address the gauge
  or uniqueness route.
