# ContractedBianchi.lean — notes

## 2026-07-16 scalar bridge

Status: focused verification passed, with no new warnings or `sorry`.

- Added `metricScalar_eq_scal`:
  `metricScalarAt g x = scalarCurv g x`.
- The proof expands the canonical metric trace in the model basis, rewrites each
  `metricRicciAt` component with `metricRicciAt_apply_eq_ricciTensor`, and then
  uses `orthonormal_basis_bilin_trace` plus
  `scalarCurv_eq_orthonormal_trace`.
- The theorem lives beside `scalarCurv` in `ContractedBianchi.lean`.  This keeps
  the dependency direction correct: the Bianchi layer imports the lower
  `MetricLeviCivitaReconcile` bridge, rather than making the reconcile layer
  depend on the full Bianchi/Bochner stack.
- No `HasLocallyConstantChartAt` or consumer-supplied geometry hypothesis was
  added.  All equalities are scalar-valued; no dependent tensor or Hom equality
  is introduced.

Honest progress: this scalar representation bridge is complete (100%).  It is a
small adapter for the weighted W-entropy route; the weighted Hessian split and W
monotonicity theorems are not proved by this change (0% as endpoint theorems),
and Perelman noncollapsing remains 0% as an endpoint.  The broader dedicated
entropy machinery remains roughly 65–70%, while the whole HCG compactness
program remains roughly 60%.
