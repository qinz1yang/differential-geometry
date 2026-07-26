# ManifoldLimitWkp

## 2026-07-19: finite cross-chart assembly

### Implemented

- `pullback_eq_chart` identifies the measurable pullback used by
  `manifoldLimitFun` with the chart pullback consumed by the cross-chart
  estimates.
- `limitFun_memWkp` proves that the existing finite POU assembly
  `manifoldLimitFun` lies in `MemWkpChart g k p`.
- For each target/source chart pair it applies `crossChartAeJoint` to
  `chartLimit_memWkp` and `chartLimit_ae_zero`; the source kernel is the compact
  `tsupport` of the canonical POU member.
- The per-pair terms are combined by finite induction using `MemWkp.add`, and
  `chartPushed` linearity is discharged pointwise.
- No existing definition was changed, and no global class, instance, or
  notation, axiom, `sorry`, or `admit` was introduced; `EuclN` is only a
  file-local notation.

### Verification and project state

- Source implementation: complete.
- Focused Lean verification: pending because this lane was explicitly
  source-only while another named build owned the shared verification slot.
- This closes the source-level membership part of manifold chart-Sobolev
  completeness.  The downstream convergence and non-instance completeness
  packaging are now implemented source-only in `ManifoldLimitConv.lean`; their
  focused Lean verification is still pending.
- `ricci_flow_unif_existence`: still 0%.  The generic spatial `W^{k,p}`
  infrastructure has advanced, but no maximal-regularity time solver or exact
  endpoint theorem has yet been proved.
