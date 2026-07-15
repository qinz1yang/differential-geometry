# Scalar flux coefficient jet bounds

## 2026-07-14 compact-slab coefficient source

`scalarFlux_eq_slot` identifies the scalar divergence-form coefficient exactly
with the existing inverse-cometric difference inserted in the unique covector
slot.  `scalarFlux_jet_grid` then transfers the existing pointwise
antidiagonal-grid jet estimate to `scalarFluxCoeff`; no parallel coefficient
model or new consumer assumption is introduced.

`metricDiff_slab` now fixes one positive backward-time slab, preserves the
regular-time fact, supplies quarter-size fibre smallness, and gives one
pointwise `iteratedCovGrad` envelope for every metric-difference jet.  For

```lean
q := G.metric T
P t := metricDifferenceCcTensor q (G.metric t)
```

joint smoothness is converted by the public `joint_to02` producer and compacted
by `joint_jet_bdd`.  `scalarFlux_slab` applies the inverse-cometric product-grid
estimate to that same data and returns a time- and point-uniform jet envelope.

The formerly missing product-base conversion is therefore closed.  No
`HasLocallyConstantChartAt`, consumer-supplied convergence bound, parallel
coefficient model, or equality of whole Hom-bundle coordinates was added.

Focused verification now passes without warnings.  The apparent missing-name
failures were stale import-boundary problems: the file now imports the native
metric coefficient and realized Gram-difference producers directly.

The remaining dependent-fibre issue was not solved with a pullback
`smul_section`: that theorem uses its domain as the bundle base, whereas this
family has domain `M × ℝ` and fibre over `p.1`.  Instead, `metricDiff_eval`
fully evaluates the moving-minus-fixed metric on two smooth vector sections,
proves the resulting real-valued function jointly smooth, and
`contMDiffOn_clm_section_of_pointwise_jointMR` reconstructs only the needed
operator field.  The rank-zero input is normalized after application by
`metricDiff_apply`.  Thus verification does not elaborate equality of whole
Hom-bundle coordinates.

## Honest progress

- Perelman noncollapsing endpoint theorem: not stated or proved here, 0%.
- The genuine `H² →L L²` operator estimate is already complete in
  `MetricLapDiffTime`; the new finite-Galerkin uniform closure is a separate
  theorem and remains unverified in `ScalarNonautUniform`.
- Dedicated compact-slab scalar coefficient machinery in this file: 100%
  verified.  This is infrastructure, not endpoint completion.
- The downstream `scalar_crit_tame` theorem is source-written but remains 0%
  complete pending its own verification; its dedicated machinery is about 98%.
- Perelman no-local-collapsing and `ham3_noncollapse` remain theorem-level 0%;
  their dedicated analytic machinery is about 44%.  Whole HCG machinery is
  about 54%, with its endpoint theorems at 0%.
