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

## 2026-07-15 finite-jet vanishing producer

`metricDiff_small` specializes the compact local-to-global theorem
`joint_jet_small` to the actual realized metric family.  For every fixed
finite order window it gives one neighborhood of `T` on which all
fixed-background metric-difference covariant jets are uniformly small at every
point of the compact manifold.  The proof uses `metricDiff_joint` and the exact
identity `metricDifferenceCcTensor q q = 0`; it adds no convergence hypothesis
and does not compare whole varying-fibre tensors.

The source is written but verification is pending the in-progress export of
the newly added lower-layer `joint_jet_small` declaration.  Until that focused
check passes, `metricDiff_small` is counted as theorem-level 0% verified and
its dedicated source machinery as about 95%.

This producer is only the first half of the coefficient-smallness step.  The
remaining genuine frontier is to transfer finite metric-difference jet
vanishing through inverse-cometric and connection-difference algebra to
`scalarTraceCoeff` and `connTraceCoeff`, then feed those envelopes to
`app_hs_small`.  The completed all-scale `A₂` operator-norm continuity theorem
and `galLimVel_lift` are still unstated/unproved, hence each remains 0%; their
dedicated machinery is about 70% and 55%, respectively.  The Perelman
noncollapsing endpoint remains 0%.

## 2026-07-15 traced-coefficient vanishing

`metricDiff_small`, `scalarTrace_small`, and `connTrace_small` are now focused
verified.  The latter two pass the jointly smooth realized metric family
through the native cometric-trace and connection-difference producers, apply
the resulting Hom sections to a smooth test section, and only then compare the
fully applied scalar fibre values.  No equality of whole Hom-bundle models,
new consumer hypothesis, or `HasLocallyConstantChartAt` instance is used.

The local failures were normal-form issues rather than a route obstruction:
the jet theorem needed the open regular set as its neighborhood, the cometric
trace declarations live in the nested `DeTurck` namespace, rank `0 + i` had to
remain explicit until elaboration, and the self connection-difference helper
needed the existing namespaced zero theorem followed by multilinear
`map_zero`.  After those repairs the edited file checks without warnings.

Honest accounting: these three producer theorems are 100% proved.  The
all-scale `lapDiffHs_small` and `lapDiffHs_tendsto` theorems are still 0% until
their own downstream file verifies; their dedicated machinery is about 95%.
`galLimVel_lift` is still unstated/unproved (0%), with dedicated machinery about
70%.  The Perelman noncollapsing endpoint remains 0%; whole HCG machinery is
about 57%, with its endpoint theorems at 0%.

## 2026-07-15 joint coefficient API

`scalarTrace_joint` and `connTrace_joint` are now public producer theorems.
Their proofs and assumptions are unchanged: each reconstructs joint
Hom-bundle smoothness from fully applied smooth sections, without asserting a
whole-Hom equality.  This exposes the exact principal and connection
coefficient paths needed for interior time differentiation while keeping the
lower helper `joint0S_sub` private.

Focused verification passes without warnings or `sorry`.  The all-scale
`lapDiffHs_small`/`lapDiffHs_tendsto`, applied compatibility, velocity lift,
and first strong `H^m` derivative are now verified downstream.  Higher time
jets remain a separate theorem-level frontier: their next missing producer is
the jointly smooth fixed-fibre time derivative of a rank-`(r,0)` coefficient
family.  Perelman noncollapsing itself remains unstated and unproved (0%).

## 2026-07-16 reflected-time coefficients

`scalarTrace_rev` and `connTrace_rev` provide the backward-time coefficient
families, and `scalarTrace_rev_on` / `connTrace_rev_on` restrict them to a
consumer slab inside the producer layer. Keeping the restriction here avoids
re-elaborating the realized total-space chart topology in downstream files.

All four producers pass focused and targeted verification. They are **100%**
and close the former fixed-fibre reflected-coefficient frontier. The all-scale
dynamic Laplacian path and `galLimExt_smooth` are now proved downstream;
Perelman noncollapsing remains theorem-level **0%**.

## 2026-07-19 compact-span API exposure

The existing proved producer `metricDiff_joint` is now public.  Its statement,
proof, and assumptions are unchanged; this is the canonical joint-smoothness
input needed by both the original one-slab path and the compact-span replay.
No bundle realization proof was copied into the consumer.

Focused verification passes without warnings or `sorry`.  A targeted module
refresh is in progress so downstream files can read the newly exported name.
The producer itself and its dedicated machinery are theorem-level 100%.
