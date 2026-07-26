# StepB1MetricIntrinsic

## Status

The canonical fixed-center framed migration is source-complete; focused Lean
verification and the exact module refresh both pass.

`HasStageJetData.cov_comp_tail`, `HasStageJetData.fwd_norm_tail`, and
`HasStageJetData.inv_norm_tail` now use `framedChartAt`, `framedExpDiffeo`, and
`expRadiusGp` at every fixed center.  The private `quarterPull_inner`,
`quarter_norm_eq`, and `stagePull_coeff` seams use the same framed exponential.
The only remaining raw tangent-fiber exponential API calls are implementation
kernel bridges behind `framedExp_source`; `normalFrame_sqrt` supplies the exact
metric-isometry conversion before invoking those raw source lemmas.

The reverse theorem still uses the exact `Function.invFunOn` obtained from the
local partial diffeomorphism, not the opposite-direction stage comparison map.
The radius hierarchy, pullback tensor/covariant-derivative architecture, theorem
names, and assumptions are unchanged.

## Proof architecture

The local argument is a bad-pair/compact-subsequence contradiction.  On the
compact coordinate patch, `pb_conv` gives smooth convergence of the actual
pullback coefficients while the retained normal-metric family converges to the
same coercive limit.  The actual pullback family is smooth on an eventual tail;
its finite prefix is totalized by the smooth limit metric before applying
`metric_tower_conv`.

The latter theorem controls the complete Pi-valued component tower.  Its
order-zero norm therefore controls a varying component slot directly; no slot
subsequence or slotwise stabilization is needed.  A finite maximum over
`Fin (p + 1)` and then over the live source charts gives the common rectangular
tail.  The framed migration changes only the fixed-center coordinate
identifications and their radius/source witnesses.

## Remaining frontier and accounting

The source migration and exact verification in this file are complete.  The
only local proof repair was to unpack the `normalBall` open-set membership
explicitly before rewriting with `Metric.mem_ball`; no assumption, statement,
or analytic route changed.

- `cov_comp_tail`, `fwd_norm_tail`, and `inv_norm_tail`: canonical framed
  source/focused/exact complete.
- This file's fixed-center migration: 100% and exact-green.
- Concrete `StepB1RawInput`: downstream proof body remains source-complete at
  5/5 fields, but it is not framed-green until this module and the exact
  downstream chain are revalidated.
- `MetricCompactBase.exists_b1_raw`: proof body complete, but not framed-green;
  do not count the live framed theorem as checked yet.
- The selected B/C raw-producer chain and conditional Theorem 3.9 remain
  source-assembled but not framed-green; their live-route checked status stays
  at 0% until the ordered exact revalidation reaches them.
- Separately named textbook B1 theorem: unstated, 0%.
- Dedicated Step-B/B1 machinery: approximately 95%; Chapter 4 machinery:
  approximately 87%; whole-HCG machinery: approximately 60%.  Unconditional
  compactness endpoints remain theorem-level 0%.
