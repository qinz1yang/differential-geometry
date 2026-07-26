# StepB1Inverse

## Status

The canonical framed-coordinate source migration is complete.  Focused Lean
verification passes against the exact-current MetricLocal and StageInjectivity
artifacts, and this module's own exact refresh also completes successfully.

The source now uses `framedChartAt` for every fixed source/target chart in
`HasStageJetData.inv_chart_conv` and `HasStageJetData.inv_chart_tail`.
Normal-chart source and target membership is expressed through
`framedExpDiffeo` and the intrinsic `expRadiusGp` ball. The only remaining raw
radius operations are the canonical implementation bridge from framed
`expRadiusGp` smallness through `normalFrame_sqrt` to the underlying raw
exponential source; no raw chart or raw-radius premise remains in the public
inverse theorems.

The proof architecture and public theorem names are unchanged:

- `exists_inv_seq` packages each sufficiently late forward chart map as a
  partial diffeomorphism, applies the moving-inverse theorem, and identifies
  its selected inverse with the actual `Function.invFunOn` readout by the
  existing checked left-inverse relation.
- `HasStageJetData.inv_chart_conv` gives compact-open smooth convergence of the
  exact inverse along each cofinal source/target pair.
- `HasStageJetData.inv_chart_tail` performs the bad-pair uniformization and
  gives one rectangular two-stage jet tail on a fixed compact target core.

The reverse finite-stage comparison map remains only an approximate-return
tool in the separate global-injectivity producer. No equality between that map
and the exact inverse is asserted.

## Radius ledger

The fixed coordinate domains now use the framed `normalBall`, whose radius is
`expRadiusGp`. The source coordinate core lies in the closed radius-`S` source
ball. The exact inverse is `Function.invFunOn` on the open radius-`T` ball, with
`S < T`. Global injectivity is supplied on a larger radius `Vrad`, with the
existing return-map buffer between `T` and `Vrad`, and `Vrad < r`. No
endpoint-radius assumption was added.

## Remaining frontier

Both focused and exact gates are now green; the reverse-metric consumer may
read the current canonical export.

The later B1 frontier remains chain-wide framed revalidation and packaging of
the already implemented intrinsic forward/reverse metric estimates into the
unchanged `StepB1RawInput`. This file introduces no new analytic frontier.

## Honest accounting

- `HasStageJetData.inv_chart_conv`: canonical framed source/focused complete.
- `HasStageJetData.inv_chart_tail`: canonical framed source/focused complete.
- Exact-local-inverse framed migration in this file: 100% current module
  verification.
- `MetricCompactBase.exists_b1_raw`: complete live proof body, but not yet
  framed-green until its full producer chain is migrated and revalidated.
- Dedicated Step-B/B1 machinery: about 95%; Chapter 4 machinery: about 87%;
  whole HCG machinery: about 60%.
- Textbook Step B1 and unconditional compactness endpoints: theorem-level 0%.
