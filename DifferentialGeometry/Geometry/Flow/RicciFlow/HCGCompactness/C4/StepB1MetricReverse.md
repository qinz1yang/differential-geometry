# StepB1MetricReverse

## Role

This file is the coordinate-level reverse metric producer for Step B1.  It
uses the exact `Function.invFunOn` of the forward stage comparison map; the
opposite-direction comparison map remains only an approximate return map for
injectivity and is never identified with the exact inverse.

## Current source status

The source migration of `HasStageJetData.inv_cov_comp_tail` to canonical framed
normal charts is complete.  Every fixed-center source and target chart in the
statement and proof now uses `NormalCoordinates.framedChartAt`.  The theorem
still gives the same rectangular `k,l` tail, basis-parametric finite
covariant-component tower, and evaluation on the actual moving target image of
the buffered source cover.  Its exact `Function.invFunOn` semantics, theorem
name, quantifiers, and analytic proof structure are unchanged.

The canonical-coordinate source passes focused Lean verification against the
exact-current inverse artifact, with no local diagnostics.  This module's own
exact refresh also completes successfully.

The first API gap was that `inv_chart_conv` hid the eventual smoothness of its
exact inverse charts even though its moving-inverse construction already proves
it.  The upstream theorem now exposes that conclusion in its output, with no
new assumption or radius field.

The source/target roles are explicit: the exact inverse pulls back the
source-stage metric, while the target-stage metric supplies the background
Christoffel coefficients and subtracted metric.  The reverse finite-stage
comparison map is not used or identified with the exact inverse.

## Remaining frontier

This theorem remains coordinate-level.  Its focused and exact gates are green.
The downstream intrinsic
bridge turns the finite component bounds into the reverse
`tensor02CovDerivNormWith`/`metricDerivNorm` tail on the local pullback-field
carrier.

The proof body of `MetricCompactBase.exists_b1_raw` is complete, but its live
framed import chain is not yet green.  It must not be reported as a checked
producer until this file and the rest of that chain have been revalidated.

## Accounting

- `inv_cov_comp_tail` proof body: canonical framed source/focused complete.
- Dedicated reverse coordinate machinery: 100% current module verification.
- `MetricCompactBase.exists_b1_raw` proof body: complete (100% source
  implementation); live framed chain verification remains 0% pending.
- `StepB1RawInput` producer under live framed semantics: proof body complete,
  but not yet framed-green.
- Textbook Step B1: 0%.
