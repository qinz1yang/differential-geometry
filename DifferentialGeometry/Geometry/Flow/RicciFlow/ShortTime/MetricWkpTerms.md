# MetricWkpTerms

## Scope

This file isolates the fixed-atlas part of the uniform initial-data argument
from the still-blocked tensor-space assembly.

`metricDiff_fam_jet` proves one pointwise Frechet-jet bound, through order
three, for every POU-weighted scalar component of every fixed-background
metric difference in the family.  The constant is independent of the family
index, chart, and tensor component.

`metricDiff_wkp_terms` applies `wkp_bdd_of_jet` chart by chart.  For each chart
it returns a finite `ENNReal` bound shared by the whole metric family and all
covariant two-tensor components, together with `MemWkp 3 p` membership.

The proof uses only the already-exported chart-locality, intrinsic metric-jet,
compact-support, and Euclidean compact-jet APIs.  It does not import the
stale-claimed `ChartWkp` or fine-tensor quotient files.

## Verification state

Source implementation is complete.  Focused verification is pending.

No endpoint theorem is claimed here.  `ricci_flow_unif_existence` remains 0%
until the exact theorem is proved and verified.
