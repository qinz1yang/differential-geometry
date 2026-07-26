# RawIntrinsicC2

## Role

This module owns the compatibility between the chart-fixed exponential and the
complete intrinsic exponential on the named `expMapC2Radius` ball.  It is the
lower bridge required by raw radial Jacobi consumers; it is not a comparison or
HCG assumption.

## Current route

- `exp_eq_intr_of_c2` propagates the existing time-zero agreement germ along
  the open radial segment by moving-chart geodesic uniqueness, then uses
  continuity at time one.
- `exp_germ_eq_intr` applies the pointwise theorem throughout the open C2 ball.

No smaller independent agreement radius is introduced.

## Verification

The source is focused-green with no diagnostics, and its exact target artifact
is current.

## Accounting

- This compatibility brick: theorem and dedicated machinery 100%.
- `radialLap_eq_mean`: theorem and dedicated source machinery 100%;
  focused/exact-green in its owning module.
- Route B-prime cutoff machinery: about 50%.
- Whole HCG supporting machinery: about 60%.
- Unconditional `compactnessSol`: theorem 0%.
