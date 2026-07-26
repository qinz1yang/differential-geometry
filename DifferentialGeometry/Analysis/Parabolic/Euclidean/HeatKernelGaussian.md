# HeatKernelGaussian

## Source boundary

`HeatKernelGaussian.lean` adds the pointwise estimates needed by the
early-time Carleson heat-potential argument:

- `baseHeat_le`: the normalized time-one Gaussian is bounded by the inverse
  normalizing mass;
- `baseHeat_decay`: outside radius `R` it gains `exp(-R^2/4)`;
- `baseD1Maj_decay`, `baseD2Maj_decay`: the same Gaussian gain for the
  derivative majorants, retaining a supplied upper scaled-radius bound;
- `heatKernel_le`: the time-`t` kernel has the expected `sqrt(t)^(-n)` scale;
- `heatKernel_half`: on `0 <= s <= t / 2`, the kernel at time `t - s` is
  bounded at the single spatial scale `sqrt(t / 2)`;
- `heatKernel_decay`: at distance at least `R sqrt(t)` it has the same scale
  times `exp(-R^2/4)`;
- `heatKernel_early`: combines the previous two estimates on the early
  Duhamel half, measuring both prefactor and annulus radius at the fixed
  observation-time scale;
- `earlyScaled_lo`, `earlyScaled_hi`: comparison of observation-scale shell
  radii with the running heat scale on the early half;
- `heatD1Maj_early`: the analogous early-half first-derivative majorant with
  shell-provided lower and upper scaled-radius bounds.

These are direct theorems about the repository's actual Euclidean heat kernel,
not assumptions on a future parametrix.

## Verification and next step

Focused Lean check passes with no warnings (2026-07-19), and the targeted
module export completed for its immediate downstream users.  The repair
supplied the nonnegativity facts required by the early first-derivative
majorant and made the square-root scale rewrite local, without changing any
public estimate.  The file contains no `sorry`, `admit`, axiom, opaque
declaration, or heartbeat override.

Those Gaussian bounds are now consumed by `HeatEarlyNear.lean` and
`HeatEarlyGlobal.lean`.  This remains only the pointwise Gaussian layer; the
full Koch--Lamm `Y_T → X_T` linear estimate still additionally needs the late
value and the local/late gradient arms.  The endpoint
`ricci_flow_forward_unique` remains 0%.
