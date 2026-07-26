# KochLammFluxScale

## Proved

- `klFluxCore_scale`: the terminal first-derivative majorant power mass at
  time `R^2` extracts `klLpScaleR R ^ klPDual V` exactly.
- `klFluxRoot_scale` and `klFluxNorm_scale`: taking the Hölder-dual root
  leaves precisely `klLpScaleR R = R^(2/(n+4))`, with a dimension-only
  constant.

This is the required kernel-side cancellation factor for
`KLSource1.late_lp`; no coarse non-small derivative estimate is used.

## Frontier

The next producer restricts this global terminal slab estimate to one late
cylinder, pairs it with `KLSource1.late_lp`, and cancels the two radius
factors.  Neither endpoint theorem is yet proved, so both remain `0%`.
