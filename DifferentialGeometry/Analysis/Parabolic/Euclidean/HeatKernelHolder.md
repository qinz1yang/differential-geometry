# HeatKernelHolder

## Status

Source complete. The focused Lean check passes with no local warnings.

## Mathematical content

- `integral_holder` is the Banach-valued spatial Hölder inequality for a
  scalar kernel paired with a vector field.
- `heatShift_memLp` proves that the translated-reflected positive-time heat
  kernel lies in every real `L^p`, `p > 0`.
- `heatConv_holder` combines these with `heatPow_shift`, so the kernel factor
  is exactly

  `t^(n(1-p)/2) * basePowMass(V,p)`

  raised to `1/p`.

This is the spatial atom of the late ordinary-source value estimate. It does
not yet turn a `KLSource0` late cylinder bound into a global source-slice
bound, sum spatial shells, or perform the terminal-time integration.

The endpoint `ricci_flow_forward_unique` remains 0%.
