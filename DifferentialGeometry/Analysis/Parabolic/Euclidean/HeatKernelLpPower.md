# HeatKernelLpPower

## Verified producer

This file computes the exact spatial integral of every positive real power of
the normalized Euclidean heat kernel.  The exported chain is:

- `baseHeat_pow`, `baseHeatPow_mem`, and `baseHeatPow_int` for the time-one
  Gaussian;
- `heatKernel_pow`, `heatKernelPow_mem`, and `heatKernelPow_int` after the
  parabolic dilation; and
- `heatPow_scale` and `heatPow_int_eq`, which collapse the dilation factor to
  the single time power `t^(n*(1-p)/2)`; and
- `heatPow_shift`, which gives the same exact mass for the
  translated-reflected kernel `y ↦ heatKernel t (x - y)` used by convolution.

The final formula retains the exact scale factor

```text
(((sqrt t)^n)^-1)^p * (sqrt t)^n * basePowMass(V,p).
```

This is the spatial input for the late-time Holder arm of the Koch--Lamm heat
map.  The focused Lean check passes with no warnings.  The source contains no
`sorry`, `admit`, axiom, opaque replacement, new class, instance, or notation.

## Honest frontier

The spatial real-power mass machinery in this file is 100%.  It does not yet
perform the terminal-time integration, local-cylinder restriction, or pair
the kernel with a `KLSource0`/`KLSource1` field.  Those are the next heat-map
producers.  Both exact endpoint theorems remain 0% until their existing Lean
declarations are proved and verified.
