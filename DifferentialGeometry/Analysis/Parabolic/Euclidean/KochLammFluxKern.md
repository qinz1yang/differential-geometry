# KochLammFluxKern

## Proved

- `klFluxMajor_memLp`: the radial first-derivative heat-kernel majorant lies
  in the exact terminal space-time dual class
  `L^((n+4)/(n+3))`.
- `klFluxKernel_ae`: on that slab, each directional kernel is almost
  everywhere bounded by `‖w‖` times the radial majorant.
- `klFluxKernel_memLp`: every directional first-derivative heat kernel lies
  in that same class, by the canonical pointwise radial majorant.
- `klFluxPowMass_eq`: the full terminal-slab power mass is evaluated exactly
  by Fubini and the real-power first-derivative heat-kernel scaling formula.

## Frontier

This is kernel-side machinery for the late `KLSource1` arm.  It does not by
itself prove either endpoint theorem.  The next producer extracts the
`R^(2/(n+4))` dual-root scale at time `R^2`; that scale must then cancel the
inverse scale in `KLSource1.late_lp` inside a local Hölder estimate.

Endpoint completion remains `0%` for both
`ricci_flow_unif_existence` and `ricci_flow_forward_unique`.
