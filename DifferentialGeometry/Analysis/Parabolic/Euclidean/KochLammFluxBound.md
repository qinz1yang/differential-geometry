# KochLammFluxBound

## Proved

This producer combines three already proved inputs:

- the almost-everywhere directional-kernel domination by the radial
  first-derivative majorant;
- the exact `R^(2/(n+4))` terminal-kernel scale;
- the inverse `KLSource1.late_lp` scale.

The focused-green endpoint theorem `klFluxNear_norm` is the
radius-independent bound
`‖near potential‖ ≤ ‖w‖ * klLate1C V * Aₚ`.

The intermediate theorems `klFluxKern_fac` and `klFluxSrc_fac` retain the
two radius factors explicitly before their exact cancellation.

## Endpoint state

This closes the near terminal-cylinder late-flux arm, not the full
Ricci-flow endpoint.  Both requested Ricci-flow endpoint theorems remain
`0%`; the far-shell/full-potential flux arm and fixed-point/gauge wiring are
still required.
