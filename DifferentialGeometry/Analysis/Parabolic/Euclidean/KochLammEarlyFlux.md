# KochLammEarlyFlux

## Purpose

This file closes the canonical-instantiation gap in the early value estimate
for a Koch--Lamm divergence source.

## Proved source content

- `fluxShell_cover` inserts the dimension-only finite cover supplied by
  `QuantCover.exists_shell_cover` at the observation-time heat scale.
- `kl1_early_norm` combines that cover, the summable shell mass
  `fluxShellSeries`, and `kl1_to_gradCarl`.  The square root of the Carleson
  radius `(A₂)^2` is simplified back to `A₂`, so the final bound is genuinely
  linear in the `KLSource1` local `L²` radius.

## Verification state

Source assembled without placeholders.  Focused verification is pending the
lock-aware exact exports of the already checked direct imports
`HeatEarlyFlux`, `HeatEarlyFluxSeries`, `QuantCover`, and `KochLammCarl`.

This proves only the early `Y¹ → L∞` arm of the Euclidean heat map.  The full
`KLSplit → KLPath` theorem and `ricci_flow_forward_unique` remain unproved, so
the endpoint remains 0%.
