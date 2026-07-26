# HmfRoughMap

## Status

Source-written fixed-point/stability interface; focused verification is
pending the shared named build.

## Exact specialization

This file targets the shortest forward-uniqueness route rather than a full
rough-metric Ricci--DeTurck solver.  For one smooth endpoint Ricci flow set
`q = g(0)` and solve the harmonic-map heat flow in local-addition coordinates
with unknown section `V` and `V(0)=0`.

`HmfCoeff eps K A Q` has the intended specialization:

- `A(t,x)` is the prescribed inverse-metric-difference coefficient
  `g(t)^{-1}-q^{-1}` in the divergence flux `A DV`;
- `eps` is its uniform operator bound, made small by `Icc`-`C⁰` convergence
  of `g(t)` to `q` on a short edge window;
- `Q(t,x)` packages the target/local-addition quadratic-gradient term and has
  a uniform bound `K`.

`HmfSplit` deliberately keeps the principal divergence flux and the
undifferentiated quadratic source in different weighted/Carleson classes.
`hmfDiffSplit` is the consumer-shaped stability estimate for two iterates.

## Critical contraction accounting

`hmfCrit` specializes the critical time convolution to

`integral_0^t eps*C*(t-s)^(-1/2)*s^(-1/2) ds <= 4*eps*C`.

There is no horizon gain.  The principal contraction smallness is exactly
`eps`; the local `L²` Carleson principal term carries `eps²`.  The quadratic
difference is small only after restricting to a small rough solution ball,
through the factors multiplying the difference-gradient norm.  This is the
faithful fixed-point design for local-addition HMF.

## Remaining producer

The next analytic theorem must map an `HmfSplit` pair through the chartwise
heat potentials back into the complete `InRoughPath` norm, including the
local Carleson estimates.  After that, compact finite-chart patching and the
geometric local-addition realization must identify the solution with the HMF
consumed by `hmf_inverse_DT`.

This file is machinery, not the endpoint: `ricci_flow_forward_unique` remains
0% until its exact theorem is proved and verified.
