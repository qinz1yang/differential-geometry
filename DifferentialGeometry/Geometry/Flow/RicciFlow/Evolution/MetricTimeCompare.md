# MetricTimeCompare

## Role

This lower evolution module owns the closed-slab metric comparison previously
available only as private implementation inside `HCGCompactness/MovingShiOpen`.
It is intended for evolution consumers such as `DistanceBarrier`; it has no HCG
dependency.

## Public API

- `metricPDE_Icc`: the Ricci-flow metric PDE on a closed slab, including the
  one-sided derivative at the left endpoint.
- `exp_bounds_log`: scalar exponential bounds from a logarithmic difference.
- `metricEquiv_Icc`: pointwise exponential comparison with the left-endpoint
  metric.
- `edistCont_Icc`: joint continuity, on a closed time slab, of the
  Riemannian extended distance from a fixed point as both time and the moving
  endpoint vary.
- `complete_of_ricBound`: completeness of every slice from completeness of the
  left endpoint and a uniform quadratic Ricci bound.

The completeness theorem treats the degenerate case `s = a` directly. Hence it
does not add a global strict inequality `a < b`; strictness is needed only on
the actual subslab when `a < s`.

The joint-continuity theorem first obtains a two-time exponential metric
sandwich by restricting `metricPDE_Icc` and `metricEquiv_Icc` to the interval
between the two times. `DistanceScaling` then gives matching extended-distance
bounds. Both bounds converge to the fixed-time continuous distance as the time
and endpoint vary. This avoids completeness, connectedness, and finite-distance
assumptions.

## Verification

Focused verification is green with zero diagnostics, including
`edistCont_Icc`. The module contains no `sorry`, `admit`, or `axiom`. An exact
artifact refresh has intentionally not been run while another target writer is
active.

## Project accounting

`complete_of_ricBound` and `edistCont_Icc` are supporting producers for the
evolving Calabi distance barrier and its cutoff layer. Both producer theorems
and their dedicated closed-slab metric comparison machinery are 100% at the
source/focused level.  Their exact artifact verification is now current. The evolving
barrier theorem remains separately accounted until its own verification. The
whole HCG supporting machinery remains about 60%, and unconditional
`compactnessSol` remains 0%.
