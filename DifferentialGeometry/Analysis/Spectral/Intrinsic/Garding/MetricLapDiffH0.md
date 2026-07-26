# MetricLapDiffH0

## Role

This module is the consumer-facing order-zero packaging of the genuine moving
scalar Laplacian perturbation.  It postcomposes the verified
`H²(gT) → L²(gT)` map with the canonical isometric identification
`L²(gT) ≃ H⁰(gT)`.

## Current status

- `lapDiffA20` is the genuine `H²(gT) →L H⁰(gT)` perturbation.
- `lapDiffA20_core` retains the finite-support realization statement.
- `lapDiffA20_norm` proves exact preservation of the operator norm.
- `lapDiffA20_cont_of` transfers `ContinuousOn` from the fixed-`L²` family
  through the canonical isometric postcomposition without a whole-operator
  extensionality proof.
- `lapDiffA20_graph` identifies every applied value, near the frozen time,
  with the closure of the genuine smooth finite-core graph.
- `lapDiffA20_test` is the pointwise consumer of such a graph certificate.  It
  maps the graph continuously to one scalar test pairing and rewrites only the
  finite-core second coordinate as the fixed-`mu_q` geometric integral.  It
  requires no measurable choice of core approximants and performs no
  whole-operator equality.
- `lapDiffA20_bound` and `lapDiffA20_zero` transfer the support-independent
  vanishing modulus and operator-norm convergence.

The value-space adapter is complete.  The formerly separate interval
measurability frontier is now closed by `lapDiffA20_short` in
`MetricLapDiffMeas.lean`.

Focused verification of the graph and scalar mapped-closure API passes.

## Progress accounting

- `H²(gT) → H⁰(gT)` A2 packaging: 100%.
- A2 as a complete `nonaut_strong_exists` input: 100%.
- Full geometric nonautonomous input package: about 50% machinery; its final
  assembly theorem is not stated or proved (0%).
- Moving conjugate-heat theorem: 0%.
- Perelman no-local-collapsing theorem: 0%; dedicated machinery about 8%.
