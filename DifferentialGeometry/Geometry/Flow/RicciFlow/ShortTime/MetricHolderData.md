# MetricHolderData

## Producer

`metricDiff_c2half` converts the exact public input used by uniform
short-time existence—one family-wide `MetricCovDerivOrderBoundOn` constant
through order three—into low-order parabolic-Hölder initial data.

For every active POU chart and every scalar component of `g₀ - gBase`, it
chooses, before the family index:

- one bound for all Fréchet derivatives through order two;
- one global exponent-`1/2` Hölder constant for the second Fréchet derivative.

## Mathematical route

The proof reuses `metricDiff_comp_jet`, whose order-three estimate is global
on the POU-weighted Euclidean component.  Mathlib's identity
`norm_fderiv_iteratedFDeriv` and the mean-value theorem therefore make the
second derivative globally Lipschitz.  The same order-two jet bound gives an
exponent-zero Hölder bound.  `HolderWith.of_le_of_le` interpolates the global
exponent-zero and exponent-one estimates to the fixed exponent `1/2`.

The global conclusion is the exact input consumed by the whole-space
Gaussian cancellation operator in `HeatKernelCancel`; no carrier-extension
lemma is needed.

This direct route is shorter than passing through `W^{3,p}` and Morrey, though
the latter remains a valid backup.  No ellipticity, high Sobolev data, or
metric-dependent shrinking time is used.

## Verification state

The theorem is source-written only.  A parent-owned named build was active,
so this lane did not run Lean.  The first focused check should concentrate on
the `ENNReal`/`NNReal` coercions in the exponent-zero estimate and the exact
normal form returned by `HolderWith.of_le_of_le`; these are elaboration
concerns, not known mathematical gaps.

Honest status: this data producer is mathematically complete in source, Lean
verification 0%, and the exact `ricci_flow_unif_existence` theorem remains 0%.
