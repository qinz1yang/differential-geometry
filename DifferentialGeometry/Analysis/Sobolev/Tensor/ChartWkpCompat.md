# ChartWkpCompat

## Status

Source-written only. Focused Lean verification is deferred to the currently
active named build lane.

## Exact compatibility result

The file proves the pointwise/a.e. identities needed to use the quantitative
coefficient from `ChartWkpBoundK.lean` without changing the geometric tensor
transition formula.

The two `chartKernelCutoff` factors are both eliminated explicitly:

1. the target cutoff is absorbed by the target POU factor using
   `pouCutoffMul`;
2. the source cutoff is one on the nonzero source representative branch,
   because `secCompRep_support` places the coordinate point in the image of
   the source POU support; chart injectivity identifies its support witness
   with the current manifold point;
3. if either the target POU weight or source representative is zero, both
   sides vanish directly.

This case split is packaged in `repCoeffEq`; no cutoff is silently discarded.
`secPullLimitEq` is now arbitrary-order in `k`; it gives the target component of one reconstructed weak
source pull, and `secCompDecomp` gives the finite active-atlas/component
decomposition of an arbitrary genuine section.

No smoothness is assigned to a weak limit, and no axiom, opaque producer,
`sorry`, or `admit` is introduced.

## Honest progress

- Exact double-cutoff compatibility: 100% source-written, 0% Lean-verified.
- Finite transport identity: 100% source-written, 0% Lean-verified.
- Exact `wkpTensor_limit`: assembled downstream, still 0% until verification.
- Exact `ricci_flow_unif_existence`: 0%.
