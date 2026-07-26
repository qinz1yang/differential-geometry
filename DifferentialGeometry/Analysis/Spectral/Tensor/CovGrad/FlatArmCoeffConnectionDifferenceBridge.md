# Flat-arm coefficient / connection-difference bridge

## Durable facts

- `connDiffLoweredCc g₀ g₁` is the covariant rank-three lowering, by `g₀`, of
  `connDiffSection g₁ g₀`.
- `connLow_rfns` exports the equality of their pointwise squared fiber norms after
  every number of `g₀`-covariant derivatives.  The proof is exact: rotate the
  three covariant slots, raise the first slot with the parallel `g₀` cometric,
  then use the realization identity already proved in this file.
- This is the small public bridge needed to feed the canonical pointwise
  connection-difference jet grid into the low-regularity `H²` coefficient route.

## Verification state

The new public lemma is source-complete but has not yet been focused-checked.
The shared exported-artifact repair is currently exclusive, so no competing
Lean process was started.  The pre-existing flat-arm theorem remains unchanged.
