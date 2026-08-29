# CutCompact

## Status

`CutCompact.lean` is focused-check green and warning-free.  It contains no
placeholders.

## Public result

- `lMinVec_lim` proves fixed-positive-time stability of minimizing initial
  L-tangents.  If `Z n` tends to `Z₀`, every `(Z n, tau)` is in the minimizing
  domain, and `(Z₀, tau)` remains in the positive L-exponential domain, then
  `(Z₀, tau)` is also minimizing.

Keeping `tau` fixed is the weakest result needed by the cut-alternative
compactness argument: minimizing vectors at later times can first be restricted
to the common cut time by `lMinDomain_down`.

## Native proof route

Joint smoothness of `lExp` gives convergence of the terminal endpoints, while
`lRayAct_tendsto` gives convergence of the corresponding regularized ray
actions.  If the limiting ray failed to minimize against a global C1
competitor, `lCost_lt_event` would transfer that strict improvement to all
sufficiently late endpoints, contradicting the minimizing equalities of the
approximating rays.  `lRegCostC1_eq_on` converts the resulting global competitor
inequality back into equality with L-cost, hence membership in `lMinDomain`.

The moving tangent fibers are never compared.  All limiting quantities are
real-valued actions or costs.

## Remaining boundary step

This theorem supplies stability after a bounded sequence has a convergent
subsequence.  The separate min--max producer must still prove that the relevant
initial tangents are bounded, after which finite dimensionality supplies the
subsequence.  The final local-diffeomorphism contradiction assembling
`lCut_alt` remains to be stated and proved.

## Honest progress

- `lMinVec_lim`: 100%.
- Fixed-time minimizing-vector stability: 100%.
- Initial-tangent boundedness/compactness assembly: not completed in this file.
- `lCut_alt`: 0% until its public theorem is stated and proved.
- `redVolume_anti`: 0%.
