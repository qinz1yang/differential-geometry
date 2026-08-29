# CutInjectivity

## Goal

Define the strict minimizing L-injectivity domain and prove its local and
fixed-time injectivity properties before establishing openness.

## Status

`lInjDomain`, `lInj_isOpen`, `lInj_local`, and `lInj_inj` pass focused
verification without warnings or placeholders.  Their axiom audits report only
`propext`, classical choice, and quotient soundness.

For openness, a hypothetical sequence outside the strict domain is moved into
the positive L-exponential domain at an intermediate time.  Compact direct
minimization supplies same-endpoint minimizing rays; the min--max initial-data
bound supplies a convergent subsequence.  Fixed-time closure preserves its
minimizing limit, strict pre-cut uniqueness identifies that limit, and local
L-exponential injectivity gives the contradiction.  The openness theorem needs
no positivity assumption on the displayed time: the witness ray supplies a
positive later time and the intermediate time is chosen above both it and zero.

## Next

`CutLocus` now uses this API to define the genuine cut domain, prove it closed
and Borel measurable at positive time, and split its image into conjugate and
multiple-minimizer parts.  Cut-image measurability and nullity remain separate
frontiers.

## Progress

- Strict minimizing-domain openness and fixed-time injectivity: 100%.
- Cut-image measure-zero theorem: 0%.
- `redVolume_anti`: 0%.
