# ScalarPotential

## Status

The fixed smooth scalar-potential producer is complete. Focused verification
and the targeted module build both pass without local warnings, `sorry`, or
`admit`.

## Implemented route

- `ScalarH1Core` is the dense finite-support scalar spectral `H¹` core.
- `scalarPotSec` realizes multiplication by a smooth real coefficient through
  the existing `scalarSmul` section construction.
- `scalarPotCore` maps that genuine product into the fixed `TensorL2 0 0 q`
  space.
- `scalarPotOp` is the `LinearMap.extendOfNorm` extension to all of spectral
  `H¹(q)`. Compactness of `M` supplies an internal global coefficient bound,
  so `scalarPotOp_core` is unconditional and introduces no consumer
  assumption.
- `scalarPotH0` postcomposes with the canonical isometric `L²(q) ≃ H⁰(q)`
  identification.
- `scalarPotH0_test` extends the genuine finite-core pairing by density and
  proves the exact fixed-metric scalar multiplier identity for every H1 input.
  No measurable core approximant is selected.
- `scalarPotOp_norm`, `scalarPot_pair_norm`, and `scalarPotH0_pair` transfer
  pointwise coefficient or coefficient-difference bounds to operator-norm
  bounds. The pair proofs use applied dense-core estimates, not equality of
  whole continuous-linear-map objects.

## Proof lessons

The cheapest multiplier estimate is scalar-valued from the start: use left and
right homogeneity of `tensorInnerPointwise`, compare the diagonal integrands,
then integrate. This avoids unfolding rank-zero tensor or Hom representations.

The graph/test additions pass focused verification.  The first earlier check
failed because `scalarSmul`, `finiteReprLin`, and
`tensorHsSmoothRepr` live in the `TensorSpectral` namespace even when their
modules are imported. Opening that namespace resolved the cascade. A second
local mismatch was only the evaluation normal form of a smooth-map difference;
changing the already-applied scalar target to `ζ x - η x` closed it with
`sub_smul`. No heartbeat increase was needed.

## Honest progress

- This scalar-potential producer theorem/API: **100%**.
- Its dedicated finite-core, extension, testing, norm, pairwise, and `H⁰` machinery:
  **100%**.
- The final time-dependent `A1` short-interval assembly theorem is outside this
  file and is not counted as complete here.
- The eventual moving conjugate-heat and Perelman no-local-collapsing endpoints
  remain **0% as Lean theorems** until their final statements and proofs exist.
