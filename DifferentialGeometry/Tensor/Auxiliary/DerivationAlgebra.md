# DerivationAlgebra

## 2026-05-14: Extracted contraction product-rule algebra

Worked:

- Added a geometry-free derivation algebra module for mixed tensor component
  contractions.
- Moved the reusable `contractUpper` finite-sum definition and product-rule
  lemmas out of `RicciIdentity.lean`.
- Generalized the extracted scalar algebra where the proof did not depend on
  `Real`.

Verification passed.

Remaining:

- Curvature-specific probe algebra still belongs in `RicciIdentity.lean` for
  now.
- The coordinate normalization frontier
  `constInChart_basisTensor0S_coordFrame` is unchanged.
