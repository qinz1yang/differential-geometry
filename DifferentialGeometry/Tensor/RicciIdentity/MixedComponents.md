# MixedComponents

## 2026-05-14: Extracted from RicciIdentity

Worked:

- Moved the `MixedComponentAlgebra` section out of
  `Tensor/RicciIdentity.lean` into this focused module.
- Preserved the existing namespace and theorem names, including
  `mixedRicciIdentityCoord_of_coordinate_second_product` and
  `coordDeriv_applyInput_eq_contractUpper`.
- Kept this file at the component/probe algebra layer.  It still consumes the
  pure `DerivationAlgebra` contraction rules and does not own the invariant
  `(0,s)` commutator proof.

Verification passed.

Remaining:

- The mixed coordinate producer is still blocked upstream by the existing
  coordinate/local-frame normalization frontier in
  `Coordinates/NablaComponents/TensorRS.lean`.
