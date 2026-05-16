# SlotAlgebra

## 2026-05-14: Extracted slot/update algebra

Worked:

- Added a geometry-free slot algebra module for finite-slot tensor
  calculations.
- Extracted reusable `Function.update`, `Fin.cons`, finite-sum splitting, and
  double-update cancellation lemmas from the Ricci identity proof.
- Kept the statements generic over additive monoids/groups where possible.

Verification passed.

Remaining:

- The next layer should package the derivation-style commutator algebra on top
  of these slot lemmas, rather than putting that algebra back into
  `RicciIdentity.lean`.
