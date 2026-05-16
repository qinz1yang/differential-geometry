# NablaOnTensors Model Notes

## 2026-05-11 RS Christoffel coordinate frontier

Attempted:

- Tried to add `covariantDeriv_tensorRSModelAt_apply_basis_slots` and its
  within-set variant to `Model/Christoffel.lean`.
- The output/lower-slot term reduces to the existing `(0,s)` correction formula.
- The input/upper Hom term reduces to a basis identity for
  `lieDeriv_correctionL r Î“X` applied to a coordinate covariant tensor basis
  element.

Blocked:

- The finite delta proof for the upper correction became brittle:
  it must prove
  `lieDeriv_correctionL r Î“X (basis upper)
    = sum a k, Î“^upper[a]_k â€¢ basis (upper[a := k])`.
- Direct `Finset.sum_eq_single` proofs over `Function.update` goals were not
  stable enough to keep. The partial code was removed and
  `Model/Christoffel.lean` checks again.

Next useful lemma:

- Prove the upper-correction basis identity as a small standalone theorem,
  probably at the coordinate-basis layer, before restating the mixed
  `covariantDeriv_tensorRSModelAt_apply_basis_slots` theorem.

## 2026-05-11 mixed Hom-coordinate work

Successful:

- Moved the explicit Hom basis and `tensorRSModel_basis` coordinate layer to
  `DifferentialGeometry.Tensor.RSTensor.Basis`.
- Added `lieDeriv_correctionL_apply_slots`.
- Proved `covariantDeriv_tensorRSModelWithin_eval_derivation`, the pure model
  Hom-derivation formula needed for mixed regularity.

Failed / remaining:

- Nothing in `Model.lean` is currently blocked. The remaining mixed regularity
  problem is in the manifold/fixed-trivialization coefficient bridge in
  `Regularity.lean`.

## 2026-05-11 extraction cleanup

Completed:

- Split the model layer into:
  - `Model/Tensor0S.lean` for pure `(0,s)` model formulas and slot product
    rules;
  - `Model/TensorRS.lean` for pure mixed/Hom model derivation formulas;
  - `Model/Christoffel.lean` for Christoffel and basis model formulas;
  - `Model/Smoothness.lean` for model smoothness lemmas.
- Kept `Model.lean` as a compatibility wrapper importing those files.

Verified:

- Verification passed.
