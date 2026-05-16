# TensorRS Model

## 2026-05-12: Mixed basis-slot Christoffel formula

- Added the mixed `(r,s)` model basis-slot expansion:
  `lieDeriv_correctionL_apply_basisTensor0S`,
  `covariantDeriv_tensorRSModelAt_apply_basis_slots`, and
  `covariantDeriv_tensorRSModelWithin_apply_basis_slots`.
- The upper-slot correction is positive in the Hom input and uses
  `connectionEndomorphismCoeff basis Î“X k (upper a)`; the lower-slot
  correction is negative and uses `connectionEndomorphismCoeff basis Î“X (lower b) k`.
- The key proof lesson was to compare the upper correction after applying the
  finite tensor basis representation, then explicitly reduce `Finsupp` finite
  sums at the chosen index. This avoids large downstream coordinate algebra.
- Cleaned flexible `simp at` warnings in the index-update zero cases.

## 2026-05-12: Basis-correction proof repair

- Repaired `lieDeriv_correctionL_apply_basisTensor0S`.
- The obstruction was not mathematical: after applying the coordinate tensor
  basis representation, the right side stayed as a `Finsupp` evaluation of a
  finite sum rather than the expanded scalar double sum expected by the old
  `change`.
- The proof now explicitly rewrites the `Finsupp` sum application and rewrites
  updated basis slots before applying `basis_coord_update_sum_comm`.
