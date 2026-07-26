# RankZero

## Frontier

`scalar0_raw_eq` is the rank-zero scalar bridge needed by the conjugate-heat
eigen-series reconstruction.  It compares the raw chart component with
`TensorRSField.scalar0` only after full scalar evaluation; no equality of whole
Hom fibres is introduced.

## Verification

Focused verification passed without warnings.

## Accounting

- `scalar0_raw_eq`: theorem and focused verification 100%.
- Scalar joint reconstruction theorem: not yet stated or proved, 0%.
- Its dedicated machinery: approximately 85% after this bridge and the compact
  eigenfunction jet bound; chart-local product-mode summability and gluing remain.
- `heatpot_of_gallim` and Perelman noncollapsing endpoints: 0%; this file only
  supplies upstream scalar realization machinery.
